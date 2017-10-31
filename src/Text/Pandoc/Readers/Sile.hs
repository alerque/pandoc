{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-
Copyright (C) 2006-2017 John MacFarlane <jgm@berkeley.edu>

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
-}

{- |
   Module      : Text.Pandoc.Readers.Sile
   Copyright   : Copyright (C) 2006-2017 Caleb Maclennan
   License     : GNU GPL, version 2 or above

   Maintainer  : Caleb Maclennan <caleb@alerque.com>
   Stability   : alpha
   Portability : portable

Conversion of Sile to 'Pandoc' document.

-}
module Text.Pandoc.Readers.Sile ( readSile,
                                   rawSileInline,
                                   rawSileBlock,
                                   inlineCommand,
                                 ) where

import Control.Applicative (many, optional, (<|>))
import Control.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Trans (lift)
import Data.Char (chr, isAlphaNum, isLetter, ord, isDigit, toLower)
import Data.Default
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.Maybe (fromMaybe, maybeToList)
import Safe (minimumDef)
import System.FilePath (addExtension, replaceExtension, takeExtension)
import Text.Pandoc.Builder
import Text.Pandoc.Class (PandocMonad, PandocPure, lookupEnv,
                          readFileFromDirs, report, setResourcePath,
                          getResourcePath, setTranslations, translateTerm)
import qualified Text.Pandoc.Translations as Translations
import Text.Pandoc.ImageSize (numUnit, showFl)
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.Pandoc.Parsing hiding (many, optional, withRaw,
                            space, (<|>), spaces, blankline)
import Text.Pandoc.Shared
import Text.Pandoc.Readers.Sile.Types (ExpansionPoint(..), Tok(..),
                            TokType(..))
import Text.Pandoc.Walk
import Text.Pandoc.Error
   (PandocError(PandocParsecError, PandocParseError))
import Text.Parsec.Pos

-- for debugging:
-- import Text.Pandoc.Extensions (getDefaultExtensions)
-- import Text.Pandoc.Class (runIOorExplode, PandocIO)
-- import Debug.Trace (traceShowId)

-- | Parse Sile from string and return 'Pandoc' document.
readSile :: PandocMonad m
          => ReaderOptions -- ^ Reader options
          -> Text        -- ^ String to parse (assumes @'\n'@ line endings)
          -> m Pandoc
readSile opts ltx = do
  parsed <- runParserT parseSile def{ sOptions = opts } "source"
               (tokenize "source" (crFilter ltx))
  case parsed of
    Right result -> return result
    Left e       -> throwError $ PandocParsecError (T.unpack ltx) e

parseSile :: PandocMonad m => SP m Pandoc
parseSile = do
  bs <- blocks
  eof
  st <- getState
  let meta = sMeta st
  let doc' = doc bs
  let headerLevel (Header n _ _) = [n]
      headerLevel _ = []
  let bottomLevel = minimumDef 1 $ query headerLevel doc'
  let adjustHeaders m (Header n attr ils) = Header (n+m) attr ils
      adjustHeaders _ x = x
  let (Pandoc _ bs') =
       -- handle the case where you have \part or \chapter
       (if bottomLevel < 1
           then walk (adjustHeaders (1 - bottomLevel))
           else id) $
       walk (resolveRefs (sLabels st)) $ doc'
  return $ Pandoc meta bs'

resolveRefs :: M.Map String [Inline] -> Inline -> Inline
resolveRefs labels x@(Link (ident,classes,kvs) _ _) =
  case (lookup "reference-type" kvs,
        lookup "reference" kvs) of
        (Just "ref", Just lab) ->
          case M.lookup lab labels of
               Just txt -> Link (ident,classes,kvs) txt ('#':lab, "")
               Nothing  -> x
        _ -> x
resolveRefs _ x = x


-- testParser :: SP PandocIO a -> Text -> IO a
-- testParser p t = do
--   res <- runIOorExplode (runParserT p defaultSileState{
--             sOptions = def{ readerExtensions =
--               enableExtension Ext_raw_tex $
--                 getDefaultExtensions "latex" }} "source" (tokenize "source" t))
--   case res of
--        Left e  -> error (show e)
--        Right r -> return r

data SileState = SileState{   sOptions       :: ReaderOptions
                            , sMeta          :: Meta
                            , sQuoteContext  :: QuoteContext
                            , sContainers    :: [String]
                            , sHeaders       :: M.Map Inlines String
                            , sLogMessages   :: [LogMessage]
                            , sIdentifiers   :: Set.Set String
                            , sCaption       :: Maybe Inlines
                            , sLastHeaderNum :: HeaderNum
                            , sLabels        :: M.Map String [Inline]
                            , sToggles       :: M.Map String Bool
                            }
     deriving Show

defaultSileState :: SileState
defaultSileState = SileState{   sOptions       = def
                              , sMeta          = nullMeta
                              , sQuoteContext  = NoQuote
                              , sContainers    = []
                              , sHeaders       = M.empty
                              , sLogMessages   = []
                              , sIdentifiers   = Set.empty
                              , sCaption       = Nothing
                              , sLastHeaderNum = HeaderNum []
                              , sLabels        = M.empty
                              , sToggles       = M.empty
                              }

instance PandocMonad m => HasQuoteContext SileState m where
  getQuoteContext = sQuoteContext <$> getState
  withQuoteContext context parser = do
    oldState <- getState
    let oldQuoteContext = sQuoteContext oldState
    setState oldState { sQuoteContext = context }
    result <- parser
    newState <- getState
    setState newState { sQuoteContext = oldQuoteContext }
    return result

instance HasLogMessages SileState where
  addLogMessage msg st = st{ sLogMessages = msg : sLogMessages st }
  getLogMessages st = reverse $ sLogMessages st

instance HasIdentifierList SileState where
  extractIdentifierList     = sIdentifiers
  updateIdentifierList f st = st{ sIdentifiers = f $ sIdentifiers st }

instance HasIncludeFiles SileState where
  getIncludeFiles = sContainers
  addIncludeFile f s = s{ sContainers = f : sContainers s }
  dropLatestIncludeFile s = s { sContainers = drop 1 $ sContainers s }

instance HasHeaderMap SileState where
  extractHeaderMap     = sHeaders
  updateHeaderMap f st = st{ sHeaders = f $ sHeaders st }

instance HasReaderOptions SileState where
  extractReaderOptions = sOptions

instance HasMeta SileState where
  setMeta field val st =
    st{ sMeta = setMeta field val $ sMeta st }
  deleteMeta field st =
    st{ sMeta = deleteMeta field $ sMeta st }

instance Default SileState where
  def = defaultSileState

type SP m = ParserT [Tok] SileState m

rawSileParser :: (PandocMonad m, HasReaderOptions s)
               => SP m a -> ParserT String s m String
rawSileParser parser = do
  inp <- getInput
  let toks = tokenize "source" $ T.pack inp
  pstate <- getState
  let lstate = def{ sOptions = extractReaderOptions pstate }
  res <- lift $ runParserT ((,) <$> try (snd <$> withRaw parser) <*> getState)
            lstate "source" toks
  case res of
       Left _    -> mzero
       Right (raw, st) -> do
         takeP (T.length (untokenize raw))

rawSileBlock :: (PandocMonad m, HasReaderOptions s)
              => ParserT String s m String
rawSileBlock = do
  lookAhead (try (char '\\' >> letter))
  rawSileParser (environment <|> blockCommand)

rawSileInline :: (PandocMonad m, HasReaderOptions s)
               => ParserT String s m String
rawSileInline = do
  lookAhead (try (char '\\' >> letter) <|> char '$')
  rawSileParser (inlineEnvironment <|> inlineCommand')

inlineCommand :: PandocMonad m => ParserT String ParserState m Inlines
inlineCommand = do
  lookAhead (try (char '\\' >> letter) <|> char '$')
  inp <- getInput
  let toks = tokenize "chunk" $ T.pack inp
  let rawinline = do
         (il, raw) <- try $ withRaw (inlineEnvironment <|> inlineCommand')
         st <- getState
         return (il, raw, st)
  pstate <- getState
  let lstate = def{ sOptions = extractReaderOptions pstate
                  }
  res <- runParserT rawinline lstate "source" toks
  case res of
       Left _ -> mzero
       Right (il, raw, s) -> do
         takeP (T.length (untokenize raw))
         return il

tokenize :: SourceName -> Text -> [Tok]
tokenize sourcename = totoks (initialPos sourcename)

totoks :: SourcePos -> Text -> [Tok]
totoks pos t =
  case T.uncons t of
       Nothing        -> []
       Just (c, rest)
         | c == '\n' ->
           Tok pos Newline "\n"
           : totoks (setSourceColumn (incSourceLine pos 1) 1) rest
         | isSpaceOrTab c ->
           let (sps, rest') = T.span isSpaceOrTab t
           in  Tok pos Spaces sps
               : totoks (incSourceColumn pos (T.length sps))
                 rest'
         | isAlphaNum c ->
           let (ws, rest') = T.span isAlphaNum t
           in  Tok pos Word ws
               : totoks (incSourceColumn pos (T.length ws)) rest'
         | c == '%' ->
           let (cs, rest') = T.break (== '\n') rest
           in  Tok pos Comment ("%" <> cs)
               : totoks (incSourceColumn pos (1 + T.length cs)) rest'
         | c == '\\' ->
           case T.uncons rest of
                Nothing -> [Tok pos Symbol (T.singleton c)]
                Just (d, rest')
                  | isLetterOrAt d ->
                      -- \makeatletter is common in macro defs;
                      -- ideally we should make tokenization sensitive
                      -- to \makeatletter and \makeatother, but this is
                      -- probably best for now
                      let (ws, rest'') = T.span isLetterOrAt rest
                          (ss, rest''') = T.span isSpaceOrTab rest''
                      in  Tok pos (CtrlSeq ws) ("\\" <> ws <> ss)
                          : totoks (incSourceColumn pos
                               (1 + T.length ws + T.length ss)) rest'''
                  | d == '\t' || d == '\n' ->
                      Tok pos Symbol ("\\")
                      : totoks (incSourceColumn pos 1) rest
                  | otherwise  ->
                      Tok pos (CtrlSeq (T.singleton d)) (T.pack [c,d])
                      : totoks (incSourceColumn pos 2) rest'
         | c == '#' ->
           let (t1, t2) = T.span (\d -> d >= '0' && d <= '9') rest
           in  case safeRead (T.unpack t1) of
                    Just i ->
                       Tok pos (Arg i) ("#" <> t1)
                       : totoks (incSourceColumn pos (1 + T.length t1)) t2
                    Nothing ->
                       Tok pos Symbol ("#")
                       : totoks (incSourceColumn pos 1) t2
         | c == '^' ->
           case T.uncons rest of
                Just ('^', rest') ->
                  case T.uncons rest' of
                       Just (d, rest'')
                         | isLowerHex d ->
                           case T.uncons rest'' of
                                Just (e, rest''') | isLowerHex e ->
                                  Tok pos Esc2 (T.pack ['^','^',d,e])
                                  : totoks (incSourceColumn pos 4) rest'''
                                _ ->
                                  Tok pos Esc1 (T.pack ['^','^',d])
                                  : totoks (incSourceColumn pos 3) rest''
                         | d < '\128' ->
                                  Tok pos Esc1 (T.pack ['^','^',d])
                                  : totoks (incSourceColumn pos 3) rest''
                       _ -> [Tok pos Symbol ("^"),
                             Tok (incSourceColumn pos 1) Symbol ("^")]
                _ -> Tok pos Symbol ("^")
                     : totoks (incSourceColumn pos 1) rest
         | otherwise ->
           Tok pos Symbol (T.singleton c) : totoks (incSourceColumn pos 1) rest

isSpaceOrTab :: Char -> Bool
isSpaceOrTab ' '  = True
isSpaceOrTab '\t' = True
isSpaceOrTab _    = False

isLetterOrAt :: Char -> Bool
isLetterOrAt '@'  = True
isLetterOrAt c    = isLetter c

isLowerHex :: Char -> Bool
isLowerHex x = x >= '0' && x <= '9' || x >= 'a' && x <= 'f'

untokenize :: [Tok] -> Text
untokenize = mconcat . map untoken

untoken :: Tok -> Text
untoken (Tok _ _ t) = t

satisfyTok :: PandocMonad m => (Tok -> Bool) -> SP m Tok
satisfyTok f =
  try $ do
    res <- tokenPrim (T.unpack . untoken) updatePos matcher
    return res
  where matcher t | f t       = Just t
                  | otherwise = Nothing
        updatePos :: SourcePos -> Tok -> [Tok] -> SourcePos
        updatePos _spos _ (Tok pos _ _ : _) = pos
        updatePos spos _ [] = spos

setpos :: SourcePos -> Tok -> Tok
setpos spos (Tok _ tt txt) = Tok spos tt txt

anyControlSeq :: PandocMonad m => SP m Tok
anyControlSeq = satisfyTok isCtrlSeq
  where isCtrlSeq (Tok _ (CtrlSeq _) _) = True
        isCtrlSeq _                     = False

anySymbol :: PandocMonad m => SP m Tok
anySymbol = satisfyTok isSym
  where isSym (Tok _ Symbol _) = True
        isSym _                = False

spaces :: PandocMonad m => SP m ()
spaces = skipMany (satisfyTok (tokTypeIn [Comment, Spaces, Newline]))

spaces1 :: PandocMonad m => SP m ()
spaces1 = skipMany1 (satisfyTok (tokTypeIn [Comment, Spaces, Newline]))

tokTypeIn :: [TokType] -> Tok -> Bool
tokTypeIn toktypes (Tok _ tt _) = tt `elem` toktypes

controlSeq :: PandocMonad m => Text -> SP m Tok
controlSeq name = satisfyTok isNamed
  where isNamed (Tok _ (CtrlSeq n) _) = n == name
        isNamed _ = False

symbol :: PandocMonad m => Char -> SP m Tok
symbol c = satisfyTok isc
  where isc (Tok _ Symbol d) = case T.uncons d of
                                    Just (c',_) -> c == c'
                                    _ -> False
        isc _ = False

symbolIn :: PandocMonad m => [Char] -> SP m Tok
symbolIn cs = satisfyTok isInCs
  where isInCs (Tok _ Symbol d) = case T.uncons d of
                                       Just (c,_) -> c `elem` cs
                                       _ -> False
        isInCs _ = False

sp :: PandocMonad m => SP m ()
sp = whitespace <|> endline

whitespace :: PandocMonad m => SP m ()
whitespace = () <$ satisfyTok isSpaceTok
  where isSpaceTok (Tok _ Spaces _) = True
        isSpaceTok _ = False

newlineTok :: PandocMonad m => SP m ()
newlineTok = () <$ satisfyTok isNewlineTok

isNewlineTok :: Tok -> Bool
isNewlineTok (Tok _ Newline _) = True
isNewlineTok _ = False

comment :: PandocMonad m => SP m ()
comment = () <$ satisfyTok isCommentTok
  where isCommentTok (Tok _ Comment _) = True
        isCommentTok _ = False

anyTok :: PandocMonad m => SP m Tok
anyTok = satisfyTok (const True)

endline :: PandocMonad m => SP m ()
endline = try $ do
  newlineTok
  lookAhead anyTok
  notFollowedBy blankline

blankline :: PandocMonad m => SP m ()
blankline = try $ skipMany whitespace *> newlineTok

primEscape :: PandocMonad m => SP m Char
primEscape = do
  Tok _ toktype t <- satisfyTok (tokTypeIn [Esc1, Esc2])
  case toktype of
       Esc1 -> case T.uncons (T.drop 2 t) of
                    Just (c, _)
                      | c >= '\64' && c <= '\127' -> return (chr (ord c - 64))
                      | otherwise                 -> return (chr (ord c + 64))
                    Nothing -> fail "Empty content of Esc1"
       Esc2 -> case safeRead ('0':'x':T.unpack (T.drop 2 t)) of
                    Just x -> return (chr x)
                    Nothing -> fail $ "Could not read: " ++ T.unpack t
       _    -> fail "Expected an Esc1 or Esc2 token" -- should not happen

bgroup :: PandocMonad m => SP m Tok
bgroup = try $ do
  skipMany sp
  symbol '{' <|> controlSeq "bgroup" <|> controlSeq "begingroup"

egroup :: PandocMonad m => SP m Tok
egroup = (symbol '}' <|> controlSeq "egroup" <|> controlSeq "endgroup")

grouped :: (PandocMonad m,  Monoid a) => SP m a -> SP m a
grouped parser = try $ do
  bgroup
  -- first we check for an inner 'grouped', because
  -- {{a,b}} should be parsed the same as {a,b}
  try (grouped parser <* egroup) <|> (mconcat <$> manyTill parser egroup)

braced :: PandocMonad m => SP m [Tok]
braced = bgroup *> braced' 1
  where braced' (n :: Int) =
          handleEgroup n <|> handleBgroup n <|> handleOther n
        handleEgroup n = do
          t <- egroup
          if n == 1
             then return []
             else (t:) <$> braced' (n - 1)
        handleBgroup n = do
          t <- bgroup
          (t:) <$> braced' (n + 1)
        handleOther n = do
          t <- anyTok
          (t:) <$> braced' n

bracketed :: PandocMonad m => Monoid a => SP m a -> SP m a
bracketed parser = try $ do
  symbol '['
  mconcat <$> manyTill parser (symbol ']')

dimenarg :: PandocMonad m => SP m Text
dimenarg = try $ do
  ch  <- option False $ True <$ symbol '='
  Tok _ _ s <- satisfyTok isWordTok
  guard $ (T.take 2 (T.reverse s)) `elem`
           ["pt","pc","in","bp","cm","mm","dd","cc","sp"]
  let num = T.take (T.length s - 2) s
  guard $ T.length num > 0
  guard $ T.all isDigit num
  return $ T.pack ['=' | ch] <> s

-- inline elements:

word :: PandocMonad m => SP m Inlines
word = (str . T.unpack . untoken) <$> satisfyTok isWordTok

regularSymbol :: PandocMonad m => SP m Inlines
regularSymbol = (str . T.unpack . untoken) <$> satisfyTok isRegularSymbol
  where isRegularSymbol (Tok _ Symbol t) = not $ T.any isSpecial t
        isRegularSymbol _ = False
        isSpecial c = c `Set.member` specialChars

specialChars :: Set.Set Char
specialChars = Set.fromList "#$%&~_^\\{}"

isWordTok :: Tok -> Bool
isWordTok (Tok _ Word _) = True
isWordTok _ = False

inlineGroup :: PandocMonad m => SP m Inlines
inlineGroup = do
  ils <- grouped inline
  if isNull ils
     then return mempty
     else return $ spanWith nullAttr ils
          -- we need the span so we can detitlecase bibtex entries;
          -- we need to know when something is {C}apitalized

doLHSverb :: PandocMonad m => SP m Inlines
doLHSverb =
  (codeWith ("",["haskell"],[]) . T.unpack . untokenize)
    <$> manyTill (satisfyTok (not . isNewlineTok)) (symbol '|')

mkImage :: PandocMonad m => [(String, String)] -> String -> SP m Inlines
mkImage options src = do
   let replaceTextwidth (k,v) =
         case numUnit v of
              Just (num, "\\textwidth") -> (k, showFl (num * 100) ++ "%")
              _ -> (k, v)
   let kvs = map replaceTextwidth
             $ filter (\(k,_) -> k `elem` ["width", "height"]) options
   let attr = ("",[], kvs)
   let alt = str "image"
   case takeExtension src of
        "" -> do
              defaultExt <- getOption readerDefaultImageExtension
              return $ imageWith attr (addExtension src defaultExt) "" alt
        _  -> return $ imageWith attr src "" alt

doxspace :: PandocMonad m => SP m Inlines
doxspace = do
  (space <$ lookAhead (satisfyTok startsWithLetter)) <|> return mempty
  where startsWithLetter (Tok _ Word t) =
          case T.uncons t of
               Just (c, _) | isLetter c -> True
               _ -> False
        startsWithLetter _ = False


lit :: String -> SP m Inlines
lit = pure . str

removeDoubleQuotes :: Text -> Text
removeDoubleQuotes t =
  maybe t id $ T.stripPrefix "\"" t >>= T.stripSuffix "\""

doubleQuote :: PandocMonad m => SP m Inlines
doubleQuote = do
       quoted' doubleQuoted (try $ count 2 $ symbol '`')
                            (void $ try $ count 2 $ symbol '\'')
   <|> quoted' doubleQuoted ((:[]) <$> symbol '“') (void $ symbol '”')
   -- the following is used by babel for localized quotes:
   <|> quoted' doubleQuoted (try $ sequence [symbol '"', symbol '`'])
                            (void $ try $ sequence [symbol '"', symbol '\''])

singleQuote :: PandocMonad m => SP m Inlines
singleQuote = do
       quoted' singleQuoted ((:[]) <$> symbol '`')
                            (try $ symbol '\'' >>
                                  notFollowedBy (satisfyTok startsWithLetter))
   <|> quoted' singleQuoted ((:[]) <$> symbol '‘')
                            (try $ symbol '’' >>
                                  notFollowedBy (satisfyTok startsWithLetter))
  where startsWithLetter (Tok _ Word t) =
          case T.uncons t of
               Just (c, _) | isLetter c -> True
               _ -> False
        startsWithLetter _ = False

quoted' :: PandocMonad m
        => (Inlines -> Inlines)
        -> SP m [Tok]
        -> SP m ()
        -> SP m Inlines
quoted' f starter ender = do
  startchs <- (T.unpack . untokenize) <$> starter
  smart <- extensionEnabled Ext_smart <$> getOption readerExtensions
  if smart
     then do
       ils <- many (notFollowedBy ender >> inline)
       (ender >> return (f (mconcat ils))) <|>
            (<> mconcat ils) <$>
                    lit (case startchs of
                              "``" -> "“"
                              "`"  -> "‘"
                              cs   -> cs)
     else lit startchs

enquote :: PandocMonad m => SP m Inlines
enquote = do
  skipopts
  quoteContext <- sQuoteContext <$> getState
  if quoteContext == InDoubleQuote
     then singleQuoted <$> withQuoteContext InSingleQuote tok
     else doubleQuoted <$> withQuoteContext InDoubleQuote tok

dolstinline :: PandocMonad m => SP m Inlines
dolstinline = do
  options <- option [] keyvals
  let classes = maybeToList $ lookup "language" options >>= fromListingsLanguage
  Tok _ Symbol t <- anySymbol
  marker <- case T.uncons t of
              Just (c, ts) | T.null ts -> return c
              _ -> mzero
  let stopchar = if marker == '{' then '}' else marker
  withVerbatimMode $
    (codeWith ("",classes,[]) . T.unpack . untokenize) <$>
      manyTill (verbTok stopchar) (symbol stopchar)

keyval :: PandocMonad m => SP m (String, String)
keyval = try $ do
  Tok _ Word key <- satisfyTok isWordTok
  let isSpecSym (Tok _ Symbol t) = t /= "]" && t /= ","
      isSpecSym _ = False
  optional sp
  val <- option [] $ do
           symbol '='
           optional sp
           braced <|> (many1 (satisfyTok isWordTok <|> satisfyTok isSpecSym
                               <|> anyControlSeq))
  optional sp
  optional (symbol ',')
  optional sp
  return (T.unpack key, T.unpack . untokenize $ val)

keyvals :: PandocMonad m => SP m [(String, String)]
keyvals = try $ symbol '[' >> manyTill keyval (symbol ']')

toksToString :: [Tok] -> String
toksToString = T.unpack . untokenize

-- citations

addPrefix :: [Inline] -> [Citation] -> [Citation]
addPrefix p (k:ks) = k {citationPrefix = p ++ citationPrefix k} : ks
addPrefix _ _      = []

addSuffix :: [Inline] -> [Citation] -> [Citation]
addSuffix s ks@(_:_) =
  let k = last ks
  in  init ks ++ [k {citationSuffix = citationSuffix k ++ s}]
addSuffix _ _ = []

simpleCiteArgs :: PandocMonad m => SP m [Citation]
simpleCiteArgs = try $ do
  first  <- optionMaybe $ toList <$> opt
  second <- optionMaybe $ toList <$> opt
  keys <- try $ bgroup *> (manyTill citationLabel egroup)
  let (pre, suf) = case (first  , second ) of
        (Just s , Nothing) -> (mempty, s )
        (Just s , Just t ) -> (s , t )
        _                  -> (mempty, mempty)
      conv k = Citation { citationId      = k
                        , citationPrefix  = []
                        , citationSuffix  = []
                        , citationMode    = NormalCitation
                        , citationHash    = 0
                        , citationNoteNum = 0
                        }
  return $ addPrefix pre $ addSuffix suf $ map conv keys

citationLabel :: PandocMonad m => SP m String
citationLabel  = do
  optional sp
  toksToString <$>
    (many1 (satisfyTok isWordTok <|> symbolIn bibtexKeyChar)
          <* optional sp
          <* optional (symbol ',')
          <* optional sp)
  where bibtexKeyChar = ".:;?!`'()/*@_+=-[]" :: [Char]

cites :: PandocMonad m => CitationMode -> Bool -> SP m [Citation]
cites mode multi = try $ do
  cits <- if multi
             then many1 simpleCiteArgs
             else count 1 simpleCiteArgs
  let cs = concat cits
  return $ case mode of
        AuthorInText -> case cs of
                             (c:rest) -> c {citationMode = mode} : rest
                             []       -> []
        _            -> map (\a -> a {citationMode = mode}) cs

citation :: PandocMonad m => String -> CitationMode -> Bool -> SP m Inlines
citation name mode multi = do
  (c,raw) <- withRaw $ cites mode multi
  return $ cite c (rawInline "sile" $ "\\" ++ name ++ (toksToString raw))


inlineCommand' :: PandocMonad m => SP m Inlines
inlineCommand' = try $ do
  Tok _ (CtrlSeq name) cmd <- anyControlSeq
  guard $ name /= "begin" && name /= "end"
  star <- option "" ("*" <$ symbol '*' <* optional sp)
  let name' = name <> star
  let names = ordNub [name', name] -- check non-starred as fallback
  let raw = do
       guard $ isInlineCommand name || not (isBlockCommand name)
       rawcommand <- getRawCommand name (cmd <> star)
       (guardEnabled Ext_raw_tex >> return (rawInline "sile" rawcommand))
         <|> ignore rawcommand
  lookupListDefault raw names inlineCommands

tok :: PandocMonad m => SP m Inlines
tok = grouped inline <|> inlineCommand' <|> singleChar'
  where singleChar' = do
          Tok _ _ t <- singleChar
          return (str (T.unpack t))

singleChar :: PandocMonad m => SP m Tok
singleChar = try $ do
  Tok pos toktype t <- satisfyTok (tokTypeIn [Word, Symbol])
  guard $ not $ toktype == Symbol &&
                T.any (`Set.member` specialChars) t
  if T.length t > 1
     then do
       let (t1, t2) = (T.take 1 t, T.drop 1 t)
       inp <- getInput
       setInput $ (Tok (incSourceColumn pos 1) toktype t2) : inp
       return $ Tok pos toktype t1
     else return $ Tok pos toktype t

opt :: PandocMonad m => SP m Inlines
opt = bracketed inline

rawopt :: PandocMonad m => SP m Text
rawopt = do
  inner <- untokenize <$> bracketedToks
  optional sp
  return $ "[" <> inner <> "]"

skipopts :: PandocMonad m => SP m ()
skipopts = skipMany rawopt

ignore :: (Monoid a, PandocMonad m) => String -> ParserT s u m a
ignore raw = do
  pos <- getPosition
  report $ SkippedContent raw pos
  return mempty

withRaw :: PandocMonad m => SP m a -> SP m (a, [Tok])
withRaw parser = do
  inp <- getInput
  result <- parser
  nxt <- option (Tok (initialPos "source") Word "") (lookAhead anyTok)
  let raw = takeWhile (/= nxt) inp
  return (result, raw)

inBrackets :: Inlines -> Inlines
inBrackets x = str "[" <> x <> str "]"

unescapeURL :: String -> String
unescapeURL ('\\':x:xs) | isEscapable x = x:unescapeURL xs
  where isEscapable c = c `elem` ("#$%&~_^\\{}" :: String)
unescapeURL (x:xs) = x:unescapeURL xs
unescapeURL [] = ""

inlineEnvironment :: PandocMonad m => SP m Inlines
inlineEnvironment = try $ do
  controlSeq "begin"
  name <- untokenize <$> braced
  M.findWithDefault mzero name inlineEnvironments

inlineEnvironments :: PandocMonad m => M.Map Text (SP m Inlines)
inlineEnvironments = M.fromList [
  ]

inlineCommands :: PandocMonad m => M.Map Text (SP m Inlines)
inlineCommands = M.union inlineLanguageCommands $ M.fromList $
  [ ("em", extractSpaces emph <$> tok)
  , ("strike", extractSpaces strikeout <$> tok)
  , ("textsuperscript", extractSpaces superscript <$> tok)
  , ("textsubscript", extractSpaces subscript <$> tok)
  , ("strong", extractSpaces strong <$> tok)
  , ("textnormal", extractSpaces (spanWith ("",["nodecor"],[])) <$> tok)
  , ("noindent", unlessParseRaw >> return mempty)
  , ("%", lit "%")
  , ("{", lit "{")
  , ("}", lit "}")
  , ("break", linebreak <$ (optional (bracketed inline) *> spaces'))
  , ("footnote", (note . mconcat) <$> (char '{' *> manyTill block (char '}')))
  , ("texttt", (code . stringify . toList) <$> tok)
  , ("url", (unescapeURL <$> braced) >>= \url ->
       pure (link url "" (str url)))
  , ("href", (unescapeURL . toksToString <$>
                 braced <* optional sp) >>= \url ->
                   tok >>= \lab -> pure (link url "" lab))
  ]

hyperlink :: PandocMonad m => SP m Inlines
hyperlink = try $ do
  src <- toksToString <$> braced
  lab <- tok
  return $ link ('#':src) "" lab

hypertargetBlock :: PandocMonad m => SP m Blocks
hypertargetBlock = try $ do
  ref <- toksToString <$> braced
  bs <- grouped block
  case toList bs of
       [Header 1 (ident,_,_) _] | ident == ref -> return bs
       _ -> return $ divWith (ref, [], []) bs

hypertargetInline :: PandocMonad m => SP m Inlines
hypertargetInline = try $ do
  ref <- toksToString <$> braced
  ils <- grouped inline
  return $ spanWith (ref, [], []) ils


rawInlineOr :: PandocMonad m => Text -> SP m Inlines -> SP m Inlines
rawInlineOr name' fallback = do
  parseRaw <- extensionEnabled Ext_raw_tex <$> getOption readerExtensions
  if parseRaw
     then rawInline "latex" <$> getRawCommand name' ("\\" <> name')
     else fallback

getRawCommand :: PandocMonad m => Text -> Text -> SP m String
getRawCommand name txt = do
  (_, rawargs) <- withRaw $
      case name of
           "write" -> do
             void $ satisfyTok isWordTok -- digits
             void braced
           "titleformat" -> do
             void braced
             skipopts
             void $ count 4 braced
           "def" -> do
             void $ manyTill anyTok braced
           _ -> do
             skipopts
             option "" (try (optional sp *> dimenarg))
             void $ many braced
  return $ T.unpack (txt <> untokenize rawargs)

isBlockCommand :: Text -> Bool
isBlockCommand s =
  s `M.member` (blockCommands :: M.Map Text (SP PandocPure Blocks))
  || s `Set.member` treatAsBlock

treatAsBlock :: Set.Set Text
treatAsBlock = Set.fromList
   , "framebreak"
   , "pagebreak"
   ]

isInlineCommand :: Text -> Bool
isInlineCommand s =
  s `M.member` (inlineCommands :: M.Map Text (SP PandocPure Inlines))
  || s `Set.member` treatAsInline

treatAsInline :: Set.Set Text
treatAsInline = Set.fromList
  [ "hbox"
  , "glue"
  , "skip"
  , "noindent"
  , "framebreak"
  , "pagebreak"
  ]

lookupListDefault :: (Show k, Ord k) => v -> [k] -> M.Map k v -> v
lookupListDefault d = (fromMaybe d .) . lookupList
  where lookupList l m = msum $ map (`M.lookup` m) l

inline :: PandocMonad m => SP m Inlines
inline = (mempty <$ comment)
     <|> (softbreak <$ endline)
     <|> word
     <|> inlineCommand'
     <|> inlineEnvironment
     <|> inlineGroup
     <|> (symbol '-' *>
           option (str "-") (symbol '-' *>
             option (str "–") (str "—" <$ symbol '-')))
     <|> doubleQuote
     <|> singleQuote
     <|> (str "”" <$ try (symbol '\'' >> symbol '\''))
     <|> (str "”" <$ symbol '”')
     <|> (str "’" <$ symbol '\'')
     <|> (str "’" <$ symbol '’')
     <|> (str "\160" <$ symbol '~')
     <|> dollarsMath
     <|> (guardEnabled Ext_literate_haskell *> symbol '|' *> doLHSverb)
     <|> (str . (:[]) <$> primEscape)
     <|> regularSymbol
     <|> (do res <- symbolIn "#^'`\"[]"
             pos <- getPosition
             let s = T.unpack (untoken res)
             report $ ParsingUnescaped s pos
             return $ str s)

inlines :: PandocMonad m => SP m Inlines
inlines = mconcat <$> many inline

-- block elements:

begin_ :: PandocMonad m => Text -> SP m ()
begin_ t = (try $ do
  controlSeq "begin"
  spaces
  txt <- untokenize <$> braced
  guard (t == txt)) <?> ("\\begin{" ++ T.unpack t ++ "}")

end_ :: PandocMonad m => Text -> SP m ()
end_ t = (try $ do
  controlSeq "end"
  spaces
  txt <- untokenize <$> braced
  guard $ t == txt) <?> ("\\end{" ++ T.unpack t ++ "}")

preamble :: PandocMonad m => SP m Blocks
preamble = mempty <$ many preambleBlock
  where preambleBlock =  spaces1
                     <|> void include
                     <|> void blockCommand
                     <|> void braced
                     <|> (notFollowedBy (begin_ "document") >> void anyTok)

paragraph :: PandocMonad m => SP m Blocks
paragraph = do
  x <- trimInlines . mconcat <$> many1 inline
  if x == mempty
     then return mempty
     else return $ para x

include :: PandocMonad m => SP m Blocks
include = do
  (Tok _ (CtrlSeq name) _) <-
                    controlSeq "include" <|> controlSeq "input" <|>
                    controlSeq "subfile" <|> controlSeq "usepackage"
  skipMany opt
  fs <- (map (T.unpack . removeDoubleQuotes . T.strip) . T.splitOn "," .
         untokenize) <$> braced
  let fs' = if name == "usepackage"
               then map (maybeAddExtension ".sty") fs
               else map (maybeAddExtension ".tex") fs
  dirs <- (splitBy (==':') . fromMaybe ".") <$> lookupEnv "TEXINPUTS"
  mapM_ (insertIncluded dirs) fs'
  return mempty


addMeta :: PandocMonad m => ToMetaValue a => String -> a -> SP m ()
addMeta field val = updateState $ \st ->
   st{ sMeta = addMetaField field val $ sMeta st }

authors :: PandocMonad m => SP m ()
authors = try $ do
  bgroup
  let oneAuthor = mconcat <$>
       many1 (notFollowedBy' (controlSeq "and") >>
               (inline <|> mempty <$ blockCommand))
               -- skip e.g. \vspace{10pt}
  auths <- sepBy oneAuthor (controlSeq "and")
  egroup
  addMeta "author" (map trimInlines auths)

bracketedToks :: PandocMonad m => SP m [Tok]
bracketedToks = do
  symbol '['
  mconcat <$> manyTill (braced <|> (:[]) <$> anyTok) (symbol ']')

bracketedNum :: PandocMonad m => SP m Int
bracketedNum = do
  ds <- untokenize <$> bracketedToks
  case safeRead (T.unpack ds) of
       Just i -> return i
       _      -> return 0

setCaption :: PandocMonad m => SP m Blocks
setCaption = do
  ils <- tok
  mblabel <- option Nothing $
               try $ spaces >> controlSeq "label" >> (Just <$> tok)
  let ils' = case mblabel of
                  Just lab -> ils <> spanWith
                                ("",[],[("label", stringify lab)]) mempty
                  Nothing  -> ils
  updateState $ \st -> st{ sCaption = Just ils' }
  return mempty

looseItem :: PandocMonad m => SP m Blocks
looseItem = do
  inListItem <- sInListItem <$> getState
  guard $ not inListItem
  skipopts
  return mempty

resetCaption :: PandocMonad m => SP m ()
resetCaption = updateState $ \st -> st{ sCaption = Nothing }

section :: PandocMonad m => Bool -> Attr -> Int -> SP m Blocks
section starred (ident, classes, kvs) lvl = do
  skipopts
  contents <- grouped inline
  lab <- option ident $
          try (spaces >> controlSeq "label"
               >> spaces >> toksToString <$> braced)
  let classes' = if starred then "unnumbered" : classes else classes
  unless starred $ do
    hn <- sLastHeaderNum <$> getState
    let num = incrementHeaderNum lvl hn
    updateState $ \st -> st{ sLastHeaderNum = num }
    updateState $ \st -> st{ sLabels = M.insert lab
                            [Str (renderHeaderNum num)]
                            (sLabels st) }
  attr' <- registerHeader (lab, classes', kvs) contents
  return $ headerWith attr' lvl contents

blockCommand :: PandocMonad m => SP m Blocks
blockCommand = try $ do
  Tok _ (CtrlSeq name) txt <- anyControlSeq
  guard $ name /= "begin" && name /= "end"
  star <- option "" ("*" <$ symbol '*' <* optional sp)
  let name' = name <> star
  let names = ordNub [name', name]
  let rawDefiniteBlock = do
        guard $ isBlockCommand name
        rawBlock "latex" <$> getRawCommand name (txt <> star)
  -- heuristic:  if it could be either block or inline, we
  -- treat it if block if we have a sequence of block
  -- commands followed by a newline.  But we stop if we
  -- hit a \startXXX, since this might start a raw ConTeXt
  -- environment (this is important because this parser is
  -- used by the Markdown reader).
  let startCommand = try $ do
        Tok _ (CtrlSeq n) _ <- anyControlSeq
        guard $ "start" `T.isPrefixOf` n
  let rawMaybeBlock = try $ do
        guard $ not $ isInlineCommand name
        curr <- rawBlock "latex" <$> getRawCommand name (txt <> star)
        rest <- many $ notFollowedBy startCommand *> blockCommand
        lookAhead $ blankline <|> startCommand
        return $ curr <> mconcat rest
  let raw = rawDefiniteBlock <|> rawMaybeBlock
  lookupListDefault raw names blockCommands

closing :: PandocMonad m => SP m Blocks
closing = do
  contents <- tok
  st <- getState
  let extractInlines (MetaBlocks [Plain ys]) = ys
      extractInlines (MetaBlocks [Para ys ]) = ys
      extractInlines _                       = []
  let sigs = case lookupMeta "author" (sMeta st) of
                  Just (MetaList xs) ->
                    para $ trimInlines $ fromList $
                      intercalate [LineBreak] $ map extractInlines xs
                  _ -> mempty
  return $ para (trimInlines contents) <> sigs

blockCommands :: PandocMonad m => M.Map Text (SP m Blocks)
blockCommands = M.fromList $
  [ ("par", mempty <$ skipopts)
  , ("title", mempty <$ (skipopts *>
                          (grouped inline >>= addMeta "title")
                      <|> (grouped block >>= addMeta "title")))
  , ("subtitle", mempty <$ (skipopts *> tok >>= addMeta "subtitle"))
  , ("author", mempty <$ (skipopts *> authors))
  , ("chapter", updateState (\s -> s{ stateHasChapters = True })
                      *> section nullAttr 0)
  , ("section", section nullAttr 1)
  , ("subsection", section nullAttr 2)
  , ("subsubsection", section nullAttr 3)
  , ("paragraph", section nullAttr 4)
  , ("subparagraph", section nullAttr 5)
  , ("hrule", pure horizontalRule)
  , ("rule", skipopts *> tok *> tok *> pure horizontalRule)
  , ("item", skipopts *> looseItem)
  , ("PandocStartInclude", startInclude)
  , ("PandocEndInclude", endInclude)
  ]


environments :: PandocMonad m => M.Map Text (SP m Blocks)
environments = M.fromList
   [ ("document", env "document" blocks)
   , ("center", env "center" blocks)
   , ("quote", blockQuote <$> env "quote" blocks)
   , ("verse", blockQuote <$> env "verse" blocks)
   , ("listarea", bulletList <$> listenv "itemize" (many item))
   , ("comment", mempty <$ verbEnv "comment")
   , ("obeylines", obeylines)
   , ("align", mathEnvWith para (Just "aligned") "align")
   ]
environment :: PandocMonad m => SP m Blocks
environment = do
  controlSeq "begin"
  name <- untokenize <$> braced
  M.findWithDefault mzero name environments
    <|> rawEnv name

env :: PandocMonad m => Text -> SP m a -> SP m a
env name p = p <* end_ name

rawEnv :: PandocMonad m => Text -> SP m Blocks
rawEnv name = do
  exts <- getOption readerExtensions
  let parseRaw = extensionEnabled Ext_raw_tex exts
  rawOptions <- mconcat <$> many rawopt
  let beginCommand = "\\begin{" <> name <> "}" <> rawOptions
  pos1 <- getPosition
  (bs, raw) <- withRaw $ env name blocks
  if parseRaw
     then return $ rawBlock "latex"
                 $ T.unpack $ beginCommand <> untokenize raw
     else do
       report $ SkippedContent (T.unpack beginCommand) pos1
       pos2 <- getPosition
       report $ SkippedContent ("\\end{" ++ T.unpack name ++ "}") pos2
       return bs

obeylines :: PandocMonad m => SP m Blocks
obeylines = do
  para . fromList . removeLeadingTrailingBreaks .
     walk softBreakToHard . toList <$> env "obeylines" inlines
  where softBreakToHard SoftBreak = LineBreak
        softBreakToHard x         = x
        removeLeadingTrailingBreaks = reverse . dropWhile isLineBreak .
                                      reverse . dropWhile isLineBreak
        isLineBreak LineBreak     = True
        isLineBreak _             = False

-- lists

item :: PandocMonad m => SP m Blocks
item = void blocks *> controlSeq "item" *> skipopts *> blocks

descItem :: PandocMonad m => SP m (Inlines, [Blocks])
descItem = do
  blocks -- skip blocks before item
  controlSeq "item"
  optional sp
  ils <- opt
  bs <- blocks
  return (ils, [bs])

listenv :: PandocMonad m => Text -> SP m a -> SP m a
listenv name p = try $ do
  oldInListItem <- sInListItem `fmap` getState
  updateState $ \st -> st{ sInListItem = True }
  res <- env name p
  updateState $ \st -> st{ sInListItem = oldInListItem }
  return res

orderedList' :: PandocMonad m => SP m Blocks
orderedList' = try $ do
  spaces
  let markerSpec = do
        symbol '['
        ts <- toksToString <$> manyTill anyTok (symbol ']')
        case runParser anyOrderedListMarker def "option" ts of
             Right r -> return r
             Left _  -> do
               pos <- getPosition
               report $ SkippedContent ("[" ++ ts ++ "]") pos
               return (1, DefaultStyle, DefaultDelim)
  (_, style, delim) <- option (1, DefaultStyle, DefaultDelim) markerSpec
  spaces
  optional $ try $ controlSeq "setlength"
                   *> grouped (count 1 $ controlSeq "itemindent")
                   *> braced
  spaces
  start <- option 1 $ try $ do pos <- getPosition
                               controlSeq "setcounter"
                               ctr <- toksToString <$> braced
                               guard $ "enum" `isPrefixOf` ctr
                               guard $ all (`elem` ['i','v']) (drop 4 ctr)
                               optional sp
                               num <- toksToString <$> braced
                               case safeRead num of
                                    Just i -> return (i + 1 :: Int)
                                    Nothing -> do
                                      report $ SkippedContent
                                        ("\\setcounter{" ++ ctr ++
                                         "}{" ++ num ++ "}") pos
                                      return 1
  bs <- listenv "enumerate" (many item)
  return $ orderedListWith (start, style, delim) bs

-- tables



startInclude :: SP Blocks
startInclude = do
  fn <- braced
  setPosition $ newPos fn 1 1
  return mempty

endInclude :: SP Blocks
endInclude = do
  fn <- braced
  ln <- braced
  co <- braced
  setPosition $ newPos fn (fromMaybe 1 $ safeRead ln) (fromMaybe 1 $ safeRead co)
  return mempty




block :: PandocMonad m => SP m Blocks
block = (mempty <$ spaces1)
    <|> environment
    <|> include
    <|> blockCommand
    <|> paragraph
    <|> grouped block

blocks :: PandocMonad m => SP m Blocks
blocks = mconcat <$> many block
