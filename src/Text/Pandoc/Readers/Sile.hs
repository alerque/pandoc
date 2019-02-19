{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-
Copyright (C) 2006-2018 John MacFarlane <jgm@berkeley.edu>

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
   Copyright   : Copyright (C) 2015-2019 Caleb Maclennan
   License     : GNU GPL, version 2 or above

   Maintainer  : Caleb Maclennan <caleb@alerque.com>
   Stability   : alpha
   Portability : portable

Conversion of Sile to 'Pandoc' document.

-}
module Text.Pandoc.Readers.Sile (  readSile,
                                   rawSileInline,
                                   rawSileBlock,
                                   inlineCommand,
                                   tokenize,
                                   untokenize
                                 ) where

import Prelude
import Control.Applicative (many, optional, (<|>))
import Control.Monad
import Control.Monad.Except (throwError)
import Data.Char (isDigit, isLetter, toLower, toUpper)
import Data.Default
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Safe (minimumDef)
import System.FilePath (addExtension, replaceExtension, takeExtension)
import Text.Pandoc.Builder
import Text.Pandoc.Class (PandocMonad, PandocPure, getResourcePath, lookupEnv,
                          readFileFromDirs, report, setResourcePath,
                          setTranslations, translateTerm, trace)
import Text.Pandoc.Error (PandocError ( PandocParseError, PandocParsecError))
import Text.Pandoc.ImageSize (numUnit, showFl)
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.Pandoc.Parsing hiding (blankline, many, mathDisplay, mathInline,
                            optional, space, spaces, withRaw, (<|>))
import Text.Pandoc.Readers.Sile.Types (ExpansionPoint (..), Macro (..),
                                        ArgSpec (..), Tok (..), TokType (..))
-- import Text.Pandoc.Readers.Sile.Parsing
import Text.Pandoc.Shared
import qualified Text.Pandoc.Translations as Translations
import Text.Pandoc.Walk
import qualified Text.Pandoc.Builder as B
import qualified Data.Text.Normalize as Normalize

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

parseSile :: PandocMonad m => LP m Pandoc
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


-- testParser :: LP PandocIO a -> Text -> IO a
-- testParser p t = do
--   res <- runIOorExplode (runParserT p defaultSileState{
--             sOptions = def{ readerExtensions =
--               enableExtension Ext_raw_tex $
--                 getDefaultExtensions "sile" }} "source" (tokenize "source" t))
--   case res of
--        Left e  -> error (show e)
--        Right r -> return r

newtype HeaderNum = HeaderNum [Int]
  deriving (Show)

renderHeaderNum :: HeaderNum -> String
renderHeaderNum (HeaderNum xs) =
  intercalate "." (map show xs)

incrementHeaderNum :: Int -> HeaderNum -> HeaderNum
incrementHeaderNum level (HeaderNum ns) = HeaderNum $
  case reverse (take level (ns ++ repeat 0)) of
       (x:xs) -> reverse (x+1 : xs)
       []     -> []  -- shouldn't happen

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

-- instance HasHeaderMap SileState where
--   extractHeaderMap     = sHeaders
--   updateHeaderMap f st = st{ sHeaders = f $ sHeaders st }

instance HasReaderOptions SileState where
  extractReaderOptions = sOptions

instance HasMeta SileState where
  setMeta field val st =
    st{ sMeta = setMeta field val $ sMeta st }
  deleteMeta field st =
    st{ sMeta = deleteMeta field $ sMeta st }

instance Default SileState where
  def = defaultSileState

type LP m = ParserT [Tok] SileState m

rawSileParser :: (PandocMonad m, HasReaderOptions s)
               => LP m a -> ParserT String s m String
rawSileParser parser = do
  inp <- getInput
  let toks = tokenize "source" $ T.pack inp
  pstate <- getState
  let lstate = def{ sOptions = extractReaderOptions pstate }
  res <- lift $ runParserT ((,) <$> try (snd <$> withRaw parser) <*> getState)
            lstate "source" toks
  case res of
       Left _    -> mzero
       Right (raw, _) -> do
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
       Right (il, raw, _) -> do
         takeP (T.length (untokenize raw))
         return il

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

satisfyTok :: PandocMonad m => (Tok -> Bool) -> LP m Tok
satisfyTok f =
  try $ do
    res <- tokenPrim (T.unpack . untoken) updatePos matcher
    return res
  where matcher t | f t       = Just t
                  | otherwise = Nothing
        updatePos :: SourcePos -> Tok -> [Tok] -> SourcePos
        updatePos _spos _ (Tok pos _ _ : _) = pos
        updatePos spos _ [] = spos

anyControlSeq :: PandocMonad m => LP m Tok
anyControlSeq = satisfyTok isCtrlSeq
  where isCtrlSeq (Tok _ (CtrlSeq _) _) = True
        isCtrlSeq _                     = False

spaces :: PandocMonad m => LP m ()
spaces = skipMany (satisfyTok (tokTypeIn [Comment, Spaces, Newline]))

spaces1 :: PandocMonad m => LP m ()
spaces1 = skipMany1 (satisfyTok (tokTypeIn [Comment, Spaces, Newline]))

tokTypeIn :: [TokType] -> Tok -> Bool
tokTypeIn toktypes (Tok _ tt _) = tt `elem` toktypes

controlSeq :: PandocMonad m => Text -> LP m Tok
controlSeq name = satisfyTok isNamed
  where isNamed (Tok _ (CtrlSeq n) _) = n == name
        isNamed _ = False

symbol :: PandocMonad m => Char -> LP m Tok
symbol c = satisfyTok isc
  where isc (Tok _ Symbol d) = case T.uncons d of
                                    Just (c',_) -> c == c'
                                    _ -> False
        isc _ = False

symbolIn :: PandocMonad m => [Char] -> LP m Tok
symbolIn cs = satisfyTok isInCs
  where isInCs (Tok _ Symbol d) = case T.uncons d of
                                       Just (c,_) -> c `elem` cs
                                       _ -> False
        isInCs _ = False

sp :: PandocMonad m => LP m ()
sp = whitespace <|> endline

whitespace :: PandocMonad m => LP m ()
whitespace = () <$ satisfyTok isSpaceTok
  where isSpaceTok (Tok _ Spaces _) = True
        isSpaceTok _ = False

newlineTok :: PandocMonad m => LP m ()
newlineTok = () <$ satisfyTok isNewlineTok

isNewlineTok :: Tok -> Bool
isNewlineTok (Tok _ Newline _) = True
isNewlineTok _ = False

comment :: PandocMonad m => LP m ()
comment = () <$ satisfyTok isCommentTok
  where isCommentTok (Tok _ Comment _) = True
        isCommentTok _ = False

anyTok :: PandocMonad m => LP m Tok
anyTok = satisfyTok (const True)

endline :: PandocMonad m => LP m ()
endline = try $ do
  newlineTok
  lookAhead anyTok
  notFollowedBy blankline

blankline :: PandocMonad m => LP m ()
blankline = try $ skipMany whitespace *> newlineTok

primEscape :: PandocMonad m => LP m Char
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

bgroup :: PandocMonad m => LP m Tok
bgroup = try $ do
  skipMany sp
  symbol '{' <|> controlSeq "bgroup" <|> controlSeq "begingroup"

egroup :: PandocMonad m => LP m Tok
egroup = (symbol '}' <|> controlSeq "egroup" <|> controlSeq "endgroup")

grouped :: (PandocMonad m,  Monoid a) => LP m a -> LP m a
grouped parser = try $ do
  bgroup
  -- first we check for an inner 'grouped', because
  -- {{a,b}} should be parsed the same as {a,b}
  try (grouped parser <* egroup) <|> (mconcat <$> manyTill parser egroup)

braced :: PandocMonad m => LP m [Tok]
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

bracketed :: PandocMonad m => Monoid a => LP m a -> LP m a
bracketed parser = try $ do
  symbol '['
  mconcat <$> manyTill parser (symbol ']')

dimenarg :: PandocMonad m => LP m Text
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

word :: PandocMonad m => LP m Inlines
word = (str . T.unpack . untoken) <$> satisfyTok isWordTok

regularSymbol :: PandocMonad m => LP m Inlines
regularSymbol = (str . T.unpack . untoken) <$> satisfyTok isRegularSymbol
  where isRegularSymbol (Tok _ Symbol t) = not $ T.any isSpecial t
        isRegularSymbol _ = False
        isSpecial c = c `Set.member` specialChars

specialChars :: Set.Set Char
specialChars = Set.fromList "#$%&~_^\\{}"

isWordTok :: Tok -> Bool
isWordTok (Tok _ Word _) = True
isWordTok _ = False

inlineGroup :: PandocMonad m => LP m Inlines
inlineGroup = do
  ils <- grouped inline
  if isNull ils
     then return mempty
     else return $ spanWith nullAttr ils
          -- we need the span so we can detitlecase bibtex entries;
          -- we need to know when something is {C}apitalized

lit :: String -> LP m Inlines
lit = pure . str


doubleQuote :: PandocMonad m => LP m Inlines
doubleQuote = do
       quoted' doubleQuoted (try $ count 2 $ symbol '`')
                            (void $ try $ count 2 $ symbol '\'')
   <|> quoted' doubleQuoted ((:[]) <$> symbol '“') (void $ symbol '”')
   -- the following is used by babel for localized quotes:
   <|> quoted' doubleQuoted (try $ sequence [symbol '"', symbol '`'])
                            (void $ try $ sequence [symbol '"', symbol '\''])

singleQuote :: PandocMonad m => LP m Inlines
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
        -> LP m [Tok]
        -> LP m ()
        -> LP m Inlines
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


toksToString :: [Tok] -> String
toksToString = T.unpack . untokenize

-- citations


inlineCommand' :: PandocMonad m => LP m Inlines
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

tok :: PandocMonad m => LP m Inlines
tok = try $ spaces >> grouped inline <|> inlineCommand' <|> singleChar'
  where singleChar' = do
          Tok _ _ t <- singleChar
          return (str (T.unpack t))

opt :: PandocMonad m => LP m Inlines
opt = bracketed inline <|> (str . T.unpack <$> rawopt)

paropt :: PandocMonad m => LP m Inlines
paropt = parenWrapped inline

rawopt :: PandocMonad m => LP m Text
rawopt = try $ do
  optional sp
  inner <- untokenize <$> bracketedToks
  optional sp
  return $ "[" <> inner <> "]"

skipopts :: PandocMonad m => LP m ()
skipopts = skipMany (overlaySpecification <|> void rawopt)

overlayTok :: PandocMonad m => LP m Tok
overlayTok =
  satisfyTok (\t ->
                  case t of
                    Tok _ Word _       -> True
                    Tok _ Spaces _     -> True
                    Tok _ Symbol c     -> c `elem` ["-","+","@","|",":",","]
                    _                  -> False)

inBrackets :: Inlines -> Inlines
inBrackets x = str "[" <> x <> str "]"


unescapeURL :: String -> String
unescapeURL ('\\':x:xs) | isEscapable x = x:unescapeURL xs
  where isEscapable c = c `elem` ("#$%&~_^\\{}" :: String)
unescapeURL (x:xs) = x:unescapeURL xs
unescapeURL [] = ""

inlineEnvironment :: PandocMonad m => LP m Inlines
inlineEnvironment = try $ do
  controlSeq "begin"
  name <- untokenize <$> braced
  M.findWithDefault mzero name inlineEnvironments

inlineEnvironments :: PandocMonad m => M.Map Text (LP m Inlines)
inlineEnvironments = M.fromList [
  ]

inlineCommands :: PandocMonad m => M.Map Text (LP m Inlines)
inlineCommands = M.fromList
  [ ("em", extractSpaces emph <$> tok)
  , ("strike", extractSpaces strikeout <$> tok)
  , ("textsuperscript", extractSpaces superscript <$> tok)
  , ("textsubscript", extractSpaces subscript <$> tok)
  , ("strong", extractSpaces strong <$> tok)
  , ("textnormal", extractSpaces (spanWith ("",["nodecor"],[])) <$> tok)
  , ("noindent", pure mempty)
  , ("%", lit "%")
  , ("{", lit "{")
  , ("}", lit "}")
  , ("break", linebreak <$ (optional (bracketed inline) *> spaces1))
  , ("footnote", note <$> grouped block)
  , ("texttt", (code . stringify . toList) <$> tok)
  , ("url", ((unescapeURL . T.unpack . untokenize) <$> braced) >>= \url ->
                  pure (link url "" (str url)))
  , ("href", (unescapeURL . toksToString <$>
                 braced <* optional sp) >>= \url ->
                   tok >>= \lab -> pure (link url "" lab))
  ]


getRawCommand :: PandocMonad m => Text -> Text -> LP m String
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
  s `M.member` (blockCommands :: M.Map Text (LP PandocPure Blocks))
  || s `Set.member` treatAsBlock

treatAsBlock :: Set.Set Text
treatAsBlock = Set.fromList
   [ "framebreak"
   , "pagebreak"
   ]

isInlineCommand :: Text -> Bool
isInlineCommand s =
  s `M.member` (inlineCommands :: M.Map Text (LP PandocPure Inlines))
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

inline :: PandocMonad m => LP m Inlines
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
     <|> (str . (:[]) <$> primEscape)
     <|> regularSymbol
     <|> (do res <- symbolIn "#^'`\"[]"
             pos <- getPosition
             let s = T.unpack (untoken res)
             report $ ParsingUnescaped s pos
             return $ str s)

inlines :: PandocMonad m => LP m Inlines
inlines = mconcat <$> many inline

-- block elements:


end_ :: PandocMonad m => Text -> LP m ()
end_ t = (try $ do
  controlSeq "end"
  spaces
  txt <- untokenize <$> braced
  guard $ t == txt) <?> ("\\end{" ++ T.unpack t ++ "}")


paragraph :: PandocMonad m => LP m Blocks
paragraph = do
  x <- trimInlines . mconcat <$> many1 inline
  if x == mempty
     then return mempty
     else return $ para x


addMeta :: PandocMonad m => ToMetaValue a => String -> a -> LP m ()
addMeta field val = updateState $ \st ->
   st{ sMeta = addMetaField field val $ sMeta st }

authors :: PandocMonad m => LP m ()
authors = try $ do
  bgroup
  let oneAuthor = mconcat <$>
       many1 (notFollowedBy' (controlSeq "and") >>
               (inline <|> mempty <$ blockCommand))
               -- skip e.g. \vspace{10pt}
  auths <- sepBy oneAuthor (controlSeq "and")
  egroup
  addMeta "author" (map trimInlines auths)

bracketedToks :: PandocMonad m => LP m [Tok]
bracketedToks = do
  symbol '['
  mconcat <$> manyTill (braced <|> (:[]) <$> anyTok) (symbol ']')


looseItem :: PandocMonad m => LP m Blocks
looseItem = do
  skipopts
  return mempty

section :: PandocMonad m => Bool -> Attr -> Int -> LP m Blocks
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

blockCommand :: PandocMonad m => LP m Blocks
blockCommand = try $ do
  Tok _ (CtrlSeq name) txt <- anyControlSeq
  guard $ name /= "begin" && name /= "end"
  star <- option "" ("*" <$ symbol '*' <* optional sp)
  let name' = name <> star
  let names = ordNub [name', name]
  let rawDefiniteBlock = do
        guard $ isBlockCommand name
        rawBlock "sile" <$> getRawCommand name (txt <> star)
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
        curr <- rawBlock "sile" <$> getRawCommand name (txt <> star)
        rest <- many $ notFollowedBy startCommand *> blockCommand
        lookAhead $ blankline <|> startCommand
        return $ curr <> mconcat rest
  let raw = rawDefiniteBlock <|> rawMaybeBlock
  lookupListDefault raw names blockCommands

blockCommands :: PandocMonad m => M.Map Text (LP m Blocks)
blockCommands = M.fromList $
  [ ("par", mempty <$ skipopts)
  , ("title", mempty <$ (skipopts *>
                          (grouped inline >>= addMeta "title")
                      <|> (grouped block >>= addMeta "title")))
  , ("subtitle", mempty <$ (skipopts *> tok >>= addMeta "subtitle"))
  , ("author", mempty <$ (skipopts *> authors))
   , ("chapter", section False nullAttr 0)
   , ("subsection", section False nullAttr 2)
   , ("subsubsection", section False nullAttr 3)
   , ("paragraph", section False nullAttr 4)
   , ("subparagraph", section False nullAttr 5)
   , ("hrule", pure horizontalRule)
   , ("rule", skipopts *> tok *> tok *> pure horizontalRule)
   , ("item", skipopts *> looseItem)
   ]


environments :: PandocMonad m => M.Map Text (LP m Blocks)
environments = M.fromList
   [ ("document", env "document" blocks)
   , ("center", env "center" blocks)
   , ("quote", blockQuote <$> env "quote" blocks)
   , ("verse", blockQuote <$> env "verse" blocks)
   , ("listarea", bulletList <$> listenv "itemize" (many item))
   , ("obeylines", obeylines)
   ]
environment :: PandocMonad m => LP m Blocks
environment = try $ do
  controlSeq "begin"
  name <- untokenize <$> braced
  M.findWithDefault mzero name environments <|>
    if M.member name (inlineEnvironments
                       :: M.Map Text (LP PandocPure Inlines))
       then mzero
       else rawEnv name

env :: PandocMonad m => Text -> LP m a -> LP m a
env name p = p <* end_ name

rawEnv :: PandocMonad m => Text -> LP m Blocks
rawEnv name = do
  exts <- getOption readerExtensions
  let parseRaw = extensionEnabled Ext_raw_tex exts
  rawOptions <- mconcat <$> many rawopt
  let beginCommand = "\\begin{" <> name <> "}" <> rawOptions
  pos1 <- getPosition
  (bs, raw) <- withRaw $ env name blocks
  if parseRaw
     then return $ rawBlock "sile"
                 $ T.unpack $ beginCommand <> untokenize raw
     else do
       report $ SkippedContent (T.unpack beginCommand) pos1
       pos2 <- getPosition
       report $ SkippedContent ("\\end{" ++ T.unpack name ++ "}") pos2
       return bs

obeylines :: PandocMonad m => LP m Blocks
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

item :: PandocMonad m => LP m Blocks
item = void blocks *> controlSeq "item" *> skipopts *> blocks

descItem :: PandocMonad m => LP m (Inlines, [Blocks])
descItem = do
  blocks -- skip blocks before item
  controlSeq "item"
  optional sp
  ils <- opt
  bs <- blocks
  return (ils, [bs])

listenv :: PandocMonad m => Text -> LP m a -> LP m a
listenv name p = try $ do
  res <- env name p
  return res

-- tables






block :: PandocMonad m => LP m Blocks
block = do
  res <- (mempty <$ spaces1)
    <|> environment
    <|> blockCommand
    <|> paragraph
    <|> grouped block
  trace (take 60 $ show $ B.toList res)
  return res

blocks :: PandocMonad m => LP m Blocks
blocks = mconcat <$> many block
