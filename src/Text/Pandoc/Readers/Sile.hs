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
import Text.Pandoc.Readers.Sile.Parsing
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
      headerLevel _              = []
  let bottomLevel = minimumDef 1 $ query headerLevel doc'
  let adjustHeaders m (Header n attr ils) = Header (n+m) attr ils
      adjustHeaders _ x                   = x
  let (Pandoc _ bs') =
       -- handle the case where you have \part or \chapter
       (if bottomLevel < 1
           then walk (adjustHeaders (1 - bottomLevel))
           else id) $
       walk (resolveRefs (sLabels st)) doc'
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


rawSileBlock :: (PandocMonad m, HasReaderOptions s)
              => ParserT String s m String
rawSileBlock = do
  lookAhead (try (char '\\' >> letter))
  snd <$> (rawSileParser True
           (environment <|> blockCommand)
           (mconcat <$> (many (block <|> beginOrEndCommand))))

-- See #4667 for motivation; sometimes people write macros
-- that just evaluate to a begin or end command, which blockCommand
-- won't accept.
beginOrEndCommand :: PandocMonad m => LP m Blocks
beginOrEndCommand = try $ do
  Tok _ (CtrlSeq name) txt <- anyControlSeq
  guard $ name == "begin" || name == "end"
  (envname, rawargs) <- withRaw braced
  if M.member (untokenize envname)
      (inlineEnvironments :: M.Map Text (LP PandocPure Inlines))
     then mzero
     else return $ rawBlock "latex"
                    (T.unpack (txt <> untokenize rawargs))

rawSileInline :: (PandocMonad m, HasReaderOptions s)
               => ParserT String s m String
rawSileInline = do
  lookAhead (try (char '\\' >> letter))
  snd <$> (  rawSileParser True
              (mempty <$ (controlSeq "input" >> skipMany opt >> braced))
              inlines
        <|> rawSileParser True (inlineEnvironment <|> inlineCommand') inlines)

inlineCommand :: PandocMonad m => ParserT String ParserState m Inlines
inlineCommand = do
  lookAhead (try (char '\\' >> letter))
  fst <$> rawSileParser True (inlineEnvironment <|> inlineCommand') inlines

-- inline elements:

word :: PandocMonad m => LP m Inlines
word = (str . T.unpack . untoken) <$> satisfyTok isWordTok

regularSymbol :: PandocMonad m => LP m Inlines
regularSymbol = (str . T.unpack . untoken) <$> satisfyTok isRegularSymbol
  where isRegularSymbol (Tok _ Symbol t) = not $ T.any isSpecial t
        isRegularSymbol _                = False
        isSpecial c = c `Set.member` specialChars

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
singleQuote =
       quoted' singleQuoted ((:[]) <$> symbol '`')
                     (try $ symbol '\'' >>
                           notFollowedBy (satisfyTok startsWithLetter))
   <|> quoted' singleQuoted ((:[]) <$> symbol '‘')
                            (try $ symbol '’' >>
                                  notFollowedBy (satisfyTok startsWithLetter))
  where startsWithLetter (Tok _ Word t) =
          case T.uncons t of
               Just (c, _) | isLetter c -> True
               _           -> False
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
skipopts = skipMany (void rawopt)

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


looseItem :: PandocMonad m => LP m Blocks
looseItem = do
  skipopts
  return mempty

resetCaption :: PandocMonad m => LP m ()
resetCaption = updateState $ \st -> st{ sCaption = (Nothing, Nothing) }

section :: PandocMonad m => Attr -> Int -> LP m Blocks
section (ident, classes, kvs) lvl = do
  skipopts
  contents <- grouped inline
  lab <- option ident $
          try (spaces >> controlSeq "label"
               >> spaces >> toksToString <$> braced)
  when (lvl == 0) $
    updateState $ \st -> st{ sHasChapters = True }
  unless ("unnumbered" `elem` classes) $ do
    hn <- sLastHeaderNum <$> getState
    hasChapters <- sHasChapters <$> getState
    let lvl' = lvl + if hasChapters then 1 else 0
    let num = incrementDottedNum lvl' hn
    updateState $ \st -> st{ sLastHeaderNum = num
                           , sLabels = M.insert lab
                              [Str (renderDottedNum num)]
                              (sLabels st) }
  attr' <- registerHeader (lab, classes, kvs) contents
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
        rawcontents <- getRawCommand name (txt <> star)
        (guardEnabled Ext_raw_sile >> return (rawBlock "sile" rawcontents))
          <|> ignore rawcontents
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
        rawcontents <- getRawCommand name (txt <> star)
        curr <- (guardEnabled Ext_raw_sile >>
                    return (rawBlock "sile" rawcontents))
                   <|> ignore rawcontents
        rest <- many $ notFollowedBy startCommand *> blockCommand
        lookAhead $ blankline <|> startCommand
        return $ curr <> mconcat rest
  let raw = rawDefiniteBlock <|> rawMaybeBlock
  lookupListDefault raw names blockCommands

closing :: PandocMonad m => LP m Blocks
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

blockCommands :: PandocMonad m => M.Map Text (LP m Blocks)
blockCommands = M.fromList
   [ ("par", mempty <$ skipopts)
   , ("title", mempty <$ (skipopts *>
                             (grouped inline >>= addMeta "title")
                         <|> (grouped block >>= addMeta "title")))
   , ("subtitle", mempty <$ (skipopts *> tok >>= addMeta "subtitle"))
   , ("author", mempty <$ (skipopts *> authors))
   , ("part", section nullAttr (-1))
   , ("chapter", section nullAttr 0)
   , ("section", section nullAttr 1)
   , ("subsubsection", section nullAttr 3)
   , ("paragraph", section nullAttr 4)
   , ("subparagraph", section nullAttr 5)
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
