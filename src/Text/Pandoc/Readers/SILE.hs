{-# LANGUAGE CPP                   #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternGuards         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE ViewPatterns          #-}
{- |
   Module      : Text.Pandoc.Readers.SILE
   Copyright   : Copyright (C) 2015-2020 Caleb Maclennan
   License     : GNU GPL, version 2 or above

   Maintainer  : Caleb Maclennan <caleb@alerque.com>
   Stability   : alpha
   Portability : portable

Conversion of SILE to 'Pandoc' document.

-}
module Text.Pandoc.Readers.SILE (  readSILE,
                                   rawSILEInline,
                                   rawSILEBlock,
                                   inlineCommand,
                                   tokenize,
                                   untokenize
                                 ) where

import Prelude
import Control.Applicative (many, optional, (<|>))
import Control.Monad
import Control.Monad.Except (throwError)
import Data.Char (isDigit, isLetter, toUpper, chr)
import Data.Default
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, maybeToList)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import System.FilePath (addExtension, replaceExtension, takeExtension)
import Text.Pandoc.BCP47 (Lang (..), renderLang)
import Text.Pandoc.Builder
import Text.Pandoc.Class (PandocMonad, PandocPure, getResourcePath, lookupEnv,
                          readFileFromDirs, report, setResourcePath,
                          setTranslations, translateTerm, trace, fileExists)
import Text.Pandoc.Error (PandocError (PandocParseError, PandocParsecError))
import Text.Pandoc.Highlighting (fromListingsLanguage, languagesByExtension)
import Text.Pandoc.ImageSize (numUnit, showFl)
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.Pandoc.Parsing hiding (blankline, many, mathDisplay, mathInline,
                            optional, space, spaces, withRaw, (<|>))
import Text.Pandoc.Readers.SILE.Types (ExpansionPoint (..), Macro (..),
                                        ArgSpec (..), Tok (..), TokType (..))
import Text.Pandoc.Readers.SILE.Parsing
import Text.Pandoc.Shared
import qualified Text.Pandoc.Translations as Translations
import Text.Pandoc.Walk
import qualified Text.Pandoc.Builder as B
import qualified Data.Text.Normalize as Normalize
import Safe

-- for debugging:
-- import Text.Pandoc.Extensions (getDefaultExtensions)
-- import Text.Pandoc.Class (runIOorExplode, PandocIO)
-- import Debug.Trace (traceShowId)

-- | Parse SILE from string and return 'Pandoc' document.
readSILE :: PandocMonad m
          => ReaderOptions -- ^ Reader options
          -> Text        -- ^ String to parse (assumes @'\n'@ line endings)
          -> m Pandoc
readSILE opts ltx = do
  parsed <- runParserT parseSILE def{ sOptions = opts } "source"
               (tokenize "source" (crFilter ltx))
  case parsed of
    Right result -> return result
    Left e       -> throwError $ PandocParsecError ltx e

parseSILE :: PandocMonad m => LP m Pandoc
parseSILE = do
  bs <- blocks
  eof
  st <- getState
  let meta = sMeta st
  let doc' = doc bs
  let headerLevel (Header n _ _) = [n]
      headerLevel _              = []
#if MIN_VERSION_safe(0,3,18)
  let bottomLevel = minimumBound 1 $ query headerLevel doc'
#else
  let bottomLevel = minimumDef 1 $ query headerLevel doc'
#endif
  let adjustHeaders m (Header n attr ils) = Header (n+m) attr ils
      adjustHeaders _ x                   = x
  let (Pandoc _ bs') =
       -- handle the case where you have \part or \chapter
       (if bottomLevel < 1
           then walk (adjustHeaders (1 - bottomLevel))
           else id) $
       walk (resolveRefs (sLabels st)) doc'
  return $ Pandoc meta bs'

resolveRefs :: M.Map Text [Inline] -> Inline -> Inline
resolveRefs labels x@(Link (ident,classes,kvs) _ _) =
  case (lookup "reference-type" kvs,
        lookup "reference" kvs) of
        (Just "ref", Just lab) ->
          case M.lookup lab labels of
               Just txt -> Link (ident,classes,kvs) txt ("#" <> lab, "")
               Nothing  -> x
        _ -> x
resolveRefs _ x = x


-- testParser :: LP PandocIO a -> Text -> IO a
-- testParser p t = do
--   res <- runIOorExplode (runParserT p defaultSILEState{
--             sOptions = def{ readerExtensions =
--               enableExtension Ext_raw_sile $
--                 getDefaultExtensions "sile" }} "source" (tokenize "source" t))
--   case res of
--        Left e  -> error (show e)
--        Right r -> return r


rawSILEBlock :: (PandocMonad m, HasMacros s, HasReaderOptions s)
              => ParserT Text s m Text
rawSILEBlock = do
  lookAhead (try (char '\\' >> letter))
  inp <- getInput
  let toks = tokenize "source" inp
  snd <$> (rawSILEParser toks False mempty blocks
      <|> (rawSILEParser toks True
             (do choice (map controlSeq
                   ["include", "input", "subfile", "usepackage"])
                 skipMany opt
                 braced
                 return mempty) blocks)
      <|> rawSILEParser toks True
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
     else return $ rawBlock "sile"
                    (txt <> untokenize rawargs)

rawSILEInline :: (PandocMonad m, HasReaderOptions s)
               => ParserT Text s m Text
rawSILEInline = do
  lookAhead (try (char '\\' >> letter))
  inp <- getInput
  let toks = tokenize "source" inp
  raw <- snd <$>
          (   rawSILEParser toks True
              (mempty <$ (controlSeq "input" >> skipMany opt >> braced))
              inlines
          <|> rawSILEParser toks True (inlineEnvironment <|> inlineCommand')
              inlines
          )
  finalbraces <- mconcat <$> many (try (string "{}")) -- see #5439
  return $ raw <> T.pack finalbraces

inlineCommand :: PandocMonad m => ParserT Text ParserState m Inlines
inlineCommand = do
  lookAhead (try (char '\\' >> letter))
  inp <- getInput
  let toks = tokenize "source" inp
  fst <$> rawSILEParser toks True (inlineEnvironment <|> inlineCommand')
          inlines

-- inline elements:

word :: PandocMonad m => LP m Inlines
word = (str . untoken) <$> satisfyTok isWordTok

regularSymbol :: PandocMonad m => LP m Inlines
regularSymbol = (str . untoken) <$> satisfyTok isRegularSymbol
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

doLHSverb :: PandocMonad m => LP m Inlines
doLHSverb =
  (codeWith ("",["haskell"],[]) . untokenize)
    <$> manyTill (satisfyTok (not . isNewlineTok)) (symbol '|')

mkImage :: PandocMonad m => [(Text, Text)] -> Text -> LP m Inlines
mkImage options (T.unpack -> src) = do
   let replaceTextwidth (k,v) =
         case numUnit v of
              Just (num, "\\textwidth") -> (k, showFl (num * 100) <> "%")
              _                         -> (k, v)
   let kvs = map replaceTextwidth
             $ filter (\(k,_) -> k `elem` ["width", "height"]) options
   let attr = ("",[], kvs)
   let alt = str "image"
   defaultExt <- getOption readerDefaultImageExtension
   let exts' = [".pdf", ".png", ".jpg", ".mps", ".jpeg", ".jbig2", ".jb2"]
   let exts  = exts' ++ map (map toUpper) exts'
   let findFile s [] = return s
       findFile s (e:es) = do
         let s' = addExtension s e
         exists <- fileExists s'
         if exists
            then return s'
            else findFile s es
   src' <- case takeExtension src of
               "" | not (T.null defaultExt) -> return $ addExtension src $ T.unpack defaultExt
                  | otherwise -> findFile src exts
               _  -> return src
   return $ imageWith attr (T.pack src') "" alt

doxspace :: PandocMonad m => LP m Inlines
doxspace =
  (space <$ lookAhead (satisfyTok startsWithLetter)) <|> return mempty
  where startsWithLetter (Tok _ Word t) =
          case T.uncons t of
               Just (c, _) | isLetter c -> True
               _           -> False
        startsWithLetter _ = False


-- converts e.g. \SI{1}[\$]{} to "$ 1" or \SI{1}{\euro} to "1 €"
dosiunitx :: PandocMonad m => LP m Inlines
dosiunitx = do
  skipopts
  value <- tok
  valueprefix <- option "" $ bracketed tok
  unit <- grouped (mconcat <$> many1 siUnit) <|> siUnit <|> tok
  let emptyOr160 "" = ""
      emptyOr160 _  = "\160"
  return . mconcat $ [valueprefix,
                      emptyOr160 valueprefix,
                      value,
                      emptyOr160 unit,
                      unit]

siUnit :: PandocMonad m => LP m Inlines
siUnit = do
  Tok _ (CtrlSeq name) _ <- anyControlSeq
  if name == "square"
     then do
       unit <- grouped (mconcat <$> many1 siUnit) <|> siUnit <|> tok
       return . mconcat $ [unit, "\178"]
     else
       case M.lookup name siUnitMap of
            Just il -> return il
            Nothing -> mzero

siUnitMap :: M.Map Text Inlines
siUnitMap = M.fromList
  [ ("fg", str "fg")
  , ("pg", str "pg")
  , ("ng", str "ng")
  , ("ug", str "μg")
  , ("mg", str "mg")
  , ("g", str "g")
  , ("kg", str "kg")
  , ("amu", str "u")
  , ("pm", str "pm")
  , ("nm", str "nm")
  , ("um", str "μm")
  , ("mm", str "mm")
  , ("cm", str "cm")
  , ("dm", str "dm")
  , ("m", str "m")
  , ("km", str "km")
  , ("as", str "as")
  , ("fs", str "fs")
  , ("ps", str "ps")
  , ("ns", str "ns")
  , ("us", str "μs")
  , ("ms", str "ms")
  , ("s", str "s")
  , ("fmol", str "fmol")
  , ("pmol", str "pmol")
  , ("nmol", str "nmol")
  , ("umol", str "μmol")
  , ("mmol", str "mmol")
  , ("mol", str "mol")
  , ("kmol", str "kmol")
  , ("pA", str "pA")
  , ("nA", str "nA")
  , ("uA", str "μA")
  , ("mA", str "mA")
  , ("A", str "A")
  , ("kA", str "kA")
  , ("ul", str "μl")
  , ("ml", str "ml")
  , ("l", str "l")
  , ("hl", str "hl")
  , ("uL", str "μL")
  , ("mL", str "mL")
  , ("L", str "L")
  , ("hL", str "hL")
  , ("mHz", str "mHz")
  , ("Hz", str "Hz")
  , ("kHz", str "kHz")
  , ("MHz", str "MHz")
  , ("GHz", str "GHz")
  , ("THz", str "THz")
  , ("mN", str "mN")
  , ("N", str "N")
  , ("kN", str "kN")
  , ("MN", str "MN")
  , ("Pa", str "Pa")
  , ("kPa", str "kPa")
  , ("MPa", str "MPa")
  , ("GPa", str "GPa")
  , ("mohm", str "mΩ")
  , ("kohm", str "kΩ")
  , ("Mohm", str "MΩ")
  , ("pV", str "pV")
  , ("nV", str "nV")
  , ("uV", str "μV")
  , ("mV", str "mV")
  , ("V", str "V")
  , ("kV", str "kV")
  , ("W", str "W")
  , ("uW", str "μW")
  , ("mW", str "mW")
  , ("kW", str "kW")
  , ("MW", str "MW")
  , ("GW", str "GW")
  , ("J", str "J")
  , ("uJ", str "μJ")
  , ("mJ", str "mJ")
  , ("kJ", str "kJ")
  , ("eV", str "eV")
  , ("meV", str "meV")
  , ("keV", str "keV")
  , ("MeV", str "MeV")
  , ("GeV", str "GeV")
  , ("TeV", str "TeV")
  , ("kWh", str "kWh")
  , ("F", str "F")
  , ("fF", str "fF")
  , ("pF", str "pF")
  , ("K", str "K")
  , ("dB", str "dB")
  , ("angstrom", str "Å")
  , ("arcmin", str "′")
  , ("arcminute", str "′")
  , ("arcsecond", str "″")
  , ("astronomicalunit", str "ua")
  , ("atomicmassunit", str "u")
  , ("atto", str "a")
  , ("bar", str "bar")
  , ("barn", str "b")
  , ("becquerel", str "Bq")
  , ("bel", str "B")
  , ("candela", str "cd")
  , ("celsius", str "°C")
  , ("centi", str "c")
  , ("coulomb", str "C")
  , ("dalton", str "Da")
  , ("day", str "d")
  , ("deca", str "d")
  , ("deci", str "d")
  , ("decibel", str "db")
  , ("degreeCelsius",str "°C")
  , ("degree", str "°")
  , ("deka", str "d")
  , ("electronvolt", str "eV")
  , ("exa", str "E")
  , ("farad", str "F")
  , ("femto", str "f")
  , ("giga", str "G")
  , ("gram", str "g")
  , ("hectare", str "ha")
  , ("hecto", str "h")
  , ("henry", str "H")
  , ("hertz", str "Hz")
  , ("hour", str "h")
  , ("joule", str "J")
  , ("katal", str "kat")
  , ("kelvin", str "K")
  , ("kilo", str "k")
  , ("kilogram", str "kg")
  , ("knot", str "kn")
  , ("liter", str "L")
  , ("litre", str "l")
  , ("lumen", str "lm")
  , ("lux", str "lx")
  , ("mega", str "M")
  , ("meter", str "m")
  , ("metre", str "m")
  , ("micro", str "μ")
  , ("milli", str "m")
  , ("minute", str "min")
  , ("mmHg", str "mmHg")
  , ("mole", str "mol")
  , ("nano", str "n")
  , ("nauticalmile", str "M")
  , ("neper", str "Np")
  , ("newton", str "N")
  , ("ohm", str "Ω")
  , ("Pa", str "Pa")
  , ("pascal", str "Pa")
  , ("percent", str "%")
  , ("per", str "/")
  , ("peta", str "P")
  , ("pico", str "p")
  , ("radian", str "rad")
  , ("second", str "s")
  , ("siemens", str "S")
  , ("sievert", str "Sv")
  , ("steradian", str "sr")
  , ("tera", str "T")
  , ("tesla", str "T")
  , ("tonne", str "t")
  , ("volt", str "V")
  , ("watt", str "W")
  , ("weber", str "Wb")
  , ("yocto", str "y")
  , ("yotta", str "Y")
  , ("zepto", str "z")
  , ("zetta", str "Z")
  ]

lit :: Text -> LP m Inlines
lit = pure . str

removeDoubleQuotes :: Text -> Text
removeDoubleQuotes t =
  Data.Maybe.fromMaybe t $ T.stripPrefix "\"" t >>= T.stripSuffix "\""

doubleQuote :: PandocMonad m => LP m Inlines
doubleQuote =
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
  startchs <- untokenize <$> starter
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

enquote :: PandocMonad m => Bool -> Maybe Text -> LP m Inlines
enquote starred mblang = do
  skipopts
  quoteContext <- sQuoteContext <$> getState
  if starred || quoteContext == InDoubleQuote
     then singleQuoted <$> withQuoteContext InSingleQuote tok
     else doubleQuoted <$> withQuoteContext InDoubleQuote tok

blockquote :: PandocMonad m => Bool -> Maybe Text -> LP m Blocks
blockquote citations mblang = do
  citePar <- if citations
                then do
                  cs <- cites NormalCitation False
                  return $ para (cite cs mempty)
                else return mempty
  bs <- grouped block
  return $ blockQuote $ (bs <> citePar)

doAcronym :: PandocMonad m => Text -> LP m Inlines
doAcronym form = do
  acro <- braced
  return . mconcat $ [spanWith ("",[],[("acronym-label", untokenize acro),
    ("acronym-form", "singular+" <> form)])
    $ str $ untokenize acro]

doAcronymPlural :: PandocMonad m => Text -> LP m Inlines
doAcronymPlural form = do
  acro <- braced
  plural <- lit "s"
  return . mconcat $ [spanWith ("",[],[("acronym-label", untokenize acro),
    ("acronym-form", "plural+" <> form)]) $
   mconcat [str $ untokenize acro, plural]]

doverb :: PandocMonad m => LP m Inlines
doverb = do
  Tok _ Symbol t <- anySymbol
  marker <- case T.uncons t of
              Just (c, ts) | T.null ts -> return c
              _            -> mzero
  withVerbatimMode $
    (code . untokenize) <$>
      manyTill (notFollowedBy newlineTok >> verbTok marker) (symbol marker)

verbTok :: PandocMonad m => Char -> LP m Tok
verbTok stopchar = do
  t@(Tok pos toktype txt) <- anyTok
  case T.findIndex (== stopchar) txt of
       Nothing -> return t
       Just i  -> do
         let (t1, t2) = T.splitAt i txt
         inp <- getInput
         setInput $ Tok (incSourceColumn pos i) Symbol (T.singleton stopchar)
                  : totoks (incSourceColumn pos (i + 1)) (T.drop 1 t2) ++ inp
         return $ Tok pos toktype t1

listingsLanguage :: [(Text, Text)] -> Maybe Text
listingsLanguage opts =
  case lookup "language" opts of
    Nothing  -> Nothing
    Just l   -> fromListingsLanguage l `mplus` Just l

dolstinline :: PandocMonad m => LP m Inlines
dolstinline = do
  options <- option [] keyvals
  let classes = maybeToList $ listingsLanguage options
  doinlinecode classes

domintinline :: PandocMonad m => LP m Inlines
domintinline = do
  skipopts
  cls <- untokenize <$> braced
  doinlinecode [cls]

doinlinecode :: PandocMonad m => [Text] -> LP m Inlines
doinlinecode classes = do
  Tok _ Symbol t <- anySymbol
  marker <- case T.uncons t of
              Just (c, ts) | T.null ts -> return c
              _            -> mzero
  let stopchar = if marker == '{' then '}' else marker
  withVerbatimMode $
    (codeWith ("",classes,[]) . T.map nlToSpace . untokenize) <$>
      manyTill (verbTok stopchar) (symbol stopchar)

nlToSpace :: Char -> Char
nlToSpace '\n' = ' '
nlToSpace x    = x

keyval :: PandocMonad m => LP m (Text, Text)
keyval = try $ do
  Tok _ Word key <- satisfyTok isWordTok
  optional sp
  val <- option mempty $ do
           symbol '='
           optional sp
           (untokenize <$> braced) <|>
             (mconcat <$> many1 (
                 (untokenize . snd <$> withRaw braced)
                 <|>
                 (untokenize <$> (many1
                      (satisfyTok
                         (\t -> case t of
                                Tok _ Symbol "]" -> False
                                Tok _ Symbol "," -> False
                                Tok _ Symbol "{" -> False
                                Tok _ Symbol "}" -> False
                                _                -> True))))))
  optional (symbol ',')
  optional sp
  return (key, T.strip val)

keyvals :: PandocMonad m => LP m [(Text, Text)]
keyvals = try $ symbol '[' >> manyTill keyval (symbol ']')

accent :: PandocMonad m => Char -> Maybe Char -> LP m Inlines
accent combiningAccent fallBack = try $ do
  ils <- tok
  case toList ils of
       (Str (T.uncons -> Just (x, xs)) : ys) -> return $ fromList $
         -- try to normalize to the combined character:
         Str (Normalize.normalize Normalize.NFC
               (T.pack [x, combiningAccent]) <> xs) : ys
       [Space]           -> return $ str $ T.singleton $ fromMaybe combiningAccent fallBack
       []                -> return $ str $ T.singleton $ fromMaybe combiningAccent fallBack
       _                 -> return ils

mathDisplay :: Text -> Inlines
mathDisplay = displayMath . trimMath

mathInline :: Text -> Inlines
mathInline = math . trimMath

dollarsMath :: PandocMonad m => LP m Inlines
dollarsMath = do
  symbol '$'
  display <- option False (True <$ symbol '$')
  (do contents <- try $ untokenize <$> pDollarsMath 0
      if display
         then (mathDisplay contents <$ symbol '$')
         else return $ mathInline contents)
   <|> (guard display >> return (mathInline ""))

-- Int is number of embedded groupings
pDollarsMath :: PandocMonad m => Int -> LP m [Tok]
pDollarsMath n = do
  tk@(Tok _ toktype t) <- anyTok
  case toktype of
       Symbol | t == "$"
              , n == 0 -> return []
              | t == "\\" -> do
                  tk' <- anyTok
                  ((tk :) . (tk' :)) <$> pDollarsMath n
              | t == "{" -> (tk :) <$> pDollarsMath (n+1)
              | t == "}" ->
                if n > 0
                then (tk :) <$> pDollarsMath (n-1)
                else mzero
       _ -> (tk :) <$> pDollarsMath n

-- citations

addPrefix :: [Inline] -> [Citation] -> [Citation]
addPrefix p (k:ks) = k {citationPrefix = p ++ citationPrefix k} : ks
addPrefix _ _      = []

addSuffix :: [Inline] -> [Citation] -> [Citation]
addSuffix s ks@(_:_) =
  let k = last ks
  in  init ks ++ [k {citationSuffix = citationSuffix k ++ s}]
addSuffix _ _ = []

simpleCiteArgs :: PandocMonad m => LP m [Citation]
simpleCiteArgs = try $ do
  first  <- optionMaybe $ toList <$> opt
  second <- optionMaybe $ toList <$> opt
  keys <- try $ bgroup *> manyTill citationLabel egroup
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

citationLabel :: PandocMonad m => LP m Text
citationLabel  = do
  optional spaces
  untokenize <$>
    (many1 (satisfyTok isWordTok <|> symbolIn bibtexKeyChar)
          <* optional spaces
          <* optional (symbol ',')
          <* optional spaces)
  where bibtexKeyChar = ".:;?!`'()/*@_+=-[]" :: [Char]

cites :: PandocMonad m => CitationMode -> Bool -> LP m [Citation]
cites mode multi = try $ do
  cits <- if multi
             then do
               multiprenote <- optionMaybe $ toList <$> paropt
               multipostnote <- optionMaybe $ toList <$> paropt
               let (pre, suf) = case (multiprenote, multipostnote) of
                     (Just s , Nothing) -> (mempty, s)
                     (Nothing , Just t) -> (mempty, t)
                     (Just s , Just t ) -> (s, t)
                     _                  -> (mempty, mempty)
               tempCits <- many1 simpleCiteArgs
               case tempCits of
                 (k:ks) -> case ks of
                             (_:_) -> return $ ((addMprenote pre k):init ks) ++
                                                 [addMpostnote suf (last ks)]
                             _ -> return [addMprenote pre (addMpostnote suf k)]
                 _ -> return [[]]
             else count 1 simpleCiteArgs
  let cs = concat cits
  return $ case mode of
        AuthorInText -> case cs of
                             (c:rest) -> c {citationMode = mode} : rest
                             []       -> []
        _            -> map (\a -> a {citationMode = mode}) cs
  where mprenote (k:ks) = (k:ks) ++ [Space]
        mprenote _ = mempty
        mpostnote (k:ks) = [Str ",", Space] ++ (k:ks)
        mpostnote _ = mempty
        addMprenote mpn (k:ks) =
          let mpnfinal = case citationPrefix k of
                           (_:_) -> mprenote mpn
                           _ -> mpn
          in addPrefix mpnfinal (k:ks)
        addMprenote _ _ = []
        addMpostnote = addSuffix . mpostnote

citation :: PandocMonad m => Text -> CitationMode -> Bool -> LP m Inlines
citation name mode multi = do
  (c,raw) <- withRaw $ cites mode multi
  return $ cite c (rawInline "sile" $ "\\" <> name <> untokenize raw)

handleCitationPart :: Inlines -> [Citation]
handleCitationPart ils =
  let isCite Cite{} = True
      isCite _      = False
      (pref, rest) = break isCite (toList ils)
  in case rest of
          (Cite cs _:suff) -> addPrefix pref $ addSuffix suff cs
          _                -> []

complexNatbibCitation :: PandocMonad m => CitationMode -> LP m Inlines
complexNatbibCitation mode = try $ do
  (cs, raw) <-
    withRaw $ concat <$> do
      bgroup
      items <- mconcat <$>
                many1 (notFollowedBy (symbol ';') >> inline)
                  `sepBy1` (symbol ';')
      egroup
      return $ map handleCitationPart items
  case cs of
       []       -> mzero
       (c:cits) -> return $ cite (c{ citationMode = mode }:cits)
                      (rawInline "sile" $ "\\citetext" <> untokenize raw)

inNote :: Inlines -> Inlines
inNote ils =
  note $ para $ ils <> str "."

inlineCommand' :: PandocMonad m => LP m Inlines
inlineCommand' = try $ do
  Tok _ (CtrlSeq name) cmd <- anyControlSeq
  guard $ name /= "begin" && name /= "end"
  star <- option "" ("*" <$ symbol '*' <* optional sp)
  overlay <- option "" overlaySpecification
  let name' = name <> star <> overlay
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
          return $ str t

opt :: PandocMonad m => LP m Inlines
opt = bracketed inline <|> (str <$> rawopt)

paropt :: PandocMonad m => LP m Inlines
paropt = parenWrapped inline

rawopt :: PandocMonad m => LP m Text
rawopt = try $ do
  optional sp
  inner <- untokenize <$> bracketedToks
  optional sp
  return $ "[" <> inner <> "]"

skipopts :: PandocMonad m => LP m ()
skipopts = skipMany (void overlaySpecification <|> void rawopt)

-- opts in angle brackets are used in beamer
overlaySpecification :: PandocMonad m => LP m Text
overlaySpecification = try $ do
  symbol '<'
  t <- untokenize <$> manyTill overlayTok (symbol '>')
  -- see issue #3368
  guard $ not (T.all isLetter t) ||
          t `elem` ["beamer","presentation", "trans",
                    "handout","article", "second"]
  return $ "<" <> t <> ">"

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

unescapeURL :: Text -> Text
unescapeURL = T.concat . go . T.splitOn "\\"
  where
    isEscapable c = c `elemText` "#$%&~_^\\{}"
    go (x:xs) = x : map unescapeInterior xs
    go []     = []
    unescapeInterior t
      | Just (c, _) <- T.uncons t
      , isEscapable c = t
      | otherwise = "\\" <> t

mathEnvWith :: PandocMonad m
            => (Inlines -> a) -> Maybe Text -> Text -> LP m a
mathEnvWith f innerEnv name = f . mathDisplay . inner <$> mathEnv name
   where inner x = case innerEnv of
                        Nothing -> x
                        Just y  -> "\\begin{" <> y <> "}\n" <> x <>
                                   "\\end{" <> y <> "}"

mathEnv :: PandocMonad m => Text -> LP m Text
mathEnv name = do
  skipopts
  optional blankline
  res <- manyTill anyTok (end_ name)
  return $ stripTrailingNewlines $ untokenize res

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
  [ ("emph", extractSpaces emph <$> tok)
  , ("strike", extractSpaces emph <$> tok)
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
  ]

ifdim :: PandocMonad m => LP m Inlines
ifdim = do
  contents <- manyTill anyTok (controlSeq "fi")
  return $ rawInline "sile" $ "\\ifdim" <> untokenize contents <> "\\fi"

makeUppercase :: Inlines -> Inlines
makeUppercase = fromList . walk (alterStr T.toUpper) . toList

makeLowercase :: Inlines -> Inlines
makeLowercase = fromList . walk (alterStr T.toLower) . toList

alterStr :: (Text -> Text) -> Inline -> Inline
alterStr f (Str xs) = Str (f xs)
alterStr _ x = x


hyperlink :: PandocMonad m => LP m Inlines
hyperlink = try $ do
  src <- untokenize <$> braced
  lab <- tok
  return $ link ("#" <> src) "" lab

hypertargetBlock :: PandocMonad m => LP m Blocks
hypertargetBlock = try $ do
  ref <- untokenize <$> braced
  bs <- grouped block
  case toList bs of
       [Header 1 (ident,_,_) _] | ident == ref -> return bs
       _                        -> return $ divWith (ref, [], []) bs

hypertargetInline :: PandocMonad m => LP m Inlines
hypertargetInline = try $ do
  ref <- untokenize <$> braced
  ils <- grouped inline
  return $ spanWith (ref, [], []) ils

romanNumeralUpper :: (PandocMonad m) => LP m Inlines
romanNumeralUpper =
  str . toRomanNumeral <$> romanNumeralArg

romanNumeralLower :: (PandocMonad m) => LP m Inlines
romanNumeralLower =
  str . T.toLower . toRomanNumeral <$> romanNumeralArg

romanNumeralArg :: (PandocMonad m) => LP m Int
romanNumeralArg = spaces *> (parser <|> inBraces)
  where
    inBraces = do
      symbol '{'
      spaces
      res <- parser
      spaces
      symbol '}'
      return res
    parser = do
      Tok _ Word s <- satisfyTok isWordTok
      let (digits, rest) = T.span isDigit s
      unless (T.null rest) $
        Prelude.fail "Non-digits in argument to \\Rn or \\RN"
      safeRead digits

newToggle :: (Monoid a, PandocMonad m) => [Tok] -> LP m a
newToggle name = do
  updateState $ \st ->
    st{ sToggles = M.insert (untokenize name) False (sToggles st) }
  return mempty

setToggle :: (Monoid a, PandocMonad m) => Bool -> [Tok] -> LP m a
setToggle on name = do
  updateState $ \st ->
    st{ sToggles = M.adjust (const on) (untokenize name) (sToggles st) }
  return mempty

ifToggle :: PandocMonad m => LP m ()
ifToggle = do
  name <- braced
  spaces
  yes <- braced
  spaces
  no <- braced
  toggles <- sToggles <$> getState
  inp <- getInput
  let name' = untokenize name
  case M.lookup name' toggles of
                Just True  -> setInput (yes ++ inp)
                Just False -> setInput (no  ++ inp)
                Nothing    -> do
                  pos <- getPosition
                  report $ UndefinedToggle name' pos
  return ()

doTerm :: PandocMonad m => Translations.Term -> LP m Inlines
doTerm term = str <$> translateTerm term

ifstrequal :: (PandocMonad m, Monoid a) => LP m a
ifstrequal = do
  str1 <- tok
  str2 <- tok
  ifequal <- braced
  ifnotequal <- braced
  if str1 == str2
     then getInput >>= setInput . (ifequal ++)
     else getInput >>= setInput . (ifnotequal ++)
  return mempty

coloredInline :: PandocMonad m => Text -> LP m Inlines
coloredInline stylename = do
  skipopts
  color <- braced
  spanWith ("",[],[("style",stylename <> ": " <> untokenize color)]) <$> tok

ttfamily :: PandocMonad m => LP m Inlines
ttfamily = (code . stringify . toList) <$> tok

rawInlineOr :: PandocMonad m => Text -> LP m Inlines -> LP m Inlines
rawInlineOr name' fallback = do
  parseRaw <- extensionEnabled Ext_raw_tex <$> getOption readerExtensions
  if parseRaw
     then rawInline "sile" <$> getRawCommand name' ("\\" <> name')
     else fallback

processHBox :: Inlines -> Inlines
processHBox = walk convert
  where
    convert Space     = Str $ T.singleton $ chr 160 -- non-breakable space
    convert SoftBreak = Str $ T.singleton $ chr 160 -- non-breakable space
    convert LineBreak = Str ""
    convert x         = x

getRawCommand :: PandocMonad m => Text -> Text -> LP m Text
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
           "def" ->
             void $ manyTill anyTok braced
           _ | isFontSizeCommand name -> return ()
             | otherwise -> do
               skipopts
               option "" (try dimenarg)
               void $ many braced
  return $ txt <> untokenize rawargs

isFontSizeCommand :: Text -> Bool
isFontSizeCommand "tiny" = True
isFontSizeCommand "scriptsize" = True
isFontSizeCommand "footnotesize" = True
isFontSizeCommand "small" = True
isFontSizeCommand "normalsize" = True
isFontSizeCommand "large" = True
isFontSizeCommand "Large" = True
isFontSizeCommand "LARGE" = True
isFontSizeCommand "huge" = True
isFontSizeCommand "Huge" = True
isFontSizeCommand _ = False

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

dolabel :: PandocMonad m => LP m Inlines
dolabel = do
  v <- braced
  let refstr = untokenize v
  return $ spanWith (refstr,[],[("label", refstr)])
    $ inBrackets $ str $ untokenize v

doref :: PandocMonad m => Text -> LP m Inlines
doref cls = do
  v <- braced
  let refstr = untokenize v
  return $ linkWith ("",[],[ ("reference-type", cls)
                           , ("reference", refstr)])
                    ("#" <> refstr)
                    ""
                    (inBrackets $ str refstr)

lookupListDefault :: (Ord k) => v -> [k] -> M.Map k v -> v
lookupListDefault d = (fromMaybe d .) . lookupList
  where lookupList l m = msum $ map (`M.lookup` m) l

inline :: PandocMonad m => LP m Inlines
inline = (mempty <$ comment)
     <|> (space  <$ whitespace)
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
     <|> (str . T.singleton <$> primEscape)
     <|> regularSymbol
     <|> (do res <- symbolIn "#^'`\"[]"
             pos <- getPosition
             let s = untoken res
             report $ ParsingUnescaped s pos
             return $ str s)

inlines :: PandocMonad m => LP m Inlines
inlines = mconcat <$> many inline

-- block elements:

begin_ :: PandocMonad m => Text -> LP m ()
begin_ t = try (do
  controlSeq "begin"
  spaces
  txt <- untokenize <$> braced
  guard (t == txt)) <?> ("\\begin{" ++ T.unpack t ++ "}")

end_ :: PandocMonad m => Text -> LP m ()
end_ t = try (do
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


addMeta :: PandocMonad m => ToMetaValue a => Text -> a -> LP m ()
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

section :: PandocMonad m => Attr -> Int -> LP m Blocks
section (ident, classes, kvs) lvl = do
  skipopts
  contents <- grouped inline
  lab <- option ident $
          try (spaces >> controlSeq "label"
               >> spaces >> untokenize <$> braced)
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
  let parseRaw = extensionEnabled Ext_raw_sile exts
  rawOptions <- mconcat <$> many rawopt
  let beginCommand = "\\begin{" <> name <> "}" <> rawOptions
  pos1 <- getPosition
  (bs, raw) <- withRaw $ env name blocks
  if parseRaw
     then return $ rawBlock "sile"
                 $ beginCommand <> untokenize raw
     else do
       report $ SkippedContent beginCommand pos1
       pos2 <- getPosition
       report $ SkippedContent ("\\end{" <> name <> "}") pos2
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
  trace (T.take 60 $ tshow $ B.toList res)
  return res

blocks :: PandocMonad m => LP m Blocks
blocks = mconcat <$> many block
