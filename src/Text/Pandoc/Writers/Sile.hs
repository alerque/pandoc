{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{- |
   Module      : Text.Pandoc.Writers.Sile
   Copyright   : Copyright (C) 2015-2019 Caleb Maclennan
   License     : GNU GPL, version 2 or above

   Maintainer  : Caleb Maclennan <caleb@alerque.com>
   Stability   : alpha
   Portability : portable

Conversion of 'Pandoc' format into Sile.
-}
module Text.Pandoc.Writers.Sile (
    writeSile
  ) where
import Prelude
import Control.Applicative ((<|>))
import Control.Monad.State.Strict
import Data.Monoid (Any(..))
import Data.Char (isAlphaNum, isAscii, isDigit, isLetter, isSpace,
                  isPunctuation, ord)
import Data.List (foldl', intersperse, nubBy, (\\), uncons )
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe, isNothing)
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Network.URI (unEscapeString)
import Text.DocTemplates (FromContext(lookupContext), renderTemplate,
                          Val(..), Context(..))
import Text.Pandoc.Class (PandocMonad, report, toLang)
import Text.Pandoc.Definition
import Text.Pandoc.ImageSize
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.DocLayout
import Text.Pandoc.Shared
import Text.DocTemplates (Val(..), Context(..))
import Text.Pandoc.Walk
import Text.Pandoc.Writers.Shared
import Text.Printf (printf)

data WriterState =
  WriterState {
                stInQuote       :: Bool          -- true if in a blockquote
              , stInHeading     :: Bool          -- true if in a section heading
              , stInItem        :: Bool          -- true if in \item[..]
              , stOLLevel       :: Int           -- level of ordered list nesting
              , stOptions       :: WriterOptions -- writer options, so they don't have to be parameter
              , stTable         :: Bool          -- true if document has a table
              , stStrikeout     :: Bool          -- true if document has strikeout
              , stUrl           :: Bool          -- true if document has visible URL link
              , stGraphics      :: Bool          -- true if document contains images
              , stLHS           :: Bool          -- true if document has literate haskell code
              , stBook          :: Bool          -- true if document uses book class
              , stInternalLinks :: [Text]      -- list of internal link targets
              , stEmptyLine     :: Bool          -- true if no content on line
              }

startingState :: WriterOptions -> WriterState
startingState options = WriterState {
                  stInQuote = False
                , stInHeading = False
                , stInItem = False
                , stOLLevel = 1
                , stOptions = options
                , stTable = False
                , stStrikeout = False
                , stUrl = False
                , stGraphics = False
                , stLHS = False
                , stBook = case writerTopLevelDivision options of
                                TopLevelPart    -> True
                                TopLevelChapter -> True
                                _               -> False
                , stInternalLinks = []
                , stEmptyLine = True }

-- | Convert Pandoc to Sile.
writeSile :: PandocMonad m => WriterOptions -> Pandoc -> m Text
writeSile options document =
  evalStateT (pandocToSile options document) $
    startingState options

type LW m = StateT WriterState m

pandocToSile :: PandocMonad m
              => WriterOptions -> Pandoc -> LW m Text
pandocToSile options (Pandoc meta blocks) = do
  let blocks' = blocks
  -- see if there are internal links
  let isInternalLink (Link _ _ (s,_))
        | Just ('#', xs) <- T.uncons s = [xs]
      isInternalLink _                     = []
  modify $ \s -> s{ stInternalLinks = query isInternalLink blocks' }
  -- set stBook depending on documentclass
  let colwidth = if writerWrapText options == WrapAuto
                    then Just $ writerColumns options
                    else Nothing
  metadata <- metaToContext options
              blockListToSile
              (fmap chomp . inlineListToSile)
              meta
  let documentClass =
        case lookupContext "documentclass" (writerVariables options) `mplus`
              (stringify <$> lookupMeta "documentclass" meta) of
                 Just x -> x
  let (blocks'', lastHeader) = if writerCiteMethod options == Citeproc then
                                 (blocks', [])
                               else case reverse blocks' of
                                 Header 1 _ il : _ -> (init blocks', il)
                                 _             -> (blocks', [])
  main <- blockListToSile blocks''
  st <- get
  titleMeta <- stringToSile TextString $ stringify $ docTitle meta
  authorsMeta <- mapM (stringToSile TextString . stringify) $ docAuthors meta
  let hasStringValue x = isJust (getField x metadata :: Maybe (Doc Text))
  let geometryFromMargins = mconcat $ intersperse ("," :: Doc Text) $
                            mapMaybe (\(x,y) ->
                                ((x <> "=") <>) <$> getField y metadata)
                              [("lmargin","margin-left")
                              ,("rmargin","margin-right")
                              ,("tmargin","margin-top")
                              ,("bmargin","margin-bottom")
                              ]

  let context  =  defField "toc" (writerTableOfContents options) $
                  defField "toc-depth" (tshow
                                        (writerTOCDepth options -
                                              if stBook st
                                                 then 1
                                                 else 0)) $
                  defField "body" main $
                  defField "title-meta" titleMeta $
                  defField "author-meta"
                        (T.intercalate "; " authorsMeta) $
                  defField "documentclass" documentClass $
                  defField "tables" (stTable st) $
                  defField "strikeout" (stStrikeout st) $
                  defField "url" (stUrl st) $
                  defField "numbersections" (writerNumberSections options) $
                  defField "lhs" (stLHS st) $
                  defField "graphics" (stGraphics st) $
                  defField "colorlinks" (any hasStringValue
                           ["citecolor", "urlcolor", "linkcolor", "toccolor",
                            "filecolor"]) $
                  defField "section-titles" True $
                  defField "geometry" geometryFromMargins $
                  (case T.uncons . render Nothing <$>
                        getField "papersize" metadata of
                        -- uppercase a4, a5, etc.
                      Just (Just ('A', ds))
                        | not (T.null ds) && T.all isDigit ds
                          -> resetField "papersize" ("a" <> ds)
                      _   -> id)
                  metadata
  return $ render colwidth $
    case writerTemplate options of
        Nothing  -> main
        Just tpl -> renderTemplate tpl context

data StringContext = TextString
                   | URLString
                   | CodeString
                   deriving (Eq)

-- escape things as needed for Sile
stringToSile :: PandocMonad m => StringContext -> Text -> LW m Text
stringToSile  context zs = do
  opts <- gets stOptions
  return $ T.pack $
    foldr (go opts context) mempty $ T.unpack $ zs
 where
  go :: WriterOptions -> StringContext -> Char -> String -> String
  go opts ctx x xs   =
    let isUrl = ctx == URLString
        emits s = s <> xs
        emitc c = c : xs
    in case x of
         '{' -> emits "\\{"
         '}' -> emits "\\}"
         '%' -> emits "\\%"
         '\\'| isUrl     -> emitc '/' -- NB. / works as path sep even on Windows
             | otherwise -> emits "\\"
         _ -> emitc x

toLabel :: PandocMonad m => Text -> LW m Text
toLabel z = go `fmap` stringToSile URLString z
 where
   go = T.concatMap $ \x -> case x of
     _ | (isLetter x || isDigit x) && isAscii x -> T.singleton x
       | x `elemText` "_-+=:;." -> T.singleton x
       | otherwise -> T.pack $ "ux" <> printf "%x" (ord x)

-- | Puts contents into Sile command.
inCmd :: Text -> Doc Text -> Doc Text
inCmd cmd contents = char '\\' <> literal cmd <> braces contents

inArgCmd :: Text -> [String] -> Doc Text -> Doc Text
inArgCmd cmd args contents = do
  let args' = if null args
                 then ""
                 else brackets $ hcat (intersperse "," (map text args))
  char '\\' <> literal cmd <> args' <> braces contents

inBlockCmd :: Text -> [String] -> Doc Text -> Doc Text
inBlockCmd cmd args contents = do
  let args' = if null args
                 then ""
                 else brackets $ hcat (intersperse "," (map text args))
      cmd' = braces (literal cmd)
  "\\begin" <> args' <> cmd' $$ contents $$ "\\end" <> cmd'

isLineBreakOrSpace :: Inline -> Bool
isLineBreakOrSpace LineBreak = True
isLineBreakOrSpace SoftBreak = True
isLineBreakOrSpace Space     = True
isLineBreakOrSpace _         = False

-- | Convert Pandoc block element to Sile.
blockToSile :: PandocMonad m
             => Block     -- ^ Block to convert
             -> LW m (Doc Text)
blockToSile Null = return empty
blockToSile (Div (id,classes,kvs) bs) = do
  ref <- toLabel id
  lang <- toLang $ lookup "lang" kvs
  let linkAnchor = if null id
                      then empty
                      else "\\pdf:link" <> braces (literal ref)
  let classes' = [ val | (val) <- classes ]
  let classes'' = intercalate "," classes'
  let params = (if id == ""
                  then []
                  else [ "id=" ++ ref ]) ++
               (if null classes'
                  then []
                  else [ "classes=\"" ++ classes'' ++ "\"" ] ) ++
                (if null kvs
                  then []
                  else [ key ++ "=" ++ attr | (key, attr) <- kvs ])
  contents <- blockListToSile bs
  return $ inBlockCmd "Div" params (linkAnchor $$ contents)
blockToSile (Plain lst) =
  inlineListToSile $ dropWhile isLineBreakOrSpace lst
blockToSile (Para [Str ".",Space,Str ".",Space,Str "."]) = do
  inlineListToSile [Str ".",Space,Str ".",Space,Str "."]
blockToSile (Para lst) =
  inlineListToSile $ dropWhile isLineBreakOrSpace lst
blockToSile (LineBlock lns) =
  blockToSile $ linesToPara lns
blockToSile (BlockQuote lst) = do
  case lst of
       _ -> do
         oldInQuote <- gets stInQuote
         modify (\s -> s{stInQuote = True})
         contents <- blockListToSile lst
         modify (\s -> s{stInQuote = oldInQuote})
         return $ "\\begin{quote}" $$ contents $$ "\\end{quote}"
blockToSile (CodeBlock (identifier,classes,kvs) str) = do
  opts <- gets stOptions
  ref <- toLabel identifier
  str' <- stringToSile CodeString str
  let classes' = [ val | (val) <- classes ]
  let classes'' = intercalate "," classes'
  let params = (if identifier == ""
                  then []
                  else [ "id=" ++ ref ]) ++
               (if null classes
                  then []
                  else [ "classes=\"" ++ classes'' ++ "\"" ] ) ++
                (if null kvs
                  then []
                  else [ key ++ "=" ++ attr | (key, attr) <- kvs ])
      sileParams
          | null params = empty
          | otherwise = brackets $ hcat (intersperse "," (map literal params))
  let linkAnchor = if null identifier
                      then empty
                      else "\\pdf:link" <> brackets (literal ref) <> braces (literal ref)
  let lhsCodeBlock = do
        modify $ \s -> s{ stLHS = True }
        return $ flush (linkAnchor $$ "\\begin{code}" $$ literal str $$
                            "\\end{code}") $$ cr
  let rawCodeBlock = do
        env <- return "verbatim"
        return $ flush (linkAnchor $$ literal ("\\begin{" ++ env ++ "}") $$
                 literal str $$ literal ("\\end{" ++ env ++ "}")) <> cr

  case () of
     _ | isEnabled Ext_literate_haskell opts && "haskell" `elem` classes &&
         "literate" `elem` classes           -> lhsCodeBlock
       | otherwise                           -> rawCodeBlock
blockToSile b@(RawBlock f x)
  | f == Format "sile" || f == Format "sil"
                        = return $ literal x
  | otherwise           = do
      report $ BlockNotRendered b
      return empty
blockToSile (BulletList []) = return empty  -- otherwise sile error
blockToSile (BulletList lst) = do
  items <- mapM listItemToSile lst
  return $ literal ("\\begin{listarea}") $$ vcat items $$
             "\\end{listarea}"
blockToSile (OrderedList _ []) = return empty -- otherwise error
blockToSile (OrderedList (_, numstyle, _) lst) = do
  st <- get
  let oldlevel = stOLLevel st
  put $ st {stOLLevel = oldlevel + 1}
  items <- mapM listItemToSile lst
  modify (\s -> s {stOLLevel = oldlevel})
  let tostyle = "numberstyle=" ++ case numstyle of
                       Decimal      -> "arabic"
                       UpperRoman   -> "Roman"
                       LowerRoman   -> "roman"
                       UpperAlpha   -> "Alpha"
                       LowerAlpha   -> "alpha"
                       Example      -> "arabic"
                       DefaultStyle -> "arabic"
  return $ literal ("\\begin[" ++ tostyle ++ "]{listarea}")
         $$ vcat items
         $$ "\\end{listarea}"
blockToSile (DefinitionList []) = return empty
blockToSile (DefinitionList lst) = do
  items <- mapM defListItemToSile lst
  let spacing = if all isTightList (map snd lst)
                   then text "tight=true,definition=true"
                   else text "tight=false,definition=true"
  return $ "\\begin" <> brackets spacing <> braces "listarea"
         $$ vcat items
         $$ "\\end" <> braces "listarea"
blockToSile HorizontalRule = return $
  "\\HorizontalRule"
blockToSile (Header level (id',classes,_) lst) = do
  modify $ \s -> s{stInHeading = True}
  hdr <- sectionHeader ("unnumbered" `elem` classes) id' level lst
  modify $ \s -> s{stInHeading = False}
  return hdr
blockToSile (Table caption aligns widths heads rows) = do
  headers <- if all null heads
                then return empty
                else do
                    contents <- (tableRowToSile True aligns widths) heads
                    return ("\\toprule" $$ contents $$ "\\midrule")
  let endhead = if all null heads
                   then empty
                   else text "\\endhead"
  let endfirsthead = if all null heads
                       then empty
                       else text "\\endfirsthead"
  captionText <- inlineListToSile caption
  let capt = if isEmpty captionText
                then empty
                else "\\caption" <> braces captionText
                         <> "\\tabularnewline"
                         $$ headers
                         $$ endfirsthead
  rows' <- mapM (tableRowToSile False aligns widths) rows
  let colDescriptors = literal $ T.concat $ map toColDescriptor aligns
  modify $ \s -> s{ stTable = True }
  return $ "\\begin{longtable}[]" <>
              braces ("@{}" <> colDescriptors <> "@{}")
              -- the @{} removes extra space at beginning and end
         $$ capt
         $$ firsthead
         $$ head'
         $$ "\\endhead"
         $$ vcat rows'
         $$ "\\bottomrule"
         $$ "\\end{longtable}"

toColDescriptor :: Alignment -> Text
toColDescriptor align =
  case align of
         AlignLeft    -> "l"
         AlignRight   -> "r"
         AlignCenter  -> "c"
         AlignDefault -> "l"

blockListToSile :: PandocMonad m => [Block] -> LW m (Doc Text)
blockListToSile lst =
  vsep `fmap` mapM (\b -> setEmptyLine True >> blockToSile b) lst

tableRowToSile :: PandocMonad m
                => Bool
                -> [Alignment]
                -> [Double]
                -> [[Block]]
                -> LW m (Doc Text)
tableRowToSile header aligns widths cols = do
  -- scale factor compensates for extra space between columns
  -- so the whole table isn't larger than columnwidth
  let scaleFactor = 0.97 ** fromIntegral (length aligns)
  let widths' = map (scaleFactor *) widths
  cells <- mapM (tableCellToSile header) $ zip3 widths' aligns cols
  return $ hsep (intersperse "&" cells) <> "\\tabularnewline"

-- we need to go to some lengths to get line breaks working:
-- as LineBreak bs = \vtop{\hbox{\strut as}\hbox{\strut bs}}.
fixLineBreaks :: Block -> Block
fixLineBreaks (Para ils)  = Para $ fixLineBreaks' ils
fixLineBreaks (Plain ils) = Plain $ fixLineBreaks' ils
fixLineBreaks x           = x

fixLineBreaks' :: [Inline] -> [Inline]
fixLineBreaks' ils = case splitBy (== LineBreak) ils of
                       []     -> []
                       [xs]   -> xs
                       chunks -> RawInline "sile" "\\vtop{" :
                                 concatMap tohbox chunks ++
                                 [RawInline "sile" "}"]
  where tohbox ys = RawInline "sile" "\\hbox{\\strut " : ys ++
                    [RawInline "sile" "}"]

-- We also change display math to inline math, since display
-- math breaks in simple tables.
displayMathToInline :: Inline -> Inline
displayMathToInline (Math DisplayMath x) = Math InlineMath x
displayMathToInline x                    = x

tableCellToSile :: PandocMonad m => Bool -> (Double, Alignment, [Block])
                 -> LW m (Doc Text)
tableCellToSile _      (0,     _,     blocks) =
  blockListToSile $ walk fixLineBreaks $ walk displayMathToInline blocks
tableCellToSile header (width, align, blocks) = do
  cellContents <- blockListToSile blocks
  let valign = text $ if header then "[b]" else "[t]"
  let halign = case align of
               AlignLeft    -> "\\raggedright"
               AlignRight   -> "\\raggedleft"
               AlignCenter  -> "\\centering"
               AlignDefault -> "\\raggedright"
  return $ ("\\begin{minipage}" <> valign <>
            braces (text (printf "%.2f\\columnwidth" width)) <>
            (halign <> "\\strut" <> cr <> cellContents <> cr) <>
            "\\strut\\end{minipage}")


listItemToSile :: PandocMonad m => [Block] -> LW m (Doc Text)
listItemToSile lst = do
  blockListToSile lst >>= return . (inCmd "listitem")

defListItemToSile :: PandocMonad m => ([Inline], [[Block]]) -> LW m (Doc Text)
defListItemToSile (term, defs) = do
    term' <- inlineListToSile term
    def'  <- liftM vsep $ mapM blockListToSile defs
    return $ case defs of
     (((Header _ _ _) : _) : _) ->
       "\\listitem" <> braces term' <> " ~ " $$ def'
     _                          ->
       "\\listitem" <> braces term' $$ def'

-- | Craft the section header, inserting the secton reference, if supplied.
sectionHeader :: PandocMonad m
              => Bool    -- True for unnumbered
              -> [Char]
              -> Int
              -> [Inline]
              -> LW m (Doc Text)
sectionHeader unnumbered ident level lst = do
  txt <- inlineListToSile lst
  let removeInvalidInline (Note _)             = []
      removeInvalidInline (Span (id', _, _) _) | not (null id') = []
      removeInvalidInline Image{}            = []
      removeInvalidInline x                    = [x]
  let lstNoNotes = foldr (mappend . (\x -> walkM removeInvalidInline x)) mempty lst
  book <- gets stBook
  opts <- gets stOptions
  let topLevelDivision = if writerTopLevelDivision opts == TopLevelDefault
                         then TopLevelChapter
                         else writerTopLevelDivision opts
  let level' = case topLevelDivision of
                      TopLevelPart    -> level - 2
                      TopLevelChapter -> level - 1
                      TopLevelSection -> level
                      TopLevelDefault -> level
  let sectionType = case level' of
                          -1 -> "part"
                          0  -> "chapter"
                          1  -> "section"
                          2  -> "subsection"
                          3  -> "subsubsection"
                          4  -> "paragraph"
                          5  -> "subparagraph"
                          _  -> ""
  lab <- labelFor ident
  return $ if level' > 5
              then txt
              else text ('\\':sectionType) <> braces txt


labelFor :: PandocMonad m => Text -> LW m (Doc Text)
labelFor ""    = return empty
labelFor ident = do
  ref <- literal `fmap` toLabel ident
  return $ text "\\label" <> braces ref

-- | Convert list of inline elements to Sile.
inlineListToSile :: PandocMonad m
                  => [Inline]  -- ^ Inlines to convert
                  -> LW m (Doc Text)
inlineListToSile lst = hcat <$>
  mapM inlineToSile (fixLineInitialSpaces $ lst)
    -- nonbreaking spaces (~) in Sile don't work after line breaks,
    -- so we turn nbsps after hard breaks to \hspace commands.
    -- this is mostly used in verse.
 where fixLineInitialSpaces [] = []
       fixLineInitialSpaces (LineBreak : Str s : xs)
         | Just ('\160', _) <- T.uncons s
         = LineBreak : fixNbsps s <> fixLineInitialSpaces xs
       fixLineInitialSpaces (x:xs) = x : fixLineInitialSpaces xs
       fixNbsps s = let (ys,zs) = T.span (=='\160') s
                    in  replicate (T.length ys) hspace <> [Str zs]
       hspace = RawInline "sile" "\\kern[width=1spc]"

-- | Convert inline element to Sile
inlineToSile :: PandocMonad m
              => Inline    -- ^ Inline to convert
              -> LW m (Doc Text)
inlineToSile (Span (id',classes,kvs) ils) = do
  ref <- toLabel id'
  lang <- toLang $ lookup "lang" kvs
  let classToCommand = [ "csl-no-emph", "csl-no-strong", "csl-no-smallcaps" ]
  let commands = filter (`elem` classToCommand) classes
  let classes' = filter (`notElem` classToCommand) classes
  contents <- inlineListToSile ils
  let classes' = filter (`notElem` [ "csl-no-emph", "csl-no-strong", "csl-no-smallcaps"]) classes
  let classes'' = [ val | (val) <- classes' ]
  let classes''' = intercalate "," classes''
  let params = (if id' == ""
                  then []
                  else [ "id=" <> ref ]) <>
               (if null classes'
                  then []
                  else [ "classes=\"" <> classes''' <> "\"" ] ) <>
                (if null kvs
                  then []
                  else [ key <> "=" <> attr | (key, attr) <- kvs ])
  return $ if null commands
              then if null params
                      then braces contents
                      else inArgCmd "Span" params contents
              else if null params
                      then foldr inCmd contents commands
                      else inArgCmd "Span" params $ foldr inCmd contents commands
inlineToSile (Emph lst) = inCmd "Emph" <$> inlineListToSile lst
inlineToSile (Strong lst) = inCmd "Strong" <$> inlineListToSile lst
inlineToSile (Strikeout lst) = inCmd "Strikeout" <$> inlineListToSile lst
inlineToSile (Superscript lst) = inCmd "Superscript" <$> inlineListToSile lst
inlineToSile (Subscript lst) = inCmd "Subscript" <$> inlineListToSile lst
inlineToSile (SmallCaps lst) = inCmd "SmallCaps" <$> inlineListToSile lst
inlineToSile (Cite cits lst) = do
  st <- get
  let opts = stOptions st
  case writerCiteMethod opts of
     Natbib   -> citationsToNatbib cits
     _        -> inlineListToSile lst

inlineToSile (Code (_,_,_) str) =
  return $ "\\code{" <> text str <> "}"
inlineToSile (Quoted SingleQuote lst) = do
  opts <- gets stOptions
  contents <- inlineListToSile lst
  return $ if isEnabled Ext_smart opts
              then "‘" <> contents <> "’"
              else "'" <> contents <> "'"
inlineToSile (Quoted DoubleQuote lst) = do
  opts <- gets stOptions
  contents <- inlineListToSile lst
  return $ if isEnabled Ext_smart opts
              then "“" <> contents <> "”"
              else "\"" <> contents <> "\""
inlineToSile (Str str) = liftM text $ stringToSile TextString str
inlineToSile (Math InlineMath str) =
  return $ "\\(" <> text str <> "\\)"
inlineToSile (Math DisplayMath str) = do
  setEmptyLine False
  return $ "\\[" <> text str <> "\\]"
inlineToSile  il@(RawInline f str) = do
  setEmptyLine False
  return $ text str
inlineToSile LineBreak = return $ "\\hfill\\break" <> cr
inlineToSile SoftBreak = do
  wrapText <- gets (writerWrapText . stOptions)
  case wrapText of
       WrapAuto     -> return space
       WrapNone     -> return space
       WrapPreserve -> return cr
inlineToSile Space = return space
inlineToSile (Link _ txt (src,_))
  | Just ('#', ident) <- T.uncons src
  = do
      contents <- inlineListToSile txt
      lab <- toLabel ident
      return $ text "\\pdf:link" <> brackets ("dest=" <> literal lab) <> braces contents
  | otherwise =
  case txt of
        [Str x] | unEscapeString (T.unpack x) == unEscapeString (T.unpack src) ->  -- autolink
             do modify $ \s -> s{ stUrl = True }
                src' <- stringToSile URLString (escapeURI src)
                return $ literal $ "\\url{" <> src' <> "}"
        [Str x] | Just rest <- T.stripPrefix "mailto:" src,
                  unEscapeString (T.unpack x) == unEscapeString (T.unpack rest) -> -- email autolink
             do modify $ \s -> s{ stUrl = True }
                src' <- stringToSile URLString (escapeURI src)
                contents <- inlineListToSile txt
                return $ "\\href" <> braces (literal src') <>
                   braces ("\\url" <> braces contents)
        _ -> do contents <- inlineListToSile txt
                src' <- stringToSile URLString (escapeURI src)
                return $ literal ("\\href{" <> src' <> "}{") <> contents <> char '}'
                -- let params = (["src=\"" <> literal src' <> "\""]) <>
                --               (if null tit
                --                 then []
                --                 else [ "title=\"" ++ tit ++ "\"" ]) <>
                --               (if null kvs
                --                   then []
                --                   else [ key ++ "=\"" ++ val ++ "\"" | (key, val) <- kvs ])
                --     linkattrs
                --       | null params = empty
                --       | otherwise = brackets $ hcat (intersperse "," (map text params))
                -- return $ literal ("\\href" <> linkattrs <> braces contents)
inlineToSile il@(Image _ _ (src, _))
  | Just _ <- T.stripPrefix "data:" src = do
  report $ InlineNotRendered il
  return empty
inlineToSile (Image _ _ (source, _)) = do
  setEmptyLine False
  modify $ \s -> s{ stGraphics = True }
  let source' = if isURI source
                   then source
                   else T.pack $ unEscapeString $ T.unpack source
  source'' <- stringToSile URLString source'
  return $ "\\img" <> brackets ("src=" <> literal source'')
inlineToSile (Note contents) = do
  setEmptyLine False
  contents' <- blockListToSile contents
  let optnl = case reverse contents of
                   (CodeBlock _ _ : _) -> cr
                   _                   -> empty
  let noteContents = nest 2 contents' <> optnl
  return $ "\\footnote" <> braces noteContents

setEmptyLine :: PandocMonad m => Bool -> LW m ()
setEmptyLine b = modify $ \st -> st{ stEmptyLine = b }

citationsToNatbib :: PandocMonad m => [Citation] -> LW m (Doc Text)
citationsToNatbib
            [one]
  = citeCommand c p s k
  where
    Citation { citationId = k
             , citationPrefix = p
             , citationSuffix = s
             , citationMode = m
             }
      = one
    c = case m of
             AuthorInText   -> "citet"
             SuppressAuthor -> "citeyearpar"
             NormalCitation -> "citep"

citationsToNatbib cits
  | noPrefix (tail cits) && noSuffix (init cits) && ismode NormalCitation cits
  = citeCommand "citep" p s ks
  where
     noPrefix  = all (null . citationPrefix)
     noSuffix  = all (null . citationSuffix)
     ismode m  = all ((==) m  . citationMode)
     p         = citationPrefix  $
                 head cits
     s         = citationSuffix  $
                 last cits
     ks        = T.intercalate ", " $ map citationId cits

citationsToNatbib (c:cs) | citationMode c == AuthorInText = do
     author <- citeCommand "citeauthor" [] [] (citationId c)
     cits   <- citationsToNatbib (c { citationMode = SuppressAuthor } : cs)
     return $ author <+> cits

citationsToNatbib cits = do
  cits' <- mapM convertOne cits
  return $ text "\\citetext{" <> foldl' combineTwo empty cits' <> text "}"
  where
    combineTwo a b | isEmpty a = b
                   | otherwise = a <> text "; " <> b
    convertOne Citation { citationId = k
                        , citationPrefix = p
                        , citationSuffix = s
                        , citationMode = m
                        }
        = case m of
               AuthorInText   -> citeCommand "citealt"  p s k
               SuppressAuthor -> citeCommand "citeyear" p s k
               NormalCitation -> citeCommand "citealp"  p s k

citeCommand :: PandocMonad m
            => Text -> [Inline] -> [Inline] -> Text -> LW m (Doc Text)
citeCommand c p s k = do
  args <- citeArguments p s k
  return $ literal ("\\" <> c) <> args

citeArguments :: PandocMonad m
              => [Inline] -> [Inline] -> Text -> LW m (Doc Text)
citeArguments p s k = do
  let s' = stripLocatorBraces $ case s of
        (Str t : r) -> case T.uncons t of
          Just (x, xs)
            | T.null xs
            , isPunctuation x -> dropWhile (== Space) r
            | isPunctuation x -> Str xs : r
          _ -> s
        _                -> s
  pdoc <- inlineListToSile p
  sdoc <- inlineListToSile s'
  let optargs = case (isEmpty pdoc, isEmpty sdoc) of
                     (True, True ) -> empty
                     (True, False) -> brackets sdoc
                     (_   , _    ) -> brackets pdoc <> brackets sdoc
  return $ optargs <> braces (literal k)

-- strip off {} used to define locator in pandoc-citeproc; see #5722
stripLocatorBraces :: [Inline] -> [Inline]
stripLocatorBraces = walk go
  where go (Str xs) = Str $ T.filter (\c -> c /= '{' && c /= '}') xs
        go x        = x

