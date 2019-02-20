{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
   Module      : Text.Pandoc.Writers.Sile
   Copyright   : Copyright (C) 2015-2018 Caleb Maclennan
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
import Data.Char (isAscii, isDigit, isLetter, isPunctuation, ord)
import Data.List (foldl', intercalate, intersperse, stripPrefix, )
import Data.Maybe (catMaybes, isJust)
import Data.Text (Text)
import Network.URI (unEscapeString)
import Text.Pandoc.Class (PandocMonad, report)
import Text.Pandoc.Definition
import Text.Pandoc.ImageSize
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.Pandoc.Pretty
import Text.Pandoc.Shared
import Text.Pandoc.Templates
import Text.Pandoc.Walk
import Text.Pandoc.Writers.Shared
import qualified Text.Parsec as P
import Text.Printf (printf)
-- import qualified Data.Text.Normalize as Normalize

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
              , stInternalLinks :: [String]      -- list of internal link targets
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
  -- Strip off final 'references' header if --natbib or --biblatex
  let method = writerCiteMethod options
  let blocks' = if method == Biblatex || method == Natbib
                   then case reverse blocks of
                             (Div (_,["references"],_) _):xs -> reverse xs
                             _                               -> blocks
                   else blocks
  -- see if there are internal links
  let isInternalLink (Link _ _ ('#':xs,_)) = [xs]
      isInternalLink _                     = []
  modify $ \s -> s{ stInternalLinks = query isInternalLink blocks' }
  let template = maybe "" id $ writerTemplate options
  -- set stBook depending on documentclass
  let colwidth = if writerWrapText options == WrapAuto
                    then Just $ writerColumns options
                    else Nothing
  let render' :: Doc -> Text
      render' = render colwidth
  metadata <- metaToJSON options
              (fmap render' . blockListToSile)
              (fmap render' . inlineListToSile)
              meta
  let bookClasses = ["book", "bible"]
  let documentClass = case P.parse pDocumentClass "template" template of
                              Right r -> r
                              Left _  -> ""
  case lookup "documentclass" (writerVariables options) `mplus`
        fmap stringify (lookupMeta "documentclass" meta) of
         Just x  | x `elem` bookClasses -> modify $ \s -> s{stBook = True}
                 | otherwise            -> return ()
         Nothing | documentClass `elem` bookClasses
                                        -> modify $ \s -> s{stBook = True}
                 | otherwise               -> return ()
  let (blocks'', lastHeader) = if writerCiteMethod options == Citeproc then
                                 (blocks', [])
                               else case last blocks' of
                                 Header 1 _ il -> (init blocks', il)
                                 _             -> (blocks', [])
  blocks''' <- return blocks''
  body <- mapM (elementToSile options) $ hierarchicalize blocks'''
  (biblioTitle :: String) <- liftM (render colwidth) $ inlineListToSile lastHeader
  let main = render' $ vsep body
  st <- get
  titleMeta <- stringToSile TextString $ stringify $ docTitle meta
  authorsMeta <- mapM (stringToSile TextString . stringify) $ docAuthors meta
  let hasStringValue x = isJust (getField x metadata :: Maybe String)
  let geometryFromMargins = intercalate [','] $ catMaybes $
                              map (\(x,y) ->
                                ((x ++ "=") ++) <$> getField y metadata)
                              [("lmargin","margin-left")
                              ,("rmargin","margin-right")
                              ,("tmargin","margin-top")
                              ,("bmargin","margin-bottom")
                              ]

  let context  =  defField "toc" (writerTableOfContents options) $
                  defField "toc-depth" (show (writerTOCDepth options -
                                              if stBook st
                                                 then 1
                                                 else 0)) $
                  defField "body" main $
                  defField "title-meta" titleMeta $
                  defField "author-meta" (intercalate "; " authorsMeta) $
                  defField "documentclass" (if stBook st
                                               then ("book" :: String)
                                               else ("plain" :: String)) $
                  defField "tables" (stTable st) $
                  defField "strikeout" (stStrikeout st) $
                  defField "url" (stUrl st) $
                  defField "numbersections" (writerNumberSections options) $
                  defField "lhs" (stLHS st) $
                  defField "graphics" (stGraphics st) $
                  defField "book-class" (stBook st) $
                  (case writerCiteMethod options of
                         Natbib   -> defField "biblio-title" biblioTitle .
                                     defField "natbib" True
                         Biblatex -> defField "biblio-title" biblioTitle .
                                     defField "biblatex" True
                         _        -> id) $
                  defField "colorlinks" (any hasStringValue
                           ["citecolor", "urlcolor", "linkcolor", "toccolor"]) $
                  defField "section-titles" True $
                  defField "geometry" geometryFromMargins $
                  (case getField "papersize" metadata of
                        Just ("A4" :: String) -> resetField "papersize"
                                                    ("a4" :: String)
                        _                     -> id) $
                  metadata
  case writerTemplate options of
       Nothing  -> return main
       Just tpl -> renderTemplate' tpl context

-- | Convert Elements to Sile
elementToSile :: PandocMonad m => WriterOptions -> Element -> LW m Doc
elementToSile _ (Blk block) = blockToSile block
elementToSile opts (Sec level _ (id',classes,_) title' elements) = do
  modify $ \s -> s{stInHeading = True}
  header' <- sectionHeader ("unnumbered" `elem` classes) id' level title'
  modify $ \s -> s{stInHeading = False}
  innerContents <- mapM (elementToSile opts) elements
  return $ vsep (header' : innerContents)

data StringContext = TextString
                   | URLString
                   | CodeString
                   deriving (Eq)

-- escape things as needed for Sile
stringToSile :: PandocMonad m => StringContext -> String -> LW m String
stringToSile  _     []     = return ""
stringToSile  ctx (x:xs) = do
  rest <- stringToSile ctx xs
  let isUrl = ctx == URLString
  return $
    case x of
       '{' -> "\\{" ++ rest
       '}' -> "\\}" ++ rest
       '%' -> "\\%" ++ rest
       '\\'| isUrl     -> '/' : rest  -- NB. / works as path sep even on Windows
           | otherwise -> "\\\\" ++ rest
       _        -> x : rest

toLabel :: PandocMonad m => String -> LW m String
toLabel z = go `fmap` stringToSile URLString z
 where go [] = ""
       go (x:xs)
         | (isLetter x || isDigit x) && isAscii x = x:go xs
         | x `elem` ("_-+=:;." :: String) = x:go xs
         | otherwise = "ux" ++ printf "%x" (ord x) ++ go xs

-- | Puts contents into Sile command.
inCmd :: String -> Doc -> Doc
inCmd cmd contents = char '\\' <> text cmd <> braces contents


isLineBreakOrSpace :: Inline -> Bool
isLineBreakOrSpace LineBreak = True
isLineBreakOrSpace SoftBreak = True
isLineBreakOrSpace Space     = True
isLineBreakOrSpace _         = False

-- | Convert Pandoc block element to Sile.
blockToSile :: PandocMonad m
             => Block     -- ^ Block to convert
             -> LW m Doc
blockToSile Null = return empty
blockToSile (Div (identifier,classes,kvs) bs)
  | "incremental" `elem` classes = do
      let classes' = filter ("incremental"/=) classes
      blockToSile $ Div (identifier,classes',kvs) bs
  | "nonincremental" `elem` classes = do
      let classes' = filter ("nonincremental"/=) classes
      blockToSile $ Div (identifier,classes',kvs) bs
  | otherwise = do
      linkAnchor' <- hypertarget True identifier empty
    -- see #2704 for the motivation for adding \leavevmode:
      let linkAnchor =
            case bs of
              Para _ : _
                | not (isEmpty linkAnchor')
                  -> "\\leavevmode" <> linkAnchor' <> "%"
              _ -> linkAnchor'
      let align dir txt = inCmd "begin" dir $$ txt $$ inCmd "end" dir
      let wrapColumns = if "columns" `elem` classes
                        then \contents ->
                               inCmd "begin" "columns" <> brackets "T"
                               $$ contents
                               $$ inCmd "end" "columns"
                        else id
          wrapColumn  = if "column" `elem` classes
                        then \contents ->
                               let w = maybe "0.48" fromPct (lookup "width" kvs)
                               in  inCmd "begin" "column" <>
                                   braces (text w <> "\\textwidth")
                                   $$ contents
                                   $$ inCmd "end" "column"
                        else id
          fromPct xs =
            case reverse xs of
              '%':ds -> case safeRead (reverse ds) of
                          Just digits -> showFl (digits / 100 :: Double)
                          Nothing -> xs
              _      -> xs
          wrapDir = case lookup "dir" kvs of
                      Just "rtl" -> align "RTL"
                      Just "ltr" -> align "LTR"
                      _          -> id
          wrapNotes txt = if "notes" `elem` classes
                          then "\\note" <> braces txt -- speaker notes
                          else linkAnchor $$ txt
      (wrapColumns . wrapColumn . wrapDir . wrapNotes)
        <$> blockListToSile bs
blockToSile (Plain lst) =
  inlineListToSile $ dropWhile isLineBreakOrSpace lst
-- title beginning with fig: indicates that the image is a figure
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
blockToSile (CodeBlock (identifier,classes,keyvalAttr) str) = do
  opts <- gets stOptions
  lab <- labelFor identifier
  linkAnchor' <- hypertarget True identifier lab
  let linkAnchor = if isEmpty linkAnchor'
                      then empty
                      else linkAnchor' <> "%"
  let lhsCodeBlock = do
        modify $ \s -> s{ stLHS = True }
        return $ flush (linkAnchor $$ "\\begin{code}" $$ text str $$
                            "\\end{code}") $$ cr
  let rawCodeBlock = do
        st <- get
        env <- return "verbatim"
        return $ flush (linkAnchor $$ text ("\\begin{" ++ env ++ "}") $$
                 text str $$ text ("\\end{" ++ env ++ "}")) <> cr

  case () of
     _ | isEnabled Ext_literate_haskell opts && "haskell" `elem` classes &&
         "literate" `elem` classes           -> lhsCodeBlock
       | otherwise                           -> rawCodeBlock
blockToSile b@(RawBlock f x)
  | f == Format "sile" || f == Format "sil"
                        = return $ text x
  | otherwise           = do
      report $ BlockNotRendered b
      return empty
blockToSile (BulletList []) = return empty  -- otherwise latex error
blockToSile (BulletList lst) = do
  items <- mapM listItemToSile lst
  return $ text ("\\begin{listarea}") $$ vcat items $$
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
  return $ text ("\\begin[" ++ tostyle ++ "]{listarea}")
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
  "\\begin{center}\\rule{0.5\\linewidth}{\\linethickness}\\end{center}"
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
                else text "\\caption" <> braces captionText <> "\\tabularnewline"
                         $$ headers
                         $$ endfirsthead
  rows' <- mapM (tableRowToSile False aligns widths) rows
  let colDescriptors = text $ concat $ map toColDescriptor aligns
  modify $ \s -> s{ stTable = True }
  return $ "\\begin{longtable}[]" <>
              braces ("@{}" <> colDescriptors <> "@{}")
              -- the @{} removes extra space at beginning and end
         $$ capt
         $$ (if all null heads then "\\toprule" else empty)
         $$ headers
         $$ endhead
         $$ vcat rows'
         $$ "\\bottomrule"
         $$ "\\end{longtable}"

toColDescriptor :: Alignment -> String
toColDescriptor align =
  case align of
         AlignLeft    -> "l"
         AlignRight   -> "r"
         AlignCenter  -> "c"
         AlignDefault -> "l"

blockListToSile :: PandocMonad m => [Block] -> LW m Doc
blockListToSile lst =
  vsep `fmap` mapM (\b -> setEmptyLine True >> blockToSile b) lst

tableRowToSile :: PandocMonad m
                => Bool
                -> [Alignment]
                -> [Double]
                -> [[Block]]
                -> LW m Doc
tableRowToSile header aligns widths cols = do
  -- scale factor compensates for extra space between columns
  -- so the whole table isn't larger than columnwidth
  let scaleFactor = 0.97 ** fromIntegral (length aligns)
  let widths' = map (scaleFactor *) widths
  cells <- mapM (tableCellToSile header) $ zip3 widths' aligns cols
  return $ hsep (intersperse "&" cells) <> "\\tabularnewline"

-- For simple latex tables (without minipages or parboxes),
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
                 -> LW m Doc
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


listItemToSile :: PandocMonad m => [Block] -> LW m Doc
listItemToSile lst = do
  blockListToSile lst >>= return . (inCmd "listitem")

defListItemToSile :: PandocMonad m => ([Inline], [[Block]]) -> LW m Doc
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
              -> LW m Doc
sectionHeader unnumbered ident level lst = do
  txt <- inlineListToSile lst
  plain <- stringToSile TextString $ concatMap stringify lst
  let removeInvalidInline (Note _)             = []
      removeInvalidInline (Span (id', _, _) _) | not (null id') = []
      removeInvalidInline Image{}            = []
      removeInvalidInline x                    = [x]
  let lstNoNotes = foldr (mappend . (\x -> walkM removeInvalidInline x)) mempty lst
  txtNoNotes <- inlineListToSile lstNoNotes
  -- footnotes in sections don't work (except for starred variants)
  -- unless you specify an optional argument:
  -- \section[mysec]{mysec\footnote{blah}}
  optional <- if unnumbered || lstNoNotes == lst || null lstNoNotes
                 then return empty
                 else
                   return $ brackets txtNoNotes
  let contents = if render Nothing txt == plain
                    then braces txt
                    else braces (text "\\texorpdfstring"
                         <> braces txt
                         <> braces (text plain))
  book <- gets stBook
  opts <- gets stOptions
  let topLevelDivision = if book && writerTopLevelDivision opts == TopLevelDefault
                         then TopLevelChapter
                         else writerTopLevelDivision opts
  let level' = if
                  topLevelDivision `elem` [TopLevelPart, TopLevelChapter]
               then if level == 1 then -1 else level - 1
               else case topLevelDivision of
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
  let prefix = empty
  lab <- labelFor ident
  let star = if unnumbered && level' < 4 then text "*" else empty
  let stuffing = star <> optional <> contents
  stuffing' <- hypertarget True ident $
                  text ('\\':sectionType) <> stuffing <> lab
  return $ if level' > 5
              then txt
              else prefix $$ stuffing'
                   $$ if unnumbered
                         then "\\addcontentsline{toc}" <>
                                braces (text sectionType) <>
                                braces txtNoNotes
                         else empty

hypertarget :: PandocMonad m => Bool -> String -> Doc -> LW m Doc
hypertarget _ "" x    = return x
hypertarget addnewline ident x = do
  ref <- text `fmap` toLabel ident
  return $ text "\\hypertarget"
              <> braces ref
              <> braces ((if addnewline && not (isEmpty x)
                             then ("%" <> cr)
                             else empty) <> x)

labelFor :: PandocMonad m => String -> LW m Doc
labelFor ""    = return empty
labelFor ident = do
  ref <- text `fmap` toLabel ident
  return $ text "\\label" <> braces ref

-- | Convert list of inline elements to Sile.
inlineListToSile :: PandocMonad m
                  => [Inline]  -- ^ Inlines to convert
                  -> LW m Doc
inlineListToSile lst =
  mapM inlineToSile (fixLineInitialSpaces lst)
    >>= return . hcat
    -- nonbreaking spaces (~) in Sile don't work after line breaks,
    -- so we turn nbsps after hard breaks to \hspace commands.
    -- this is mostly used in verse.
 where fixLineInitialSpaces [] = []
       fixLineInitialSpaces (LineBreak : Str s@('\160':_) : xs) =
         LineBreak : fixNbsps s ++ fixLineInitialSpaces xs
       fixLineInitialSpaces (x:xs) = x : fixLineInitialSpaces xs
       fixNbsps s = let (ys,zs) = span (=='\160') s
                    in  replicate (length ys) hspace ++ [Str zs]
       hspace = RawInline "sile" "\\kern[width=1spc]"

-- | Convert inline element to Sile
inlineToSile :: PandocMonad m
              => Inline    -- ^ Inline to convert
              -> LW m Doc
inlineToSile (Span (id',classes,_) ils) = do
  ref <- toLabel id'
  let linkAnchor = if null id'
                      then empty
                      else "\\protect\\pdf:link" <> braces (text ref)
  let cmds = ["textup" | "csl-no-emph" `elem` classes] ++
             ["textnormal" | "csl-no-strong" `elem` classes ||
                             "csl-no-smallcaps" `elem` classes]
  contents <- inlineListToSile ils
  return $ linkAnchor <>
          if null cmds
              then braces contents
              else foldr inCmd contents cmds
inlineToSile (Emph lst) =
  inlineListToSile lst >>= return . inCmd "em"
inlineToSile (Strong lst) =
  inlineListToSile lst >>= return . inCmd "strong"
inlineToSile (Strikeout lst) = do
  inlineListToSile lst >>= return . inCmd "strike"
inlineToSile (Superscript lst) =
  inlineListToSile lst >>= return . inCmd "textsuperscript"
inlineToSile (Subscript lst) = do
  inlineListToSile lst >>= return . inCmd "textsubscript"
inlineToSile (SmallCaps lst) =
  inlineListToSile lst >>= return . inCmd "textsc"
inlineToSile (Cite cits lst) = do
  st <- get
  let opts = stOptions st
  case writerCiteMethod opts of
     Natbib   -> citationsToNatbib cits
     Biblatex -> citationsToBiblatex cits
     _        -> inlineListToSile lst

inlineToSile (Code (_,_,_) str) =
  return $ "\\code{" <> text str <> "}"
inlineToSile (Quoted SingleQuote lst) = do
  opts <- gets stOptions
  contents <- inlineListToSile lst
  return $ if isEnabled Ext_smart opts
              then "'" <> contents <> "'"
              else "‘" <> contents <> "’"
inlineToSile (Quoted DoubleQuote lst) = do
  opts <- gets stOptions
  contents <- inlineListToSile lst
  return $ if isEnabled Ext_smart opts
              then "\"" <> contents <> "\""
              else "“" <> contents <> "”"
inlineToSile (Str str) = liftM text $ stringToSile TextString str
inlineToSile (Math InlineMath str) =
  return $ "\\(" <> text str <> "\\)"
inlineToSile (Math DisplayMath str) = do
  setEmptyLine False
  return $ "\\[" <> text str <> "\\]"
inlineToSile  il@(RawInline f str)
  | f == Format "sile" || f == Format "sil"
                        = do
      setEmptyLine False
      return $ text str
  | otherwise           = do
      report $ InlineNotRendered il
      return empty
inlineToSile (LineBreak) = return $ "\\hfill\\break" <> cr
inlineToSile SoftBreak = do
  wrapText <- gets (writerWrapText . stOptions)
  case wrapText of
       WrapAuto     -> return space
       WrapNone     -> return space
       WrapPreserve -> return cr
inlineToSile Space = return space
inlineToSile (Link _ txt ('#':ident, _)) = do
  contents <- inlineListToSile txt
  lab <- toLabel ident
  return $ text "\\pdf:link" <> brackets ("dest=" <> text lab) <> braces contents
inlineToSile (Link (_,_,keyvalAttr) txt (src, tit)) =
  case txt of
        [Str x] | escapeURI x == src ->  -- autolink
             do modify $ \s -> s{ stUrl = True }
                src' <- stringToSile URLString (escapeURI src)
                return $ text $ "\\url{" ++ src' ++ "}"
        [Str x] | Just rest <- stripPrefix "mailto:" src,
                  escapeURI x == rest -> -- email autolink
             do modify $ \s -> s{ stUrl = True }
                src' <- stringToSile URLString (escapeURI src)
                contents <- inlineListToSile txt
                return $ "\\href" <> braces (text src') <>
                   braces ("\\url" <> braces contents)
        _ -> do contents <- inlineListToSile txt
                src' <- stringToSile URLString (escapeURI src)
                let params = (["src=\"" ++ src' ++ "\""]) ++
                              (if null tit
                                then []
                                else [ "title=\"" ++ tit ++ "\"" ]) ++
                              (if null keyvalAttr
                                  then []
                                  else [ key ++ "=\"" ++ val ++ "\"" | (key, val) <- keyvalAttr ])
                    linkattrs
                      | null params = empty
                      | otherwise = brackets $ hcat (intersperse "," (map text params))
                return $ "\\href" <> linkattrs <> braces contents
inlineToSile il@(Image _ _ ('d':'a':'t':'a':':':_, _)) = do
  report $ InlineNotRendered il
  return empty
inlineToSile (Image _ _ (source, _)) = do
  setEmptyLine False
  modify $ \s -> s{ stGraphics = True }
  let source' = if isURI source
                   then source
                   else unEscapeString source
  source'' <- stringToSile URLString source'
  return $ "\\img" <> brackets ("src=" <> text source'')
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

citationsToNatbib :: PandocMonad m => [Citation] -> LW m Doc
citationsToNatbib (one:[])
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
     ismode m  = all (((==) m)  . citationMode)
     p         = citationPrefix  $ head $ cits
     s         = citationSuffix  $ last $ cits
     ks        = intercalate ", " $ map citationId cits

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
            => String -> [Inline] -> [Inline] -> String -> LW m Doc
citeCommand c p s k = do
  args <- citeArguments p s k
  return $ text ("\\" ++ c) <> args

citeArguments :: PandocMonad m
              => [Inline] -> [Inline] -> String -> LW m Doc
citeArguments p s k = do
  let s' = case s of
        (Str (x:[]) : r) | isPunctuation x -> dropWhile (== Space) r
        (Str (x:xs) : r) | isPunctuation x -> Str xs : r
        _                -> s
  pdoc <- inlineListToSile p
  sdoc <- inlineListToSile s'
  let optargs = case (isEmpty pdoc, isEmpty sdoc) of
                     (True, True ) -> empty
                     (True, False) -> brackets sdoc
                     (_   , _    ) -> brackets pdoc <> brackets sdoc
  return $ optargs <> braces (text k)

citationsToBiblatex :: PandocMonad m => [Citation] -> LW m Doc
citationsToBiblatex (one:[])
  = citeCommand cmd p s k
    where
       Citation { citationId = k
                , citationPrefix = p
                , citationSuffix = s
                , citationMode = m
                } = one
       cmd = case m of
                  SuppressAuthor -> "autocite*"
                  AuthorInText   -> "textcite"
                  NormalCitation -> "autocite"

citationsToBiblatex (c:cs) = do
  args <- mapM convertOne (c:cs)
  return $ text cmd <> foldl' (<>) empty args
    where
       cmd = case citationMode c of
                  SuppressAuthor -> "\\autocites*"
                  AuthorInText   -> "\\textcites"
                  NormalCitation -> "\\autocites"
       convertOne Citation { citationId = k
                           , citationPrefix = p
                           , citationSuffix = s
                           }
              = citeArguments p s k

citationsToBiblatex _ = return empty


pDocumentOptions :: P.Parsec String () [String]
pDocumentOptions = do
  P.char '['
  opts <- P.sepBy
    (P.many $ P.spaces *> P.noneOf (" ,]" :: String) <* P.spaces)
    (P.char ',')
  P.char ']'
  return opts

pDocumentClass :: P.Parsec String () String
pDocumentClass =
  do P.skipMany (P.satisfy (/='\\'))
     P.string "\\documentclass"
     classOptions <- pDocumentOptions <|> return []
     if ("article" :: String) `elem` classOptions
       then return "article"
       else do P.skipMany (P.satisfy (/='{'))
               P.char '{'
               P.manyTill P.letter (P.char '}')
