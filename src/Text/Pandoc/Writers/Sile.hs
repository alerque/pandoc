{-# LANGUAGE OverloadedStrings, ScopedTypeVariables,
             PatternGuards #-}
{-
Copyright (C) 2006-2015 John MacFarlane <jgm@berkeley.edu>

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
   Copyright   : Copyright (C) 2006-2015 John MacFarlane
   License     : GNU GPL, version 2 or above

   Maintainer  : Caleb Maclennan <caleb@alerque.com>
   Stability   : alpha
   Portability : portable

Conversion of 'Pandoc' format into Sile.
-}
module Text.Pandoc.Writers.Sile ( writeSile ) where
import Text.Pandoc.Definition
import Text.Pandoc.Walk
import Text.Pandoc.Shared
import Text.Pandoc.Writers.Shared
import Text.Pandoc.Options
import Text.Pandoc.Templates
import Text.Printf ( printf )
import Network.URI ( isURI, unEscapeString )
import Data.Aeson (object, (.=))
import Data.List ( (\\), isInfixOf, stripPrefix, intercalate, intersperse, nub, nubBy )
import Data.Char ( toLower, isPunctuation, isAscii, isLetter, isDigit, ord )
import Data.Maybe ( fromMaybe )
import qualified Data.Text as T
import Control.Applicative ((<|>))
import Control.Monad.State
import qualified Text.Parsec as P
import Text.Pandoc.Pretty
import Text.Pandoc.Highlighting (highlight, styleToLaTeX,
                                 formatLaTeXInline, formatLaTeXBlock,
                                 toListingsLanguage)

data WriterState =
  WriterState { stInNote        :: Bool          -- true if we're in a note
              , stInQuote       :: Bool          -- true if in a blockquote
              , stInMinipage    :: Bool          -- true if in minipage
              , stInHeading     :: Bool          -- true if in a section heading
              , stNotes         :: [Doc]         -- notes in a minipage
              , stOLLevel       :: Int           -- level of ordered list nesting
              , stOptions       :: WriterOptions -- writer options, so they don't have to be parameter
              , stVerbInNote    :: Bool          -- true if document has verbatim text in note
              , stTable         :: Bool          -- true if document has a table
              , stStrikeout     :: Bool          -- true if document has strikeout
              , stUrl           :: Bool          -- true if document has visible URL link
              , stGraphics      :: Bool          -- true if document contains images
              , stLHS           :: Bool          -- true if document has literate haskell code
              , stBook          :: Bool          -- true if document uses book class
              , stCsquotes      :: Bool          -- true if document uses csquotes
              , stHighlighting  :: Bool          -- true if document has highlighted code
              , stInternalLinks :: [String]      -- list of internal link targets
              }

-- | Convert Pandoc to Sile.
writeSile :: WriterOptions -> Pandoc -> String
writeSile options document =
  evalState (pandocToSile options document) $
  WriterState { stInNote = False, stInQuote = False,
                stInMinipage = False, stInHeading = False,
                stNotes = [], stOLLevel = 1,
                stOptions = options, stVerbInNote = False,
                stTable = False, stStrikeout = False,
                stUrl = False, stGraphics = False,
                stLHS = False, stBook = writerChapters options,
                stCsquotes = False, stHighlighting = False,
                stInternalLinks = [] }

pandocToSile :: WriterOptions -> Pandoc -> State WriterState String
pandocToSile options (Pandoc meta blocks) = do
  -- Strip off final 'references' header if --natbib or --biblatex
  let method = writerCiteMethod options
  let blocks' = if method == Biblatex || method == Natbib
                   then case reverse blocks of
                             (Div (_,["references"],_) _):xs -> reverse xs
                             _ -> blocks
                   else blocks
  -- see if there are internal links
  let isInternalLink (Link _ ('#':xs,_))  = [xs]
      isInternalLink _                    = []
  modify $ \s -> s{ stInternalLinks = query isInternalLink blocks' }
  let template = writerTemplate options
  -- set stBook depending on documentclass
  let colwidth = if writerWrapText options
                    then Just $ writerColumns options
                    else Nothing
  metadata <- metaToJSON options
              (fmap (render colwidth) . blockListToSile)
              (fmap (render colwidth) . inlineListToSile)
              meta
  let bookClasses = ["book"]
  let documentClass = case P.parse (do P.skipMany (P.satisfy (/='\\'))
                                       P.string "\\documentclass"
                                       P.skipMany (P.satisfy (/='{'))
                                       P.char '{'
                                       P.manyTill P.letter (P.char '}')) "template"
                              template of
                              Right r -> r
                              Left _  -> ""
  case lookup "documentclass" (writerVariables options) `mplus`
        fmap stringify (lookupMeta "documentclass" meta) of
         Just x  | x `elem` bookClasses -> modify $ \s -> s{stBook = True}
                 | otherwise            -> return ()
         Nothing | documentClass `elem` bookClasses
                                        -> modify $ \s -> s{stBook = True}
                 | otherwise               -> return ()
  -- check for \usepackage...{csquotes}; if present, we'll use
  -- \enquote{...} for smart quotes:
  when ("{csquotes}" `isInfixOf` template) $
    modify $ \s -> s{stCsquotes = True}
  let (blocks'', lastHeader) = if writerCiteMethod options == Citeproc then
                                 (blocks', [])
                               else case last blocks' of
                                 Header 1 _ il -> (init blocks', il)
                                 _             -> (blocks', [])
  blocks''' <- return blocks''
  body <- mapM (elementToSile options) $ hierarchicalize blocks'''
  (biblioTitle :: String) <- liftM (render colwidth) $ inlineListToSile lastHeader
  let main = render colwidth $ vsep body
  st <- get
  titleMeta <- stringToSile TextString $ stringify $ docTitle meta
  authorsMeta <- mapM (stringToSile TextString . stringify) $ docAuthors meta
  let docLangs = nub $ query (extract "lang") blocks
  let context  =  defField "toc" (writerTableOfContents options) $
                  defField "toc-depth" (show (writerTOCDepth options -
                                              if stBook st
                                                 then 1
                                                 else 0)) $
                  defField "body" main $
                  defField "title-meta" titleMeta $
                  defField "author-meta" (intercalate "; " authorsMeta) $
                  defField "documentclass" (if stBook st
                                               then "book"::String
                                               else "plain"::String) $
                  defField "verbatim-in-note" (stVerbInNote st) $
                  defField "tables" (stTable st) $
                  defField "strikeout" (stStrikeout st) $
                  defField "url" (stUrl st) $
                  defField "numbersections" (writerNumberSections options) $
                  defField "lhs" (stLHS st) $
                  defField "graphics" (stGraphics st) $
                  defField "book-class" (stBook st) $
                  defField "listings" (writerListings options || stLHS st) $
                  (if stHighlighting st
                      then defField "highlighting-macros" (styleToLaTeX
                                $ writerHighlightStyle options )
                      else id) $
                  (case writerCiteMethod options of
                         Natbib   -> defField "biblio-title" biblioTitle .
                                     defField "natbib" True
                         Biblatex -> defField "biblio-title" biblioTitle .
                                     defField "biblatex" True
                         _        -> id) $
                  -- set lang to something so polyglossia/babel is included
                  defField "lang" (if null docLangs then ""::String else "en") $
                  metadata
  return $ if writerStandalone options
              then renderTemplate' template context
              else main

-- | Convert Elements to Sile
elementToSile :: WriterOptions -> Element -> State WriterState Doc
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
stringToSile :: StringContext -> String -> State WriterState String
stringToSile  _     []     = return ""
stringToSile  ctx (x:xs) = do
  opts <- gets stOptions
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

toLabel :: String -> State WriterState String
toLabel z = go `fmap` stringToSile URLString z
 where go [] = ""
       go (x:xs)
         | (isLetter x || isDigit x) && isAscii x = x:go xs
         | elem x ("-+=:;." :: String) = x:go xs
         | otherwise = "ux" ++ printf "%x" (ord x) ++ go xs

-- | Puts contents into Sile command.
inCmd :: String -> Doc -> Doc
inCmd cmd contents = char '\\' <> text cmd <> braces contents


isListBlock :: Block -> Bool
isListBlock (BulletList _)     = True
isListBlock (OrderedList _ _)  = True
isListBlock (DefinitionList _) = True
isListBlock _                  = False

isLineBreakOrSpace :: Inline -> Bool
isLineBreakOrSpace LineBreak = True
isLineBreakOrSpace Space = True
isLineBreakOrSpace _ = False

-- | Convert Pandoc block element to Sile.
blockToSile :: Block     -- ^ Block to convert
             -> State WriterState Doc
blockToSile Null = return empty
blockToSile (Div (identifier,classes,kvs) bs) = do
  ref <- toLabel identifier
  let linkAnchor = if null identifier
                      then empty
                      else "\\hypertarget" <> braces (text ref) <>
                             braces empty
  contents <- blockListToSile bs
  return (linkAnchor $$ contents)
blockToSile (Plain lst) =
  inlineListToSile $ dropWhile isLineBreakOrSpace lst
-- title beginning with fig: indicates that the image is a figure
blockToSile (Para [Image txt (src,'f':'i':'g':':':tit)]) = do
  inNote <- gets stInNote
  modify $ \st -> st{ stInMinipage = True, stNotes = [] }
  capt <- inlineListToSile txt
  notes <- gets stNotes
  modify $ \st -> st{ stInMinipage = False, stNotes = [] }
  -- We can't have footnotes in the list of figures, so remove them:
  captForLof <- if null notes
                   then return empty
                   else brackets <$> inlineListToSile (walk deNote txt)
  img <- inlineToSile (Image txt (src,tit))
  let footnotes = notesToSile notes
  return $ if inNote
              -- can't have figures in notes
              then "\\begin{center}" $$ img $+$ capt $$ "\\end{center}"
              else "\\begin{figure}[htbp]" $$ "\\centering" $$ img $$
                    ("\\caption" <> captForLof <> braces capt) $$
                    "\\end{figure}" $$
                    footnotes
blockToSile (Para [Str ".",Space,Str ".",Space,Str "."]) = do
  inlineListToSile [Str ".",Space,Str ".",Space,Str "."]
blockToSile (Para lst) =
  inlineListToSile $ dropWhile isLineBreakOrSpace lst
blockToSile (BlockQuote lst) = do
  oldInQuote <- gets stInQuote
  modify (\s -> s{stInQuote = True})
  contents <- blockListToSile lst
  modify (\s -> s{stInQuote = oldInQuote})
  return $ "\\begin{quote}" $$ contents $$ "\\end{quote}"
blockToSile (CodeBlock (identifier,classes,keyvalAttr) str) = do
  opts <- gets stOptions
  ref <- toLabel identifier
  let linkAnchor = if null identifier
                      then empty
                      else "\\hypertarget" <> braces (text ref) <>
                                braces ("%\\label" <> braces (text ref))
  let lhsCodeBlock = do
        modify $ \s -> s{ stLHS = True }
        return $ flush (linkAnchor $$ "\\begin{code}" $$ text str $$
                            "\\end{code}") $$ cr
  let rawCodeBlock = do
        st <- get
        env <- if stInNote st
                  then modify (\s -> s{ stVerbInNote = True }) >>
                       return "Verbatim"
                  else return "verbatim"
        return $ flush (linkAnchor $$ text ("\\begin{" ++ env ++ "}") $$
                 text str $$ text ("\\end{" ++ env ++ "}")) <> cr
  let listingsCodeBlock = do
        st <- get
        let params = if writerListings (stOptions st)
                     then (case getListingsLanguage classes of
                                Just l  -> [ "language=" ++ l ]
                                Nothing -> []) ++
                          [ "numbers=left" | "numberLines" `elem` classes
                             || "number" `elem` classes
                             || "number-lines" `elem` classes ] ++
                          [ (if key == "startFrom"
                                then "firstnumber"
                                else key) ++ "=" ++ attr |
                                (key,attr) <- keyvalAttr ] ++
                          (if identifier == ""
                                then []
                                else [ "label=" ++ ref ])

                     else []
            printParams
                | null params = empty
                | otherwise   = brackets $ hcat (intersperse ", " (map text params))
        return $ flush ("\\begin{lstlisting}" <> printParams $$ text str $$
                 "\\end{lstlisting}") $$ cr
  let highlightedCodeBlock =
        case highlight formatLaTeXBlock ("",classes,keyvalAttr) str of
               Nothing -> rawCodeBlock
               Just  h -> modify (\st -> st{ stHighlighting = True }) >>
                          return (flush $ linkAnchor $$ text h)
  case () of
     _ | isEnabled Ext_literate_haskell opts && "haskell" `elem` classes &&
         "literate" `elem` classes                      -> lhsCodeBlock
       | writerListings opts                            -> listingsCodeBlock
       | writerHighlight opts && not (null classes)     -> highlightedCodeBlock
       | otherwise                                      -> rawCodeBlock
blockToSile (RawBlock f x)
  | f == Format "sile" || f == Format "sil"
                        = return $ text x
  | otherwise           = return empty
blockToSile (BulletList []) = return empty  -- otherwise latex error
blockToSile (BulletList lst) = do
  items <- mapM listItemToSile lst
  let spacing = if isTightList lst
                   then text "\\tightlist"
                   else empty
  return $ spacing $$ vcat items
blockToSile (OrderedList _ []) = return empty -- otherwise latex error
blockToSile (OrderedList (start, numstyle, numdelim) lst) = do
  st <- get
  let oldlevel = stOLLevel st
  put $ st {stOLLevel = oldlevel + 1}
  items <- mapM listItemToSile lst
  modify (\s -> s {stOLLevel = oldlevel})
  let tostyle x = case numstyle of
                       Decimal      -> "\\arabic" <> braces x
                       UpperRoman   -> "\\Roman" <> braces x
                       LowerRoman   -> "\\roman" <> braces x
                       UpperAlpha   -> "\\Alph" <> braces x
                       LowerAlpha   -> "\\alph" <> braces x
                       Example      -> "\\arabic" <> braces x
                       DefaultStyle -> "\\arabic" <> braces x
  let todelim x = case numdelim of
                       OneParen    -> x <> ")"
                       TwoParens   -> parens x
                       Period      -> x <> "."
                       _           -> x <> "."
  let enum = text $ "enum" ++ map toLower (toRomanNumeral oldlevel)
  let stylecommand = if numstyle == DefaultStyle && numdelim == DefaultDelim
                        then empty
                        else "\\def" <> "\\label" <> enum <>
                              braces (todelim $ tostyle enum)
  let resetcounter = if start == 1 || oldlevel > 4
                        then empty
                        else "\\setcounter" <> braces enum <>
                              braces (text $ show $ start - 1)
  let spacing = if isTightList lst
                   then text "\\tightlist"
                   else empty
  return $ text ("\\begin{enumerate}")
         $$ stylecommand
         $$ resetcounter
         $$ spacing
         $$ vcat items
         $$ "\\end{enumerate}"
blockToSile (DefinitionList []) = return empty
blockToSile (DefinitionList lst) = do
  items <- mapM defListItemToSile lst
  let spacing = if all isTightList (map snd lst)
                   then text "\\tightlist"
                   else empty
  return $ text ("\\begin{description}") $$ spacing $$ vcat items $$
               "\\end{description}"
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
                else ($$ "\\midrule\n") `fmap`
                      (tableRowToSile True aligns widths) heads
  let endhead = if all null heads
                   then empty
                   else text "\\endhead"
  captionText <- inlineListToSile caption
  let capt = if isEmpty captionText
                then empty
                else text "\\caption" <> braces captionText
                         <> "\\tabularnewline\n\\toprule\n"
                         <> headers
                         <> "\\endfirsthead"
  rows' <- mapM (tableRowToSile False aligns widths) rows
  let colDescriptors = text $ concat $ map toColDescriptor aligns
  modify $ \s -> s{ stTable = True }
  return $ "\\begin{longtable}[c]" <>
              braces ("@{}" <> colDescriptors <> "@{}")
              -- the @{} removes extra space at beginning and end
         $$ capt
         $$ "\\toprule"
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

blockListToSile :: [Block] -> State WriterState Doc
blockListToSile lst = vsep `fmap` mapM blockToSile lst

tableRowToSile :: Bool
                -> [Alignment]
                -> [Double]
                -> [[Block]]
                -> State WriterState Doc
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
                       chunks -> RawInline "tex" "\\vtop{" :
                                 concatMap tohbox chunks ++
                                 [RawInline "tex" "}"]
  where tohbox ys = RawInline "tex" "\\hbox{\\strut " : ys ++
                    [RawInline "tex" "}"]

-- We also change display math to inline math, since display
-- math breaks in simple tables.
displayMathToInline :: Inline -> Inline
displayMathToInline (Math DisplayMath x) = Math InlineMath x
displayMathToInline x = x

tableCellToSile :: Bool -> (Double, Alignment, [Block])
                 -> State WriterState Doc
tableCellToSile _      (0,     _,     blocks) =
  blockListToSile $ walk fixLineBreaks $ walk displayMathToInline blocks
tableCellToSile header (width, align, blocks) = do
  modify $ \st -> st{ stInMinipage = True, stNotes = [] }
  cellContents <- blockListToSile blocks
  notes <- gets stNotes
  modify $ \st -> st{ stInMinipage = False, stNotes = [] }
  let valign = text $ if header then "[b]" else "[t]"
  let halign = case align of
               AlignLeft    -> "\\raggedright"
               AlignRight   -> "\\raggedleft"
               AlignCenter  -> "\\centering"
               AlignDefault -> "\\raggedright"
  return $ ("\\begin{minipage}" <> valign <>
            braces (text (printf "%.2f\\columnwidth" width)) <>
            (halign <> "\\strut" <> cr <> cellContents <> cr) <>
            "\\strut\\end{minipage}") $$
            notesToSile notes

notesToSile :: [Doc] -> Doc
notesToSile [] = empty
notesToSile ns = (case length ns of
                              n | n > 1 -> "\\addtocounter" <>
                                           braces "footnote" <>
                                           braces (text $ show $ 1 - n)
                                | otherwise -> empty)
                   $$
                   vcat (intersperse
                     ("\\addtocounter" <> braces "footnote" <> braces "1")
                     $ map (\x -> "\\footnotetext" <> braces x)
                     $ reverse ns)

listItemToSile :: [Block] -> State WriterState Doc
listItemToSile lst
  -- we need to put some text before a header if it's the first
  -- element in an item. This will look ugly in Sile regardless, but
  -- this will keep the typesetter from throwing an error.
  | ((Header _ _ _) :_) <- lst =
    blockListToSile lst >>= return . (inCmd "listitem")
  | otherwise = blockListToSile lst >>= return .  (inCmd "listitem")

defListItemToSile :: ([Inline], [[Block]]) -> State WriterState Doc
defListItemToSile (term, defs) = do
    term' <- inlineListToSile term
    def'  <- liftM vsep $ mapM blockListToSile defs
    return $ case defs of
     (((Header _ _ _) : _) : _) ->
       "\\listitem" <> brackets term' <> " ~ " $$ def'
     _                          ->
       "\\listitem" <> brackets term' $$ def'

-- | Craft the section header, inserting the secton reference, if supplied.
sectionHeader :: Bool    -- True for unnumbered
              -> [Char]
              -> Int
              -> [Inline]
              -> State WriterState Doc
sectionHeader unnumbered ref level lst = do
  txt <- inlineListToSile lst
  lab <- text `fmap` toLabel ref
  plain <- stringToSile TextString $ foldl (++) "" $ map stringify lst
  let noNote (Note _) = Str ""
      noNote x        = x
  let lstNoNotes = walk noNote lst
  txtNoNotes <- inlineListToSile lstNoNotes
  let star = if unnumbered then text "*" else empty
  -- footnotes in sections don't work (except for starred variants)
  -- unless you specify an optional argument:
  -- \section[mysec]{mysec\footnote{blah}}
  optional <- if unnumbered || lstNoNotes == lst
                 then return empty
                 else do
                   return $ brackets txtNoNotes
  let contents = if render Nothing txt == plain
                    then braces txt
                    else braces (text "\\texorpdfstring"
                         <> braces txt
                         <> braces (text plain))
  let stuffing = star <> optional <> contents
  book <- gets stBook
  opts <- gets stOptions
  let level' = if book || writerChapters opts then level - 1 else level
  internalLinks <- gets stInternalLinks
  let refLabel x = (if ref `elem` internalLinks
                       then text "\\hypertarget"
                                <> braces lab
                                <> braces x
                       else x)
  let headerWith x y = refLabel $ text x <> y <>
                             if null ref
                                then empty
                                else text "%\\label" <> braces lab
  let sectionType = case level' of
                          0  -> "chapter"
                          1  -> "section"
                          2  -> "subsection"
                          3  -> "subsubsection"
                          4  -> "paragraph"
                          5  -> "subparagraph"
                          _  -> ""
  inQuote <- gets stInQuote
  let prefix = if inQuote && level' >= 4
                  then text "\\mbox{}%"
                  -- needed for \paragraph, \subparagraph in quote environment
                  -- see http://tex.stackexchange.com/questions/169830/
                  else empty
  return $ if level' > 5
              then txt
              else prefix $$
                   headerWith ('\\':sectionType) stuffing
                   $$ if unnumbered
                         then "\\addcontentsline{toc}" <>
                                braces (text sectionType) <>
                                braces txtNoNotes
                         else empty

-- | Convert list of inline elements to Sile.
inlineListToSile :: [Inline]  -- ^ Inlines to convert
                  -> State WriterState Doc
inlineListToSile lst =
  mapM inlineToSile (fixBreaks $ fixLineInitialSpaces lst)
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
       hspace = RawInline "sile" "\\hspace*{0.333em}"
       -- linebreaks after blank lines cause problems:
       fixBreaks [] = []
       fixBreaks ys@(LineBreak : LineBreak : _) =
         case span (== LineBreak) ys of
               (lbs, rest) -> RawInline "sile"
                               ("\\\\[" ++ show (length lbs) ++
                                "\\baselineskip]") : fixBreaks rest
       fixBreaks (y:ys) = y : fixBreaks ys

isQuoted :: Inline -> Bool
isQuoted (Quoted _ _) = True
isQuoted _ = False

-- | Convert inline element to Sile
inlineToSile :: Inline    -- ^ Inline to convert
              -> State WriterState Doc
inlineToSile (Span (id',classes,kvs) ils) = do
  let noEmph = "csl-no-emph" `elem` classes
  let noStrong = "csl-no-strong" `elem` classes
  let noSmallCaps = "csl-no-smallcaps" `elem` classes
  let rtl = ("dir","rtl") `elem` kvs
  let ltr = ("dir","ltr") `elem` kvs
  ref <- toLabel id'
  let linkAnchor = if null id'
                      then empty
                      else "\\protect\\hypertarget" <> braces (text ref) <>
                             braces empty
  fmap (linkAnchor <>)
    ((if noEmph then inCmd "textup" else id) .
     (if noStrong then inCmd "font[weight=400]" else id) .
     (if noSmallCaps then inCmd "font[weight=400]" else id) .
     (if rtl then inCmd "RL" else id) .
     (if ltr then inCmd "LR" else id) .
     (if not (noEmph || noStrong || noSmallCaps)
         then braces
         else id)) `fmap` inlineListToSile ils
inlineToSile (Emph lst) =
  inlineListToSile lst >>= return . inCmd "font[style=italic]"
inlineToSile (Strong lst) =
  inlineListToSile lst >>= return . inCmd "font[weight=800]"
inlineToSile (Strikeout lst) = do
  -- we need to protect VERB in an mbox or we get an error
  -- see #1294
  contents <- inlineListToSile $ protectCode lst
  modify $ \s -> s{ stStrikeout = True }
  return $ inCmd "sout" contents
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

inlineToSile (Code (_,classes,_) str) = do
  opts <- gets stOptions
  inHeading <- gets stInHeading
  case () of
     _ | writerListings opts  && not inHeading      -> listingsCode
       | writerHighlight opts && not (null classes) -> highlightCode
       | otherwise                                  -> rawCode
   where listingsCode = do
           inNote <- gets stInNote
           when inNote $ modify $ \s -> s{ stVerbInNote = True }
           let chr = case "!\"&'()*,-./:;?@_" \\ str of
                          (c:_) -> c
                          []    -> '!'
           return $ text $ "\\lstinline" ++ [chr] ++ str ++ [chr]
         highlightCode = do
           case highlight formatLaTeXInline ("",classes,[]) str of
                  Nothing -> rawCode
                  Just  h -> modify (\st -> st{ stHighlighting = True }) >>
                             return (text h)
         rawCode = liftM (text . (\s -> "\\texttt{" ++ escapeSpaces s ++ "}"))
                          $ stringToSile CodeString str
           where
             escapeSpaces =  concatMap (\c -> if c == ' ' then "\\ " else [c])
inlineToSile (Quoted qt lst) = do
  contents <- inlineListToSile lst
  csquotes <- liftM stCsquotes get
  opts <- gets stOptions
  if csquotes
     then return $ "\\enquote" <> braces contents
     else do
       let s1 = if (not (null lst)) && (isQuoted (head lst))
                   then "\\,"
                   else empty
       let s2 = if (not (null lst)) && (isQuoted (last lst))
                   then "\\,"
                   else empty
       let inner = s1 <> contents <> s2
       return $ case qt of
                DoubleQuote -> char '\x201C' <> inner <> char '\x201D'
                SingleQuote -> char '\x2018' <> inner <> char '\x2019'
inlineToSile (Str str) = liftM text $ stringToSile TextString str
inlineToSile (Math InlineMath str) =
  return $ "\\(" <> text str <> "\\)"
inlineToSile (Math DisplayMath str) =
  return $ "\\[" <> text str <> "\\]"
inlineToSile (RawInline f str)
  | f == Format "sile" || f == Format "sil"
                        = return $ text str
  | otherwise           = return empty
inlineToSile (LineBreak) = return $ "\\\\" <> cr
inlineToSile Space = return space
inlineToSile (Link txt ('#':ident, _)) = do
  contents <- inlineListToSile txt
  lab <- toLabel ident
  return $ text "\\protect\\hyperlink" <> braces (text lab) <> braces contents
inlineToSile (Link txt (src, _)) =
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
                   braces ("\\nolinkurl" <> braces contents)
        _ -> do contents <- inlineListToSile txt
                src' <- stringToSile URLString (escapeURI src)
                return $ text ("\\href{" ++ src' ++ "}{") <>
                         contents <> char '}'
inlineToSile (Image _ (source, _)) = do
  modify $ \s -> s{ stGraphics = True }
  let source' = if isURI source
                   then source
                   else unEscapeString source
  source'' <- stringToSile URLString (escapeURI source')
  inHeading <- gets stInHeading
  return $
    (if inHeading then "\\protect\\includegraphics" else "\\includegraphics")
    <> braces (text source'')
inlineToSile (Note contents) = do
  inMinipage <- gets stInMinipage
  modify (\s -> s{stInNote = True})
  contents' <- blockListToSile contents
  modify (\s -> s {stInNote = False})
  let optnl = case reverse contents of
                   (CodeBlock _ _ : _) -> cr
                   _                   -> empty
  let noteContents = nest 2 contents' <> optnl
  opts <- gets stOptions
  modify $ \st -> st{ stNotes = noteContents : stNotes st }
  return $
    if inMinipage
       then "\\footnotemark{}"
       -- note: a \n before } needed when note ends with a Verbatim environment
       else "\\footnote" <> braces noteContents

protectCode :: [Inline] -> [Inline]
protectCode [] = []
protectCode (x@(Code ("",[],[]) _) : xs) = x : protectCode xs
protectCode (x@(Code _ _) : xs) = ltx "\\mbox{" : x : ltx "}" : xs
  where ltx = RawInline (Format "sile")
protectCode (x : xs) = x : protectCode xs

citationsToNatbib :: [Citation] -> State WriterState Doc
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
             AuthorInText     -> "citet"
             SuppressAuthor  -> "citeyearpar"
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
  return $ text "\\citetext{" <> foldl combineTwo empty cits' <> text "}"
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

citeCommand :: String -> [Inline] -> [Inline] -> String -> State WriterState Doc
citeCommand c p s k = do
  args <- citeArguments p s k
  return $ text ("\\" ++ c) <> args

citeArguments :: [Inline] -> [Inline] -> String -> State WriterState Doc
citeArguments p s k = do
  let s' = case s of
        (Str (x:[]) : r) | isPunctuation x -> dropWhile (== Space) r
        (Str (x:xs) : r) | isPunctuation x -> Str xs : r
        _                                  -> s
  pdoc <- inlineListToSile p
  sdoc <- inlineListToSile s'
  let optargs = case (isEmpty pdoc, isEmpty sdoc) of
                     (True, True ) -> empty
                     (True, False) -> brackets sdoc
                     (_   , _    ) -> brackets pdoc <> brackets sdoc
  return $ optargs <> braces (text k)

citationsToBiblatex :: [Citation] -> State WriterState Doc
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
  return $ text cmd <> foldl (<>) empty args
    where
       cmd = case citationMode c of
                  AuthorInText -> "\\textcites"
                  _            -> "\\autocites"
       convertOne Citation { citationId = k
                           , citationPrefix = p
                           , citationSuffix = s
                           }
              = citeArguments p s k

citationsToBiblatex _ = return empty

-- Determine listings language from list of class attributes.
getListingsLanguage :: [String] -> Maybe String
getListingsLanguage [] = Nothing
getListingsLanguage (x:xs) = toListingsLanguage x <|> getListingsLanguage xs

-- Extract a key from divs and spans
extract :: String -> Block -> [String]
extract key (Div attr _)     = lookKey key attr
extract key (Plain ils)      = concatMap (extractInline key) ils
extract key (Para ils)       = concatMap (extractInline key) ils
extract key (Header _ _ ils) = concatMap (extractInline key) ils
extract _ _                  = []

-- Extract a key from spans
extractInline :: String -> Inline -> [String]
extractInline key (Span attr _) = lookKey key attr
extractInline _ _               = []

-- Look up a key in an attribute and give a list of its values
lookKey :: String -> Attr -> [String]
lookKey key (_,_,kvs) =  maybe [] words $ lookup key kvs

deNote :: Inline -> Inline
deNote (Note _) = RawInline (Format "sile") ""
deNote x = x
