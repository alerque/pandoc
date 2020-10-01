{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
{- |
   Module      : Text.Pandoc.Writers.Sile
   Copyright   : Copyright (C) 2015-2020 Caleb Maclennan
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
import Control.Monad.State.Strict
import Data.Char (isAscii, isDigit, isLetter, isPunctuation, ord)
import Data.List (foldl', intersperse)
import Data.Text (Text)
import qualified Data.Text as T
import Network.URI (unEscapeString)
import Text.DocTemplates (FromContext(lookupContext), renderTemplate)
import Text.Pandoc.Class (PandocMonad, report) -- , toLang)
import Text.Pandoc.Definition
import Text.Pandoc.Logging
import Text.Pandoc.Options
import Text.DocLayout
import Text.Pandoc.Shared
import Text.Pandoc.Walk
import Text.Pandoc.Writers.Shared
import Text.Printf (printf)

data WriterState =
  WriterState {
                stInHeading     :: Bool          -- true if in a section heading
              , stOLLevel       :: Int           -- level of ordered list nesting
              , stOptions       :: WriterOptions -- writer options, so they don't have to be parameter
              , stHasChapters   :: Bool          -- true if document has chapters
              , stEmptyLine     :: Bool          -- true if no content on line
              }

startingState :: WriterOptions -> WriterState
startingState options = WriterState {
                  stInHeading = False
                , stOLLevel = 1
                , stOptions = options
                , stHasChapters = case writerTopLevelDivision options of
                                TopLevelPart    -> True
                                TopLevelChapter -> True
                                _               -> False
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
  let colwidth = if writerWrapText options == WrapAuto
                    then Just $ writerColumns options
                    else Nothing
  metadata <- metaToContext options
              blockListToSile
              (fmap chomp . inlineListToSile)
              meta
  let chaptersClasses = ["book","jbook","markdown","bible","triglot","docbook"]
  let documentClass =
        case lookupContext "documentclass" (writerVariables options) `mplus`
              (stringify <$> lookupMeta "documentclass" meta) of
                 Just x -> x
                 Nothing -> case writerTopLevelDivision options of
                                 TopLevelPart    -> "book"
                                 TopLevelChapter -> "book"
                                 _               -> "plain"
  when (documentClass `elem` chaptersClasses) $
     modify $ \s -> s{ stHasChapters = True }
  main <- blockListToSile blocks'
  st <- get
  titleMeta <- stringToSile TextString $ stringify $ docTitle meta
  authorsMeta <- mapM (stringToSile TextString . stringify) $ docAuthors meta

  let context  =  defField "toc" (writerTableOfContents options) $
                  defField "toc-depth" (tshow
                                        (writerTOCDepth options -
                                              if stHasChapters st
                                                 then 1
                                                 else 0)) $
                  defField "body" main $
                  defField "title-meta" titleMeta $
                  defField "author-meta"
                        (T.intercalate "; " authorsMeta) $
                  defField "documentclass" documentClass $
                  defField "numbersections" (writerNumberSections options) $
                  defField "has-chapters" (stHasChapters st) $
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
  go _ ctx x xs   =
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

toOptions :: PandocMonad m => Text -> [Text] -> [(Text, Text)] -> LW m [Text]
toOptions ident classes kvs = do
  ref <- toLabel ident
  -- lang <- toLang $ lookup "lang" kvs
  let classes' = [ val | (val) <- classes ]
  let classes'' = T.intercalate "," classes'
  let options = (if T.null ident
                  then []
                  else [ "id=" <> ref ]) <>
                (if null classes'
                    then []
                    else [ "classes=\"" <> classes'' <> "\"" ] ) <>
                (if null kvs
                    then []
                    else [ key <> "=" <> attr | (key, attr) <- kvs ])
  return options

inCmd :: Text -> Doc Text -> Doc Text
inCmd cmd content = do
  char '\\' <> literal cmd <> braces content

inOptCmd :: Text -> [Text] -> Doc Text -> Doc Text
inOptCmd cmd args content = do
  let args' = if null args
                 then ""
                 else brackets $ hcat (intersperse "," (map literal args))
  char '\\' <> literal cmd <> args' <> braces content

inOptEnv :: Text -> [Text] -> Doc Text -> Doc Text
inOptEnv cmd args content = do
  let args' = if null args
                 then ""
                 else brackets $ hcat (intersperse "," (map literal args))
      cmd' = braces (literal cmd)
  literal "\\begin" <> args' <> cmd'
        $$ content
        $$ literal "\\end" <> cmd'

-- | Convert Pandoc block element to Sile.
blockToSile :: PandocMonad m
             => Block     -- ^ Block to convert
             -> LW m (Doc Text)
blockToSile Null = return empty
blockToSile (Div (ident,classes,kvs) bs) = do
  options <- toOptions ident classes kvs
  content <- blockListToSile bs
  return $ inOptEnv "Div" options content
blockToSile (Plain lst) =
  inlineListToSile lst
blockToSile (Para [Str ".",Space,Str ".",Space,Str "."]) = do
  inlineListToSile [Str ".",Space,Str ".",Space,Str "."]
blockToSile (Para lst) =
  inlineListToSile lst
blockToSile (LineBlock lns) =
  blockToSile $ linesToPara lns
blockToSile (BlockQuote lst) = do
  let options = []
  content <- blockListToSile lst
  return $ inOptEnv "quote" options content
blockToSile (CodeBlock (ident,classes,kvs) str) = do
  options <- toOptions ident classes kvs
  content <- liftM literal $ stringToSile CodeString str
  return $ inOptEnv "verbatim" options content
blockToSile b@(RawBlock f x)
  | f == Format "sile" || f == Format "sil"
                        = return $ literal x
  | otherwise           = do
      report $ BlockNotRendered b
      return empty
blockToSile (BulletList []) = return empty  -- otherwise sile error
blockToSile (BulletList lst) = do
  items <- mapM listItemToSile lst
  let content = vcat items
  return $ inOptEnv "listarea" [] content
blockToSile (OrderedList _ []) = return empty -- otherwise error
blockToSile (OrderedList (start, numstyle, _) lst) = do
  st <- get
  let oldlevel = stOLLevel st
  put $ st {stOLLevel = oldlevel + 1}
  items <- mapM listItemToSile lst
  let content = vcat items
  modify (\s -> s {stOLLevel = oldlevel})
  let numstyle' = case numstyle of
                      Decimal      -> "arabic"
                      UpperRoman   -> "Roman"
                      LowerRoman   -> "roman"
                      UpperAlpha   -> "Alpha"
                      LowerAlpha   -> "alpha"
                      Example      -> "arabic"
                      DefaultStyle -> "arabic"
  let start' = T.pack $ show start
  let opts =  [("numberstyle", numstyle')] ++
              [("start", start') | start > 1] ++
              [("tight", "true") | isTightList lst]
  options <- toOptions "" [] opts
  return $ inOptEnv "OrderedList" options content
blockToSile (DefinitionList []) = return empty
blockToSile (DefinitionList lst) = do
  items <- mapM defListItemToSile lst
  let content = vcat items
  let opts = [("tight", "true") | all isTightList (map snd lst)]
  options <- toOptions "" [] opts
  return $ inOptEnv "DefinitionList" options content
blockToSile HorizontalRule = return $
  "\\HorizontalRule"
blockToSile (Header level (id',classes,_) lst) = do
  modify $ \s -> s{stInHeading = True}
  hdr <- sectionHeader classes id' level lst
  modify $ \s -> s{stInHeading = False}
  return hdr
blockToSile (Table _ _ _ _ _) = do
  return $ "\\script{SU.warn(\"Unimplemented, tables!\")}"

blockListToSile :: PandocMonad m => [Block] -> LW m (Doc Text)
blockListToSile lst =
  vsep `fmap` mapM (\b -> setEmptyLine True >> blockToSile b) lst

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

sectionHeader :: PandocMonad m
              => [Text]  -- classes
              -> Text
              -> Int
              -> [Inline]
              -> LW m (Doc Text)
sectionHeader classes id' level lst = do
  content <- inlineListToSile lst
  book <- gets stHasChapters
  opts <- gets stOptions
  let topLevelDivision = if book && writerTopLevelDivision opts == TopLevelDefault
                         then TopLevelChapter
                         else writerTopLevelDivision opts
  let level' = case topLevelDivision of
                      TopLevelPart    -> level - 2
                      TopLevelChapter -> level - 1
                      TopLevelSection -> level
                      TopLevelDefault -> level
  let level'' = T.pack $ show level'
  let sectionType = case level' of
                          -1 -> "part"
                          0  -> "chapter"
                          1  -> "section"
                          2  -> "subsection"
                          _  -> "sectionHeader"
  options <- toOptions id' classes [ ("level", level'') ]
  return $ inOptCmd sectionType options content

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
  content <- inlineListToSile ils
  let classToCommand = [ "csl-no-emph", "csl-no-strong", "csl-no-smallcaps" ]
  let cmds = filter (`elem` classToCommand) classes
  let classes' = filter (`notElem` classToCommand) classes
  options <- toOptions id' classes' kvs
  return $ if null cmds
            then inOptCmd "Span" options content
            else inOptCmd "Span" options $ foldr inCmd content cmds

inlineToSile (Emph lst) =
  inCmd "Emph" <$> inlineListToSile lst
inlineToSile (Strong lst) =
  inCmd "Strong" <$> inlineListToSile lst
inlineToSile (Strikeout lst) =
  inCmd "Strikeout" <$> inlineListToSile lst
inlineToSile (Superscript lst) =
  inCmd "Superscript" <$> inlineListToSile lst
inlineToSile (Subscript lst) =
  inCmd "textsubscript" <$> inlineListToSile lst
inlineToSile (SmallCaps lst) =
  inCmd "SmallCaps" <$> inlineListToSile lst
inlineToSile (Cite cits lst) = do
  st <- get
  let opts = stOptions st
  case writerCiteMethod opts of
     Natbib   -> citationsToNatbib cits
     _        -> inlineListToSile lst

inlineToSile (Code (_,_,_) str) =
  return $ "\\code{" <> literal str <> "}"
inlineToSile (Quoted SingleQuote lst) = do
  opts <- gets stOptions
  content <- inlineListToSile lst
  return $ if isEnabled Ext_smart opts
              then "‘" <> content <> "’"
              else "'" <> content <> "'"
inlineToSile (Quoted DoubleQuote lst) = do
  opts <- gets stOptions
  content <- inlineListToSile lst
  return $ if isEnabled Ext_smart opts
              then "“" <> content <> "”"
              else "\"" <> content <> "\""
inlineToSile (Str str) = do
  setEmptyLine False
  liftM literal $ stringToSile TextString str
inlineToSile (Math _ str) =
  return $ literal str
inlineToSile (RawInline _ str) = do
  setEmptyLine False
  return $ literal str
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
      content <- inlineListToSile txt
      lab <- toLabel ident
      return $ text "\\pdf:link" <> brackets ("dest=" <> literal lab) <> braces content
  | otherwise =
  case txt of
        [Str x] | unEscapeString (T.unpack x) == unEscapeString (T.unpack src) ->  -- autolink
             do src' <- stringToSile URLString (escapeURI src)
                return $ literal $ "\\url{" <> src' <> "}"
        [Str x] | Just rest <- T.stripPrefix "mailto:" src,
                  unEscapeString (T.unpack x) == unEscapeString (T.unpack rest) -> -- email autolink
             do src' <- stringToSile URLString (escapeURI src)
                content <- inlineListToSile txt
                return $ "\\href" <> braces (literal src') <>
                   braces ("\\url" <> braces content)
        _ -> do content <- inlineListToSile txt
                src' <- stringToSile URLString (escapeURI src)
                return $ literal ("\\href{" <> src' <> "}{") <> content <> char '}'
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
                -- return $ literal ("\\href" <> linkattrs <> braces content)
inlineToSile il@(Image _ _ (src, _))
  | Just _ <- T.stripPrefix "data:" src = do
  report $ InlineNotRendered il
  return empty
inlineToSile (Image _ _ (source, _)) = do
  setEmptyLine False
  let source' = if isURI source
                   then source
                   else T.pack $ unEscapeString $ T.unpack source
  source'' <- stringToSile URLString source'
  return $ "\\img" <> brackets ("src=" <> literal source'')
inlineToSile (Note content) = do
  setEmptyLine False
  contents' <- blockListToSile content
  let optnl = case reverse content of
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

