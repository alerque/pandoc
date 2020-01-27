{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
module Tests.Writers.SILE (tests) where

import Prelude
import Data.Text (unpack)
import Test.Tasty
import Tests.Helpers
import Text.Pandoc
import Text.Pandoc.Arbitrary ()
import Text.Pandoc.Builder

sile :: (ToPandoc a) => a -> String
sile = sileWithOpts def

sileWithOpts :: (ToPandoc a) => WriterOptions -> a -> String
sileWithOpts opts = unpack . purely (writeSILE opts) . toPandoc

{-
  "my test" =: X =?> Y

is shorthand for

  test sile "my test" $ X =?> Y

which is in turn shorthand for

  test sile "my test" (X,Y)
-}

infix 4 =:
(=:) :: (ToString a, ToPandoc a)
     => String -> (a, String) -> TestTree
(=:) = test sile

tests :: [TestTree]
tests = [testGroup "code blocks"
          [ "in footnotes" =: note (para "hi" <> codeBlock "hi") =?>
            "\\footnote{hi\n\n  \\begin{verbatim}\n  hi\n  \\end{verbatim}\n}"
          ]
        , testGroup "definition lists"
          [ "with internal link" =: definitionList [(link "#go" "" (str "testing"),
             [plain (text "hi there")])] =?>
            "\\begin[tight=true]{DefinitionList}\n\\term{\\pdf:link[id=go]{testing}}\n\\definition{hi there}\n\\end{DefinitionList}"
          ]
        , testGroup "headers"
          [ "unnumbered header" =:
            headerWith ("foo",["unnumbered"],[]) 1
              (text "Header 1" <> note (plain $ text "note")) =?>
            "\\section[id=foo,classes=\"unnumbered\",level=1]{Header 1\\footnote{note}}"
          , "in list item" =:
            bulletList [header 2 (text "foo")] =?>
            "\\begin{listarea}\n\\listitem{\\subsection[level=2]{foo}}\n\\end{listarea}"
          , "in definition list item" =:
            definitionList [(text "foo", [header 2 (text "bar"),
                                          para $ text "baz"])] =?>
            "\\begin{DefinitionList}\n\\term{foo}\n\\definition{\\subsection[level=2]{bar}\n\nbaz}\n\\end{DefinitionList}"
          , "containing image" =:
            header 1 (image "imgs/foo.jpg" "" (text "Alt text")) =?>
            "\\section[level=1]{\\img[src=imgs/foo.jpg]{Alt text}}"
          ]
        ]
