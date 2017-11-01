{-
Copyright (C) 2017 John MacFarlane <jgm@berkeley.edu>

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
   Module      : Text.Pandoc.Readers.Sile.Types
   Copyright   : Copyright (C) 2015-2017 Caleb Maclennan
   License     : GNU GPL, version 2 or above

   Maintainer  : Caleb Maclennan <caleb@alerque.com>
   Stability   : alpha
   Portability : portable

Types for Sile tokens and macros.
-}
module Text.Pandoc.Readers.Sile.Types ( Tok(..)
                                       , TokType(..)
                                       , SourcePos
                                       )
where
import Data.Text (Text)
import Text.Parsec.Pos (SourcePos)

data TokType = CtrlSeq Text | Spaces | Newline | Symbol | Word | Comment |
               Esc1    | Esc2   | Arg Int
     deriving (Eq, Ord, Show)

data Tok = Tok SourcePos TokType Text
     deriving (Eq, Ord, Show)
