module Nm.IntSet ( singleton, insert, member ) where

import qualified Data.IntSet as IS
import           Nm
import           U

singleton (Nm _ (U i) _) = IS.singleton i
insert (Nm _ (U i) _) = IS.insert i
member (Nm _ (U i) _) = IS.member i
