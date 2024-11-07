module R.M ( RM
           , nextN
           , nextU
           ) where

import           Control.Monad.Trans.State.Strict (State, state)
import qualified Data.Text                        as T
import           Nm
import           U

type RM = State Int

nextU :: T.Text -> a -> RM (Nm a)
nextU n l = state (\i -> let j=i+1 in (Nm n (U j) l, j))

nextN :: a -> RM (Nm a)
nextN = nextU "x"
