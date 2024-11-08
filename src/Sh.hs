{-# LANGUAGE DeriveGeneric #-}

module Sh (I (..), Sh (..)) where

import           Control.DeepSeq   (NFData)
import           GHC.Generics      (Generic)
import           Nm
import           Prettyprinter     (Pretty (pretty), group, parens, (<+>))
import           Prettyprinter.Ext

instance Pretty (I a) where pretty=ps 0

pg True=group.parens; pg False=id

instance PS (I a) where
    ps _ (Ix _ i)        = pretty i
    ps _ (IVar _ n)      = pretty n
    ps d (StaPlus _ i j) = parensp (d>5) (ps 6 i <+> "+" <+> ps 6 j)
    ps d (StaMul _ i j)  = parensp (d>7) (ps 8 i <+> "*" <+> ps 8 j)
    ps _ (IEVar _ n)     = "#" <> pretty n

data I a = Ix { ia :: a, ii :: !Int }
         | IVar { ia :: a, ixn :: Nm a }
         | IEVar { ia :: a , ie :: Nm a } -- existential
         | StaPlus { ia :: a, ix0, ix1 :: I a }
         | StaMul { ia :: a, ix0, ix1 :: I a }
         deriving (Functor, Generic)

infixr 8 `Cons`

data Sh a = Nil
          | SVar (Nm a)
          | Cons (I a) (Sh a)
          | Rev (Sh a)
          | Cat (Sh a) (Sh a)
          | Π (Sh a)
          deriving (Functor, Generic)

unroll Nil         = Just []
unroll (Cons i sh) = (i:)<$>unroll sh
unroll _           = Nothing

instance PS (Sh a) where
    ps _ (SVar n)    = pretty n
    ps _ sh@Cons{}   | Just is <- unroll sh = tupledBy " × " (pretty <$> is)
    ps d (Cons i sh) = pg (d>6) (pretty i <+> "`Cons`" <+> pretty sh)
    ps _ Nil         = "Nil"
    ps d (Cat s s')  = group (parensp (d>5) (ps 6 s <+> "⧺" <+> ps 6 s'))
    ps d (Rev s)     = parensp (d>appPrec) ("rev" <+> ps (appPrec+1) s)
    ps d (Π s)       = group (parensp (d>appPrec) ("Π" <+> ps (appPrec+1) s))

instance Pretty (Sh a) where pretty=ps 0

instance Show (I a) where show=show.pretty
instance Show (Sh a) where show=show.pretty

instance NFData a => NFData (I a) where
instance NFData a => NFData (Sh a) where
