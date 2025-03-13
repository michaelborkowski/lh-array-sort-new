{-# language CPP #-}

module Linear.Common where

type a -. b =
#ifdef LINEAR
--  a %1 -> b
  a -> b
#else
  a -> b
#endif

infixr 0 -.

infixl 1 &
{-# INLINE (&) #-}
(&) :: a -. ((a -. b) -> b)
a & b = b a

infixl 8 #
{-# INLINE (#) #-}
(#) :: (a -. b) -. ((b -. c) -. (a -. c))
(#) f g x = g (f x)
