{-# language CPP #-}

module Linear.Common where

type a -. b =
#ifdef LINEAR
  a %1 -> b
#else
  a -> b
#endif

infixr 0 -.
