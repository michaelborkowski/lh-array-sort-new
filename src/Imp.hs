{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!
{-@ infixr <~  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Imp where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
-- import           Expressions -- hiding (And)

-------------------------------------------------------------------------------
-- | 1. The source language: IMP
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- | 1.1 Arithmetic Expressions 
-------------------------------------------------------------------------------

type Vname = String

data AExp  
  = N Val 
  | V Vname 
  | Plus  AExp AExp 
  | Minus AExp AExp 
  deriving (Show)

type Val   = Int 
type State = S.GState Vname Val -- should we use this?
type Reg = S.GState Int Val -- TODO: add LH constrains so that the index of the reg can only be Nat

{-@ reflect aval @-}
aval                :: AExp -> State -> Val 
aval (N n) _         = n 
aval (V x) s         = S.get s x 
aval (Plus  e1 e2) s = aval e1 s + aval e2 s
aval (Minus e1 e2) s = aval e1 s - aval e2 s
-- aval (Times e1 e2) s = aval e1 s * aval e2 s

{-@ reflect asgn @-}
asgn :: Vname -> AExp -> State -> State
asgn x a s = S.set s x (aval a s)


-- Three-Addressing Code
-- data Imm 
--   = R Int
--   | N Val 
--   | V Vname 

-- data TAExp 
--   = Imm Imm
--   | Plus  Imm Imm 
--   | Minus Imm Imm 
--   | Times Imm Imm 
--   deriving (Show)

-- {-@ reflect ival @-}
-- ival :: Imm -> Reg -> State -> Val
-- ival (N n) _ _ = n
-- ival (V x) _ s = S.get s x 
-- ival (R i) r _ = S.get r i 


-- {-@ reflect taval @-}
-- taval                :: TAExp -> Reg -> State -> Val 
-- taval (Imm i) r s       = ival i r s
-- taval (Plus  i1 i2) r s = ival i1 r s + ival i2 r s
-- taval (Minus i1 i2) r s = ival i1 r s - ival i2 r s
-- taval (Times i1 i2) r s = ival i1 r s * ival i2 r s


{-@ measure is_imm @-}
is_imm :: AExp -> Bool 
is_imm (N _) = True
is_imm (V _) = True
is_imm _     = False

{-@ measure is_TAC @-}
is_TAC :: AExp -> Bool 
is_TAC (Plus  a1 a2) = (is_imm a1) && (is_imm a2)
is_TAC (Minus a1 a2) = (is_imm a1) && (is_imm a2)
-- is_TAC (Times a1 a2) = (is_imm a1) && (is_imm a2) 
is_TAC _             = True

{-@ type TAExp = {a:AExp | is_TAC a} @-}


-------------------------------------------------------------------------------
-- | Boolean Expressions 
-------------------------------------------------------------------------------

data BExp 
  = Bc    Bool       -- true, false 
  | Not   BExp       -- not b 
  | And   BExp BExp  -- b1 && b2
  | Leq   AExp AExp  -- a1 <= a2 
  | Equal AExp AExp  -- a1 == a2 
  deriving (Show)

{-@ reflect .&&. @-}
(.&&.) :: BExp -> BExp -> BExp 
b1 .&&. b2 = And b1 b2 

{-@ reflect .=>. @-}
(.=>.) :: BExp -> BExp -> BExp 
b1 .=>. b2 = bImp b1 b2 

{-@ reflect bAnd @-}
bAnd :: BExp -> BExp -> BExp 
bAnd b1 b2 = And b1 b2 

{-@ reflect bIte @-}
bIte :: BExp -> BExp -> BExp -> BExp 
bIte p b1 b2 = And (bImp p b1) (bImp (Not p) b2)

{-@ reflect .==. @-}
(.==.) :: AExp -> AExp -> BExp 
b1 .==. b2 = Equal b1 b2 

{-@ reflect .<=. @-}
(.<=.) :: AExp -> AExp -> BExp 
b1 .<=. b2 = Leq b1 b2 

{-@ reflect bOr @-}
bOr :: BExp -> BExp -> BExp 
bOr b1 b2 = Not ((Not b1) `And` (Not b2))
       
{-@ reflect bImp @-}
bImp :: BExp -> BExp -> BExp 
bImp b1 b2 = bOr (Not b1) b2

{-@ reflect bLess @-}
bLess :: AExp -> AExp -> BExp 
bLess a1 a2 = And (Leq a1 a2) (Not (Equal a1 a2))

{-@ reflect tt @-}
tt :: BExp 
tt = Bc True 

{-@ reflect ff @-}
ff :: BExp 
ff = Bc False 

{-@ reflect bval @-}
bval :: BExp -> State -> Bool
bval (Bc   b)      _ = b 
bval (Not  b)      s = not (bval b s) 
bval (And  b1 b2)  s = bval b1 s && bval b2 s 
bval (Leq  a1 a2)  s = aval a1 s <= aval a2 s 
bval (Equal a1 a2) s = aval a1 s == aval a2 s 



--------------------------------------------------------------------------------
-- | IMP Commands
--------------------------------------------------------------------------------
data Com 
  = Skip                      -- skip 
  | Assign Vname AExp         -- x := a
  | Seq    Com   Com          -- c1; c2
  | If     BExp  Com   Com    -- if b then c1 else c2
  | While  BExp  Com          -- while b c 
  deriving (Show)

{-@ reflect <~ @-}
(<~) :: Vname -> AExp -> Com 
x <~ a = Assign x a 

{-@ reflect @@ @-}
(@@) :: Com -> Com -> Com 
s1 @@ s2 = Seq s1 s2

-- cexec property
data CExecP where
  CExec :: State -> Com -> State -> CExecP

data CExec where
  CExecSkip   :: State -> CExec
  CExecAssign :: State -> Vname -> AExp -> CExec
  CExecSeq    :: Com -> Com -> State -> State -> State -> CExec -> CExec -> CExec
  CExecIf     :: BExp -> Com -> Com -> State -> State -> CExec -> CExec
  CExecWhileD :: BExp -> Com -> State -> CExec -- while done
  CExecWhileL :: BExp -> Com -> State -> State -> State -> CExec -> CExec -> CExec -- while loop

{-@ data CExec  where 
      CExecSkip   :: s:_
                  -> Prop (CExec s Skip s)
      CExecAssign :: s:_ -> x:_ -> e:_
                  -> Prop (CExec s (Assign x e) (asgn x e s))
      CExecSeq    :: c1:_ -> c2:_ -> s0:_ -> s1:_ -> s2:_ -> Prop (CExec s0 c1 s1) -> Prop (CExec s1 c2 s2) 
                  -> Prop (CExec s0 (Seq c1 c2) s2)
      CExecIf     :: b:_ -> c1:_ -> c2:_ -> s0:_ -> s1:_ -> Prop (CExec s0 {if (bval b s0) then c1 else c2} s1) 
                  -> Prop (CExec s0 (If b c1 c2) s1)
      CExecWhileD :: b:_ -> c:_ -> s:{(bval b s) = False} 
                  -> Prop (CExec s (While b c) s)
      CExecWhileL :: b:_ -> c:_ -> s0:_ -> s1:_ -> s2:{(bval b s0) = True} -> Prop (CExec s0 c s1) -> Prop (CExec s1 (While b c) s2) 
                  -> Prop (CExec s0 (While b c) s2)
  @-} 

-- small-step sematic
