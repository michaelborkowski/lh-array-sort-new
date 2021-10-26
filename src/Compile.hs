{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--compile-spec" @-}

{-@ infixr ++  @-}  
{-@ infixr <~  @-}  

{-# LANGUAGE GADTs #-}

module Compile where

import           Prelude hiding ((++), length, max)
import           ProofCombinators
import qualified State as S
import           Imp 
-- import           Expressions -- hiding (And)

-------------------------------------------------------------------------------
-- | 2. The target language: a register machine
-------------------------------------------------------------------------------

data List a = Nil | Cons a (List a)
  deriving (Eq, Show)

{-@ reflect app @-}
app :: List a -> List a -> List a 
app Nil ys         = ys 
app (Cons x xs) ys = Cons x (app xs ys)


-- copied from 230 wi19 notes
{-@ thm_app_assoc :: l1:_ -> l2:_ -> l3:_ -> { app (app l1 l2) l3 == app l1 (app l2 l3) } @-}
thm_app_assoc :: Code -> Code -> Code -> Proof
thm_app_assoc Nil ys zs
  = app (app Nil ys) zs
  === app ys zs 
  === app Nil (app ys zs) 
  *** QED

thm_app_assoc (Cons x xs) ys zs 
  = app (app (Cons x xs) ys) zs
  === app (Cons x (app xs ys)) zs 
  === Cons x (app (app xs ys) zs) 
    ? thm_app_assoc xs ys zs 
  === Cons x (app xs (app ys zs))
  === app (Cons x xs) (app ys zs)
  *** QED

{-@ measure length2 @-}
-- {-@ length2 :: l:_ -> Nat @-} -- weird bug with this line on TODO: 
length2 :: List a -> Int
length2 Nil        = 0
length2 (Cons _ xs) = (length2 xs) + 1


data Instr 
  = IConst Int Val                      -- assign ri with the value val
  | IVar Int Vname         -- assign ri with the value of vname
  | ISetvar Int Vname          -- assign vname with the value of ri
  | IAdd Int Int Int   -- set vname to be the value of the sum of two imms 
  | ISub Int Int Int   -- set vname to be the value of the difference of two imms 
  | IBranch Val      -- skip forward or backward this number of instructions
  | IBeq Int Int Val Val -- pop two integers, skip the first number of instructions if they are equal, otherwise skip the second number of instructions
  | IBle Int Int Val Val -- pop two integers, skip the first number of instructions if the first integer is less than or equal to the second, otherwise skip the second number of instructions
  | IHalt
  deriving (Show)


type Code = List Instr -- should i use built-in list?

-- Why cant just do "codelen = length" ?
{-@ measure codelen @-}
{-@ codelen :: Code -> Nat @-}
codelen :: Code -> Int
codelen Nil        = 0
codelen (Cons _ xs) = (codelen xs) + 1

-- Might have some problem here
{-@ reflect instr_at @-}
instr_at :: Code -> Int -> Maybe Instr
instr_at Nil _ = Nothing
instr_at (Cons x xs) 0 = Just x
instr_at (Cons _ xs) i = instr_at xs (i-1)

type Stack = List Int


data Config = Conf Int Reg State -- datatype

testconfig :: Int
testconfig = 2
-- {-@ testconfig :: a:{b:Int | b == 1+1} @-}

{-@ reflect increase_pc @-}
-- {-@ increase_pc :: Nat -> Nat @-}
increase_pc :: Int -> Int
increase_pc n = n+1

{-@ reflect myplus @-}
myplus :: Int -> Int -> Int
myplus n1 n2 = n1+n2

{-@ reflect myinverse @-}
myinverse :: Int -> Int
myinverse n = -n



-- base small step cases in running Instr
data ISStepP where
  ISStep :: Code -> Config -> Config -> ISStepP 

data ISStep where
  ISConst   :: Code -> Int -> Reg -> State -> Int -> Val -> ISStep
  ISVar     :: Code -> Int -> Reg -> State -> Int -> Vname -> ISStep
  ISSetvar  :: Code -> Int -> Reg -> State -> Int -> Vname -> ISStep
  ISAdd     :: Code -> Int -> Reg -> State -> Int -> Int -> Int -> ISStep
  ISSub     :: Code -> Int -> Reg -> State -> Int -> Int -> Int -> ISStep
  ISBranch  :: Code -> Int -> Reg -> State -> Int -> Int -> ISStep
  ISBeq     :: Code -> Int -> Reg -> State -> Int -> Int -> Int -> Int -> Int -> ISStep
  ISBle     :: Code -> Int -> Reg -> State -> Int -> Int -> Int -> Int -> Int -> ISStep


-- parse error when replace increase_pc pc with pc+1, as well as myplus
{-@ data ISStep  where 
      ISConst   :: c:_ -> pc:_ -> reg:_ -> s:_ -> r:_ -> n:{instr_at c pc = Just (IConst r n)}
                -> Prop (ISStep c
                                (Conf pc reg s) 
                                (Conf {pc + 1} (S.set reg r n) s) ) 
      ISVar     :: c:_ -> pc:_ -> reg:_ -> s:_ -> r:_ -> x:{instr_at c pc = Just (IVar r x)}
                -> Prop (ISStep c
                                (Conf pc reg s) 
                                (Conf {pc + 1} (S.set reg r (S.get s x)) s) ) 
      ISSetvar  :: c:_ -> pc:_ -> reg:_ -> s:_ -> r:_ -> x:{instr_at c pc = Just (ISetvar r x)}
                -> Prop (ISStep c
                                (Conf pc reg s) 
                                (Conf {pc + 1} reg (S.set s x (S.get reg r))) ) 
      ISAdd     :: c:_ -> pc:_ -> reg:_ -> s:_ -> t:_ -> r1:_ -> r2:{instr_at c pc = Just (IAdd t r1 r2)}
                -> Prop (ISStep c
                                (Conf pc reg s) 
                                (Conf {pc + 1} (S.set reg t {(S.get reg r1) + (S.get reg r2)}) s) ) 
      ISSub     :: c:_ -> pc:_ -> reg:_ -> s:_ -> t:_ -> r1:_ -> r2:{instr_at c pc = Just (ISub t r1 r2)}
                -> Prop (ISStep c
                                (Conf pc reg s) 
                                (Conf {pc + 1} (S.set reg t {(S.get reg r1) - (S.get reg r2)}) s) ) 
      ISBranch  :: c:_ -> pc:_ -> reg:_ -> s:_ -> d:_ -> pc':{ pc' == pc + 1 + d && instr_at c pc = Just (IBranch d)}
                -> Prop (ISStep c
                                (Conf pc reg s) 
                                (Conf pc' reg s) ) 
      ISBeq     :: c:_ -> pc:_ -> reg:_ -> s:_ -> r1:_ -> r2:_ -> d1:_ -> d2:_ 
                -> pc':{ pc' = pc + 1 + (if ((S.get reg r1) == (S.get reg r2)) then d1 else d2) && instr_at c pc = Just (IBeq r1 r2 d1 d2) }
                -> Prop (ISStep c
                                (Conf pc  reg s) 
                                (Conf pc' reg s) ) 
      ISBle     :: c:_ -> pc:_ -> reg:_ -> s:_ -> r1:_ -> r2:_ -> d1:_ -> d2:_ 
                -> pc':{ pc' = pc + 1 + (if ((S.get reg r1) <= (S.get reg r2)) then d1 else d2) && instr_at c pc = Just (IBle r1 r2 d1 d2) }
                -> Prop (ISStep c
                                (Conf pc  reg s) 
                                (Conf pc' reg s) ) 
  @-} 




-- small steps
data ISStepsP where
  ISSteps :: Code -> Config -> Config -> ISStepsP

data ISSteps where
  IRefl :: Code -> Config -> ISSteps
  IEdge :: Code -> Config -> Config -> Config -> ISStep -> ISSteps -> ISSteps

{-@  data ISSteps where
        IRefl :: c:_ -> s:_ -> Prop (ISSteps c s s)
        IEdge :: c:_ -> s1:_ -> s2:_ -> s3:_
             -> Prop (ISStep c s1 s2)
             -> Prop (ISSteps c s2 s3)
             -> Prop (ISSteps c s1 s3)
  @-}



{-@ lem_one_ssteps :: c:_ -> s1:_ -> s2:_ 
        -> Prop (ISStep c s1 s2) 
        -> Prop (ISSteps c s1 s2) 
  @-}
lem_one_ssteps :: Code -> Config -> Config -> ISStep -> ISSteps
lem_one_ssteps c s1 s2 pf = IEdge c s1 s2 s2 pf (IRefl c s2)


{-@ lem_many_ssteps :: c:_ -> s1:_ -> s2:_ -> s3:_
        -> Prop (ISSteps c s1 s2) 
        -> Prop (ISSteps c s2 s3) 
        -> Prop (ISSteps c s1 s3) 
  @-}
lem_many_ssteps :: Code -> Config -> Config -> Config -> ISSteps -> ISSteps -> ISSteps
lem_many_ssteps c s1 s2 s3 (IRefl {}) c23 = c23
lem_many_ssteps c s1 s2 s3 (IEdge _ _ m _ c1m cm2) c23 
  = IEdge c s1 m s3 c1m (lem_many_ssteps c m s2 s3 cm2 c23)

-- This is just a helper function that makes the code clearer
{-@ lem_three_ssteps :: c:_ -> s1:_ -> s2:_ -> s3:_ -> s4:_
        -> Prop (ISSteps c s1 s2) 
        -> Prop (ISSteps c s2 s3) 
        -> Prop (ISSteps c s3 s4)
        -> Prop (ISSteps c s1 s4) 
  @-}
lem_three_ssteps :: Code -> Config -> Config -> Config -> Config -> ISSteps -> ISSteps -> ISSteps -> ISSteps
lem_three_ssteps c s1 s2 s3 s4 c12 c23 c34 
  = lem_many_ssteps c s1 s2 s4 c12 (lem_many_ssteps c s2 s3 s4 c23 c34)

{-@ lem_four_ssteps :: c:_ -> s1:_ -> s2:_ -> s3:_ -> s4:_ -> s5:_
        -> Prop (ISSteps c s1 s2) 
        -> Prop (ISSteps c s2 s3) 
        -> Prop (ISSteps c s3 s4)
        -> Prop (ISSteps c s4 s5)
        -> Prop (ISSteps c s1 s5) 
  @-}
lem_four_ssteps :: Code -> Config -> Config -> Config -> Config -> Config -> ISSteps -> ISSteps -> ISSteps -> ISSteps -> ISSteps
lem_four_ssteps c s1 s2 s3 s4 s5 c12 c23 c34 c45
  = lem_three_ssteps c s1 s2 s3 s5 c12 c23 (lem_many_ssteps c s3 s4 s5 c34 c45)


-- {-@ type NilConfig pc s = (Conf pc Nil s) @-}

-- data NilConfig pc s = Conf pc Nil s

-- LH treats _ as space TODO:
{-@ type MachineTerminates C si sf = 
      ( pc : { v:Int | instr_at C v == Just Ihalt }, 
        Prop (ISSteps C (Conf 0 Nil si) (Conf pc Nil sf))
      ) 
  @-}

type MachineTerminates = (Int, ISSteps)



{-@ reflect compile_AExp @-}
compile_AExp :: Int -> AExp -> Code -- r the is currently available register
compile_AExp r (N n) = Cons (IConst r n) Nil
compile_AExp r (V x) = Cons (IVar r x) Nil
compile_AExp r (Plus e1 e2) = app (compile_AExp (r+1) e1) (app (compile_AExp (r+2) e2) (Cons (IAdd r (r+1) (r+2)) Nil)) 
compile_AExp r (Minus e1 e2) = app (compile_AExp (r+1) e1) (app (compile_AExp (r+2) e2) (Cons (ISub r (r+1) (r+2)) Nil)) 
-- compile_AExp r (Times e1 e2) = app (compile_AExp (r+1) e1) (app (compile_AExp (r+2) e2) (Cons (ISub r (r+1) (r+2)) Nil)) 
-- compile_AExp (Times e1 e2) = app (app (compile_AExp e1) (compile_AExp e2)) (Cons IAdd Nil)





{- For Boolean expressions [b], we could produce code that deposits [1] or [0]
  at the top of the stack, depending on whether [b] is true or false.
  The compiled code for [IFTHENELSE] and [WHILE] commands would, then,
  compare this 0/1 value against 0 and branch to the appropriate piece of code.

  However, it is simpler and more efficient to compile a Boolean expression [b]
  to a piece of code that directly jumps [d1] or [d0] instructions forward,
  depending on whether [b] is true or false.  The actual value of [b] is
  never computed as an integer, and the stack is unchanged. 
  -}


{-@ reflect compile_BExp @-}
compile_BExp :: BExp -> Int -> Int -> Code
compile_BExp (Bc b) d1 d2 = if b then (if d1 == 0 then Nil else (Cons (IBranch d1) Nil)) else (if d2 == 0 then Nil else (Cons (IBranch d2) Nil))
compile_BExp (Not b) d1 d2 = compile_BExp b d2 d1
compile_BExp (And b1 b2) d1 d2 =  let code2 = compile_BExp b2 d1 d2 
                                      code1 = compile_BExp b1 0 (codelen code2 + d2)
                                  in app code1 code2
compile_BExp (Leq e1 e2) d1 d2 = app (compile_AExp 0 e1) (app (compile_AExp 1 e2) (Cons (IBle 0 1 d1 d2) Nil))
compile_BExp (Equal e1 e2) d1 d2 = app (compile_AExp 0 e1) (app (compile_AExp 1 e2) (Cons (IBeq 0 1 d1 d2) Nil))



{-@ reflect compile_Com @-}
compile_Com :: Com -> Code
compile_Com (Skip) = Nil
compile_Com (Assign x e) = app (compile_AExp 0 e) (Cons (ISetvar 0 x) Nil)
compile_Com (Seq c1 c2) = app (compile_Com c1) (compile_Com c2)
compile_Com (If b c1 c2) =  let code1 = compile_Com c1
                                code2 = compile_Com c2
                            in app (compile_BExp b 0 (codelen code1 + 1)) (app code1  (Cons (IBranch (codelen code2)) code2))
compile_Com (While b c) = let codeC = compile_Com c 
                              codeB = compile_BExp b 0 (codelen codeC + 1)
                              lenC  = codelen codeC
                              lenB  = codelen codeB
                          in app codeB (app codeC (Cons (IBranch (-(lenC + lenB + 1))) Nil))

{-@ reflect compileProgram @-}
compileProgram :: Com -> Code
compileProgram p = app (compile_Com p) (Cons IHalt Nil)


data CodeAtP where
  CodeAt :: Code -> Int -> Code -> CodeAtP

data CodeAt where
  CodeAtIntro :: Code -> Code -> Code -> Int -> CodeAt

{-@ data CodeAt  where 
      CodeAtIntro :: c1:_ -> c2:_ -> c3:_ -> pc:{ pc = codelen c1} 
                  -> Prop (CodeAt (app c1 (app c2 c3)) pc c2)
  @-} 

-- BY DEFINITION
-- {-@ lem_codelen_cons :: i:_ -> c:_ -> 
--         -> {codelen (Cons i c) = codelen c + 1}
--   @-}
-- lem_codelen_cons :: Instr -> Code -> Proof
-- lem_codelen_cons i Nil 
--   = codelen (Cons i Nil)
--   === 1 + codelen Nil
--   === 1 + 0
--   === 1
--   === 0 + 1
--   === codelen Nil + 1
--   *** QED

-- lem_codelen_cons i (Cons x xs)
--   = codelen (Cons i (Cons x xs))
--   === 1 + (codelen (Cons x xs))
--     ? 
--   === 1 + (codelen xs + 1)
--   === 1 + (codelen (Cons ))
--   === 
--   === codelen (Cons x xs) + 1



{-@ lem_codelen_app :: c1:_ -> c2:_
        -> {codelen (app c1 c2) = (codelen c1) + (codelen c2)}
  @-}
lem_codelen_app :: Code -> Code -> Proof
lem_codelen_app Nil c2
  = codelen (app Nil c2)
  === codelen c2
  === (codelen Nil) + (codelen c2)
  *** QED

lem_codelen_app (Cons x xs) c2
  = codelen (app (Cons x xs) c2)
  === codelen (Cons x (app xs c2))
  === 1 + (codelen (app xs c2))
    ? lem_codelen_app xs c2
  === 1 + ((codelen xs) + (codelen c2))
  === (codelen (Cons x xs)) + (codelen c2)
  *** QED



{-@ lem_instr_at_app :: pc:_ -> i:_ -> c1:_ -> c2:{pc = codelen c1} 
        -> {instr_at (app c1 (Cons i c2)) pc == Just i}
  @-}
lem_instr_at_app :: Int -> Instr -> Code -> Code -> Proof
lem_instr_at_app 0 i Nil c2
  = instr_at (app Nil (Cons i c2)) 0
  === instr_at (Cons i c2) 0
  === Just i
  *** QED

lem_instr_at_app pc i (Cons x xs) c2
  = let ys = (app xs (Cons i c2))
    in instr_at (app (Cons x xs) (Cons i c2)) pc
  === instr_at (Cons x ys) pc
  === instr_at ys (pc-1)
    ? lem_instr_at_app (pc-1) i xs c2
  === Just i
  *** QED

-- c = c1 c2 c3 = c1 (cons i c') c3 = c1 (cons i c'') | c'' = app c' c3
{-@ lem_code_at_head :: c:_ -> pc:_ -> i:_ -> c':_ -> Prop (CodeAt c pc (Cons i c'))
        -> {instr_at c pc == Just i}
  @-}
lem_code_at_head ::  Code -> Int -> Instr -> Code -> CodeAt -> Proof
lem_code_at_head c pc i c' (CodeAtIntro c1 c2 c3 _pc) 
  = lem_instr_at_app pc i c1 (app c' c3)

-- (Cons i Nil) = Cons i (app Nil Nil) = app (Cons i Nil) Nil
-- app c1 (app (Cons i Nil) (app c' c3)) = app c1 (Cons i (app ))
-- app (app c1 (Cons i Nil)) (app c' c3) =? app c1 (app (Cons i c') c3) 
--   = app c1 (Cons i (app c' c3))
{-@ lem_code_at_tail :: c:_ -> pc:_ -> i:_ -> c':_ -> Prop (CodeAt c pc (Cons i c'))
        -> Prop (CodeAt c {pc + 1} c')
  @-}
lem_code_at_tail ::  Code -> Int -> Instr -> Code -> CodeAt -> CodeAt
lem_code_at_tail c pc i c' (CodeAtIntro c1 c2 c3 _pc) 
  = CodeAtIntro (app c1 (Cons i Nil)) c' c3 n ? (thm_app_assoc c1 (Cons i Nil) (app c' c3))
    where
      {-@ n :: m:{m = (codelen (app c1 (Cons i Nil)))} @-}
      n = ((pc + 1) ? (lem_codelen_app c1 (Cons i Nil)))


-- c   = (app c1' (app c2' c3')) = (app c1' (app (app c1 c2) c3')) 
--     =? app c1' (app c1 (app c2 c3')) 
-- c2' = (app c1 c2)
{-@ lem_code_at_app_left :: c:_ -> pc:_ -> c1:_ -> c2:_ -> Prop (CodeAt c pc (app c1 c2))
        -> Prop (CodeAt c pc c1)
  @-}
lem_code_at_app_left :: Code -> Int -> Code -> Code -> CodeAt -> CodeAt
lem_code_at_app_left c pc c1 c2 (CodeAtIntro c1' c2' c3' _pc) 
  = (CodeAtIntro c1' c1 (app c2 c3') pc) 
    ? (thm_app_assoc c1 c2 c3')

-- c   = (app c1' (app c2' c3')) = c1' ++ c1 ++ c2 ++ c3' = (app c1' (app (app c1 c2) c3')) 
--     =? app (app c1' c1) (app c2 c3')
-- c2' = (app c1 c2)
{-@ lem_code_at_app_right :: c:_ -> pc:_ -> c1:_ -> c2:_ -> Prop (CodeAt c pc (app c1 c2))
        -> Prop (CodeAt c {pc + (codelen c1)} c2)
  @-}
lem_code_at_app_right :: Code -> Int -> Code -> Code -> CodeAt -> CodeAt
lem_code_at_app_right c pc c1 c2 (CodeAtIntro c1' c2' c3' _pc) 
  = (CodeAtIntro (app c1' c1) c2 c3' (pc + (codelen c1))) 
    ? (lem1 &&& lem2)
    where 
      {-@ lem1 :: { (app c1' (app (app c1 c2) c3')) = app (app c1' c1) (app c2 c3') } @-}
      lem1 = (thm_app_assoc c1 c2 c3') &&& (thm_app_assoc c1' c1 (app c2 c3'))
      {-@ lem2 :: { codelen (app c1' c1) = pc + (codelen c1) } @-}
      lem2 = lem_codelen_app c1' c1


-- helper functions that combines app_left and app_right
-- c   = (app c1' (app c2' c3')) = c1' ++ c1 ++ c2 ++ c3 ++ c3' = (app c1' (app (app c1 c2) c3')) 
--     =? app (app c1' c1) (app c2 c3')
-- c2' = (app c1 (app c2 c3))
-- Prop (CodeAt c {pc + (codelen c1)} c2)
{-@ lem_code_at_app_mid :: c:_ -> pc:_ -> c1:_ -> c2:_ -> c3:_ -> Prop (CodeAt c pc (app c1 (app c2 c3)) )
        -> Prop (CodeAt c {pc + (codelen c1)} c2)
  @-}
lem_code_at_app_mid :: Code -> Int -> Code -> Code -> Code -> CodeAt -> CodeAt
lem_code_at_app_mid c pc c1 c2 c3 ca@(CodeAtIntro c1' c2' c3' _pc) 
  = lem_code_at_app_left c (pc + (codelen c1)) c2 c3 (lem_code_at_app_right c pc c1 (app c2 c3) ca)


-- reg_after_AExp :: Reg -> State -> Int -> AExp -> Reg
-- reg_after_AExp reg r s (N n) = (S.set reg r n)
-- reg_after_AExp reg r s (V x) = (S.set reg r (S.get s x))
-- reg_after_AExp reg r s (Plus e1 e2) = (S.set reg r (S.get s x))


{-@ reflect reg_after_Code @-}
{-@ reg_after_Code :: c:_ -> pc:_ -> l:Nat -> reg:_ -> s:_ -> reg':_ / [l] @-}
reg_after_Code :: Code -> Int -> Int -> Reg -> State -> Reg
reg_after_Code _ _ 0 reg _ = reg
reg_after_Code c pc l reg s 
  = let 
      reg' = case (instr_at c pc) of
        Just (IConst r n) -> (S.set reg r n)
        Just (IVar r x) -> (S.set reg r (S.get s x))
        Just (ISetvar r x) -> reg
        Just (IAdd t r1 r2) -> (S.set reg t ((S.get reg r1) + (S.get reg r2)))
        Just (ISub t r1 r2) -> (S.set reg t ((S.get reg r1) - (S.get reg r2)))
        Just (IBranch d) -> reg
        Just (IBeq r1 r2 d1 d2) -> reg
        Just (IBle r1 r2 d1 d2) -> reg
        _ -> reg
    in reg_after_Code c (pc+1) (l-1) reg' s



-- reg' = 

-- idea: if for all reg, reg', r such that reg' and reg agrees on all 0 <= t < r and reg' at r equals aval e, then we have the desired property
-- we need a proper reg' to fill in the second Conf in the returned Prop
-- 
{-@ lem_compile_AExp_correct :: c:_ -> pc:_ -> reg:_ -> s:_ -> r:_ -> e:_ -> Prop (CodeAt c pc (compile_AExp r e))
        -> Prop (ISSteps c (Conf pc reg s) 
                           (Conf {pc + (codelen (compile_AExp r e))} (reg_after_Code c pc (codelen (compile_AExp r e)) reg s) s))
  @-}
lem_compile_AExp_correct :: Code -> Int -> Reg -> State -> Int -> AExp -> CodeAt -> ISSteps
lem_compile_AExp_correct c pc reg s r (N n) ca 
  = let 
      s1 = Conf pc reg s
      s2 = Conf (pc + 1) (S.set reg r n) s
    in lem_one_ssteps c s1 s2 (ISConst c pc reg s r (n ? (lem_code_at_head c pc (IConst r n) Nil ca))) 

lem_compile_AExp_correct c pc reg s r (V x) ca 
  = let 
      s1 = Conf pc reg s
      s2 = Conf (pc + 1) (S.set reg r (S.get s x)) s
    in lem_one_ssteps c s1 s2 (ISVar c pc reg s r (x ? (lem_code_at_head c pc (IVar r x) Nil ca))) 


-- c  = app c1 (app c2 c3)
-- c2 = compile_AExp e = c_AE e1 ++ c_AE e2 ++ IAdd
lem_compile_AExp_correct c pc reg s r (Plus e1 e2) ca
  = let 
      e1_cod = (compile_AExp (r+1) e1)
      e2_cod = (compile_AExp (r+2) e2)
      ex_cod = (Cons (IAdd r (r+1) (r+2)) Nil) -- extra code
      e1_len = (codelen e1_cod)
      e2_len = (codelen e2_cod)
      e1_val = (aval e1 s)
      e2_val = (aval e2 s)
      reg1   = (reg_after_Code c pc e1_len reg s)
      reg2   = (reg_after_Code c (pc + e1_len) e2_len reg1 s)
      reg3   = (reg_after_Code c (pc + e1_len + e2_len) 1 reg2 s)
      s1     = Conf pc reg s
      s2     = Conf (pc + e1_len) reg1 s
      s3     = Conf (pc + e1_len + e2_len) reg2 s
      s4     = Conf (pc + e1_len + e2_len + 1) reg3 s
      c12    = lem_compile_AExp_correct c pc reg s (r+1) e1 ca_e1
                where 
                  {-@ ca_e1 :: Prop (CodeAt c pc e1_cod) @-}
                  ca_e1  = lem_code_at_app_left c pc e1_cod (app e2_cod ex_cod) ca
      c23    = lem_compile_AExp_correct c (pc + e1_len) reg1 s (r+2) e2 ca_e2
                where
                  {-@ ca_e2 :: Prop (CodeAt c {pc + e1_len} e2_cod) @-}
                  ca_e2  = lem_code_at_app_mid c pc e1_cod e2_cod ex_cod ca
      c34    = lem_one_ssteps c s3 s4 ((ISAdd c (pc + e1_len + e2_len) reg2 s r (r+1) (r+2)) 
                ? pf_instr_at_add)
                where 
                  ca_c_npc_add = (lem_code_at_app_right c pc (app e1_cod e2_cod) ex_cod (ca ? (thm_app_assoc e1_cod e2_cod ex_cod))) ? (lem_codelen_app e1_cod e2_cod)
                  pf_instr_at_add = (lem_code_at_head c (pc + e1_len + e2_len) (IAdd r (r+1) (r+2)) Nil ca_c_npc_add)
      in (lem_three_ssteps c s1 s2 s3 s4 c12 c23 c34) ? ((lem_codelen_app e1_cod (app e2_cod ex_cod)) &&& (lem_codelen_app e2_cod ex_cod))
lem_compile_AExp_correct _ _ _ _ _ _ _ = undefined
{- 
lem_compile_AExp_correct c pc stk s (Minus e1 e2) ca
  = let 
      e1_cod = (compile_AExp e1)
      e2_cod = (compile_AExp e2)
      ex_cod = (Cons IOpp (Cons IAdd Nil)) -- extra code
      e1_len = (codelen e1_cod)
      e2_len = (codelen e2_cod)
      e1_val = (aval e1 s)
      e2_val = (aval e2 s)
      s1     = Conf pc stk s
      s2     = Conf (pc + e1_len) (Cons e1_val stk) s
      s3     = Conf (pc + e1_len + e2_len) (Cons e2_val (Cons e1_val stk)) s
      s4     = Conf (pc + e1_len + e2_len + 2) (Cons (e1_val - e2_val) stk) s
      c12    = lem_compile_AExp_correct c pc stk s e1 ca_e1
                where 
                  {-@ ca_e1 :: Prop (CodeAt c pc e1_cod) @-}
                  ca_e1  = lem_code_at_app_left c pc e1_cod (app e2_cod ex_cod) ca
      c23    = lem_compile_AExp_correct c (pc + e1_len) (Cons e1_val stk) s e2 ca_e2
                where
                  {-@ ca_e2 :: Prop (CodeAt c {pc + e1_len} e2_cod) @-}
                  ca_e2  = lem_code_at_app_mid c pc e1_cod e2_cod ex_cod ca
      {-@ c34 :: Prop (ISSteps c s3 s4) @-}
      c34    = lem_many_ssteps c s3 m s4 c3m cm4
                where
                  m   = Conf (pc + e1_len + e2_len + 1) (Cons (- e2_val) (Cons e1_val stk)) s
                  c3m = lem_one_ssteps c s3 m (ISOpp c (pc + e1_len + e2_len) (Cons e1_val stk) s e2_val ? pf_instr_at_opp)
                  cm4 = lem_one_ssteps c m s4 ((ISAdd c (pc + e1_len + e2_len + 1) stk s (-e2_val) e1_val) ? pf_instr_at_add)
                  {-@ pf_instr_at_opp :: {instr_at c (pc + e1_len + e2_len) = Just (IOpp)} @-}
                  {-@ pf_instr_at_add :: {instr_at c (pc + e1_len + e2_len + 1) = Just (IAdd)} @-}
                  {-@ ca_ex_code      :: Prop (CodeAt c {pc + e1_len + e2_len} ex_cod)  @-}
                  {-@ ca_add          :: Prop (CodeAt c {pc + e1_len + e2_len + 1} (Cons IAdd Nil))  @-}
                  pf_instr_at_opp = lem_code_at_head c (pc + e1_len + e2_len) (IOpp) (Cons IAdd Nil) ca_ex_code
                  pf_instr_at_add = lem_code_at_head c (pc + e1_len + e2_len + 1) (IAdd) Nil ca_add
                  ca_ex_code      = (lem_code_at_app_right c pc (app e1_cod e2_cod) ex_cod (ca ? (thm_app_assoc e1_cod e2_cod ex_cod))) ? (lem_codelen_app e1_cod e2_cod)
                  ca_add          = lem_code_at_tail c (pc + e1_len + e2_len) (IOpp) (Cons IAdd Nil) ca_ex_code
    in (lem_three_ssteps c s1 s2 s3 s4 c12 c23 c34) ? ((lem_codelen_app e1_cod (app e2_cod ex_cod)) &&& (lem_codelen_app e2_cod ex_cod))



-- {-@ LIQUID "--checks=lem_compile_BExp_correct" @-}
{-@ lem_compile_BExp_correct :: c:_ -> pc:_ -> stk:_ -> s:_ -> b:_ -> d1:_ -> d2:_ -> Prop (CodeAt c pc (compile_BExp b d1 d2))
        -> Prop (ISSteps c (Conf pc stk s) 
                           (Conf {pc + (codelen (compile_BExp b d1 d2)) + ( if (bval b s) then d1 else d2 ) } stk s))
  @-}
lem_compile_BExp_correct :: Code -> Int -> Stack -> State -> BExp -> Int -> Int -> CodeAt -> ISSteps
lem_compile_BExp_correct c pc stk s (Bc True) 0 d2 ca
  = IRefl c (Conf pc stk s) 
lem_compile_BExp_correct c pc stk s (Bc True) d1 d2 ca
  = let
      s1 = (Conf pc stk s)
      s2 = (Conf (pc + d1 + 1) stk s)
    in lem_one_ssteps c s1 s2 (ISBranch c pc stk s d1 ((pc+1+d1) ? (lem_code_at_head c pc (IBranch d1) Nil ca))) 
lem_compile_BExp_correct c pc stk s (Bc False) d1 0 ca
  = IRefl c (Conf pc stk s) 
lem_compile_BExp_correct c pc stk s (Bc False) d1 d2 ca
  = let
      s1 = (Conf pc stk s)
      s2 = (Conf (pc + d2 + 1) stk s)
    in lem_one_ssteps c s1 s2 (ISBranch c pc stk s d2 ((pc+1+d2) ? (lem_code_at_head c pc (IBranch d2) Nil ca))) 
    
lem_compile_BExp_correct c pc stk s (Not b) d1 d2 ca
  = lem_compile_BExp_correct c pc stk s b d2 d1 ca

lem_compile_BExp_correct c pc stk s (And b1 b2) d1 d2 ca
  = let
      b1_cod = compile_BExp b1 0 (b2_len + d2)
      b2_cod = compile_BExp b2 d1 d2
      b1_len = codelen b1_cod
      b2_len = codelen b2_cod
      b1_val = bval b1 s
      b2_val = bval b2 s
      s1 = (Conf pc stk s)

      {-@ ca_b1 :: Prop (CodeAt c pc b1_cod) @-}
      {-@ ca_b2 :: Prop (CodeAt c {pc + b1_len} b2_cod) @-}
      ca_b1 = lem_code_at_app_left c pc b1_cod b2_cod ca
      ca_b2 = lem_code_at_app_right c pc b1_cod b2_cod ca
    in case (b1_val, b2_val) of 
      (False,  _    ) -> lem_compile_BExp_correct c pc stk s b1 0 (b2_len + d2) ca_b1 ? (lem_codelen_app b1_cod b2_cod)
      (True ,  False) -> lem_many_ssteps c s1 s2 s3 c12 c23 ? (lem_codelen_app b1_cod b2_cod)
        where 
          s2  = (Conf (pc + b1_len) stk s)
          s3  = (Conf (pc + b1_len + b2_len + d2) stk s)
          c12 = lem_compile_BExp_correct c pc stk s b1 0 (b2_len + d2) ca_b1
          c23 = lem_compile_BExp_correct c (pc + b1_len) stk s b2 d1 d2 ca_b2
      (True ,  True ) -> lem_many_ssteps c s1 s2 s3 c12 c23 ? (lem_codelen_app b1_cod b2_cod)
        where 
          s2  = (Conf (pc + b1_len) stk s)
          s3  = (Conf (pc + b1_len + b2_len + d1) stk s)
          c12 = lem_compile_BExp_correct c pc stk s b1 0 (b2_len + d2) ca_b1
          c23 = lem_compile_BExp_correct c (pc + b1_len) stk s b2 d1 d2 ca_b2
          
lem_compile_BExp_correct c pc stk s (Leq e1 e2) d1 d2 ca
  = let 
      e1_cod = compile_AExp e1
      e2_cod = compile_AExp e2
      ex_cod = Cons (IBle d1 d2) Nil -- extra code
      e1_len = codelen e1_cod
      e2_len = codelen e2_cod
      e1_val = aval e1 s
      e2_val = aval e2 s
      s1     = Conf pc stk s
      s2     = Conf (pc + e1_len) (Cons e1_val stk) s
      s3     = Conf (pc + e1_len + e2_len) (Cons e2_val (Cons e1_val stk)) s
      s4     = Conf (pc + e1_len + e2_len + 1 + (if (e1_val <= e2_val) then d1 else d2)) stk s
      c12    = lem_compile_AExp_correct c pc stk s e1 ca_e1
                where 
                  {-@ ca_e1 :: Prop (CodeAt c pc e1_cod) @-}
                  ca_e1  = lem_code_at_app_left c pc e1_cod (app e2_cod ex_cod) ca
      c23    = lem_compile_AExp_correct c (pc + e1_len) (Cons e1_val stk) s e2 ca_e2
                where
                  {-@ ca_e2 :: Prop (CodeAt c {pc + e1_len} e2_cod) @-}
                  ca_e2  = lem_code_at_app_mid c pc e1_cod e2_cod ex_cod ca
      c34    = lem_one_ssteps c s3 s4 isble
                where 
                  {-@ isble  :: Prop (ISStep c s3 s4) @-}
                  -- {-@ ia_ble :: { instr_at c pc == Just (IBle d1 d2) } @-} -- TODO: wried bug
                  {-@ ca_ble :: Prop (CodeAt c {pc + e1_len + e2_len} ex_cod)  @-}
                  isble  = (ISBle c (pc + e1_len + e2_len) stk s d1 d2 e1_val e2_val (pc + e1_len + e2_len + 1 + (if (e1_val <= e2_val) then d1 else d2))) ? ia_ble
                  ca_ble = (lem_code_at_app_right c pc (app e1_cod e2_cod) ex_cod (ca ? (thm_app_assoc e1_cod e2_cod ex_cod))) ? (lem_codelen_app e1_cod e2_cod)
                  ia_ble = (lem_code_at_head c (pc + e1_len + e2_len) (IBle d1 d2) Nil ca_ble)
      in (lem_three_ssteps c s1 s2 s3 s4 c12 c23 c34) ? ((lem_codelen_app e1_cod (app e2_cod ex_cod)) &&& (lem_codelen_app e2_cod ex_cod))

lem_compile_BExp_correct c pc stk s (Equal e1 e2) d1 d2 ca
  = let 
      e1_cod = compile_AExp e1
      e2_cod = compile_AExp e2
      ex_cod = Cons (IBeq d1 d2) Nil -- extra code
      e1_len = codelen e1_cod
      e2_len = codelen e2_cod
      e1_val = aval e1 s
      e2_val = aval e2 s
      s1     = Conf pc stk s
      s2     = Conf (pc + e1_len) (Cons e1_val stk) s
      s3     = Conf (pc + e1_len + e2_len) (Cons e2_val (Cons e1_val stk)) s
      s4     = Conf (pc + e1_len + e2_len + 1 + (if (e1_val == e2_val) then d1 else d2)) stk s
      c12    = lem_compile_AExp_correct c pc stk s e1 ca_e1
                where 
                  {-@ ca_e1 :: Prop (CodeAt c pc e1_cod) @-}
                  ca_e1  = lem_code_at_app_left c pc e1_cod (app e2_cod ex_cod) ca
      c23    = lem_compile_AExp_correct c (pc + e1_len) (Cons e1_val stk) s e2 ca_e2
                where
                  {-@ ca_e2 :: Prop (CodeAt c {pc + e1_len} e2_cod) @-}
                  ca_e2  = lem_code_at_app_mid c pc e1_cod e2_cod ex_cod ca
      c34    = lem_one_ssteps c s3 s4 isbeq
                where 
                  {-@ isbeq  :: Prop (ISStep c s3 s4) @-}
                  -- {-@ ia_beq :: { instr_at c pc == Just (IBeq d1 d2) } @-} -- TODO: weird bug
                  {-@ ca_beq :: Prop (CodeAt c {pc + e1_len + e2_len} ex_cod)  @-}
                  isbeq  = (ISBeq c (pc + e1_len + e2_len) stk s d1 d2 e1_val e2_val (pc + e1_len + e2_len + 1 + (if (e1_val == e2_val) then d1 else d2))) ? ia_beq
                  ca_beq = (lem_code_at_app_right c pc (app e1_cod e2_cod) ex_cod (ca ? (thm_app_assoc e1_cod e2_cod ex_cod))) ? (lem_codelen_app e1_cod e2_cod)
                  ia_beq = (lem_code_at_head c (pc + e1_len + e2_len) (IBeq d1 d2) Nil ca_beq)
      in (lem_three_ssteps c s1 s2 s3 s4 c12 c23 c34) ? ((lem_codelen_app e1_cod (app e2_cod ex_cod)) &&& (lem_codelen_app e2_cod ex_cod))


{-@ lem_compile_Com_correct_terminating :: s:_ -> c':_ -> s':_ -> Prop (CExec s c' s') -> c:_ -> pc:_ -> stk:_ -> Prop (CodeAt c pc (compile_Com c'))
        -> Prop (ISSteps c (Conf pc stk s) 
                           (Conf {pc + (codelen (compile_Com c')) } stk s'))
  @-}
lem_compile_Com_correct_terminating :: State -> Com -> State -> CExec -> Code -> Int -> Stack -> CodeAt -> ISSteps
lem_compile_Com_correct_terminating s (Skip) s' (CExecSkip _) c pc stk ca
  = IRefl c (Conf pc stk s)

lem_compile_Com_correct_terminating s (Assign x e) s' (CExecAssign _ _ _) c pc stk ca
  = let 
      e_cod  = compile_AExp e
      e_len  = codelen e_cod
      e_val  = aval e s
      ex_cod = Cons (ISetvar x) Nil
      s1     = Conf pc stk s
      s2     = Conf (pc + e_len) (Cons e_val stk) s
      s3     = Conf (pc + e_len + 1) stk s'
      c12    = lem_compile_AExp_correct c pc stk s e ca_e
                where
                  {-@ ca_e :: Prop (CodeAt c pc e_cod) @-}
                  ca_e = lem_code_at_app_left c pc e_cod ex_cod ca
      c23    = lem_one_ssteps c s2 s3 (ISSetvar c (pc + e_len) stk s x e_val ? ia_setvar)
                where
                  ca_setvar = lem_code_at_app_right c pc e_cod ex_cod ca
                  ia_setvar = lem_code_at_head c (pc + e_len) (ISetvar x) Nil ca_setvar
    in lem_many_ssteps c s1 s2 s3 c12 c23 ? (lem_codelen_app e_cod ex_cod)

lem_compile_Com_correct_terminating s (Seq c1 c2) s' (CExecSeq _ _ _ m _ ce1 ce2) c pc stk ca
  = let 
      c1_cod = compile_Com c1
      c2_cod = compile_Com c2
      c1_len = codelen c1_cod
      c2_len = codelen c2_cod
      s1     = Conf pc stk s
      s2     = Conf (pc + c1_len) stk m
      s3     = Conf (pc + c1_len + c2_len) stk s'
      c12    = lem_compile_Com_correct_terminating s c1 m ce1 c pc stk ca_c1
                where
                  {-@ ca_c1 :: Prop (CodeAt c pc c1_cod) @-}
                  ca_c1 = lem_code_at_app_left c pc c1_cod c2_cod ca
      c23    = lem_compile_Com_correct_terminating m c2 s' ce2 c (pc + c1_len) stk ca_c2
                where
                  {-@ ca_c2 :: Prop (CodeAt c {pc + c1_len} c2_cod) @-} -- TODO: multiple definition
                  ca_c2 = lem_code_at_app_right c pc c1_cod c2_cod ca
    in lem_many_ssteps c s1 s2 s3 c12 c23 ? (lem_codelen_app c1_cod c2_cod)

lem_compile_Com_correct_terminating s (If b c1 c2) s' (CExecIf _ _ _ _ _ ce) c pc stk ca
  = let 
      b_cod  = compile_BExp b 0 (c1_len + 1)
      br_int = IBranch (c2_len)
      c1_cod = compile_Com c1
      c2_cod = compile_Com c2
      b_len  = codelen b_cod
      c1_len = codelen c1_cod
      c2_len = codelen c2_cod
      b_val  = bval b s
      s1     = Conf pc stk s

      {-@ ca_b  :: Prop (CodeAt c pc b_cod) @-}
      {-@ ca_c1 :: Prop (CodeAt c {pc + b_len} c1_cod) @-}
      {-@ ca_c2 :: Prop (CodeAt c {pc + b_len + c1_len + 1} c2_cod) @-} 
      ca_b   = lem_code_at_app_left c pc b_cod (app c1_cod (Cons br_int c2_cod)) ca
      ca_br  = lem_code_at_app_right c pc b_cod (app c1_cod (Cons br_int c2_cod)) ca
      ca_c1  = lem_code_at_app_left c (pc + b_len) c1_cod (Cons br_int c2_cod) ca_br
      ca_c1r = lem_code_at_app_right c (pc + b_len) c1_cod (Cons br_int c2_cod) ca_br
      ia_brc = lem_code_at_head c (pc + b_len + c1_len) br_int c2_cod ca_c1r 
      ca_c2  = lem_code_at_tail c (pc + b_len + c1_len) br_int c2_cod ca_c1r 

    in case (b_val) of
      True -> lem_three_ssteps c s1 s2 s3 s4 c12 c23 c34 ? ((lem_codelen_app b_cod (app c1_cod (Cons br_int c2_cod))) &&& (lem_codelen_app c1_cod (Cons br_int c2_cod)))
        where 
          s2  = Conf (pc + b_len) stk s
          s3  = Conf (pc + b_len + c1_len) stk s'
          s4  = Conf (pc + b_len + c1_len + 1 + c2_len) stk s'
          c12 = lem_compile_BExp_correct c pc stk s b 0 (c1_len + 1) ca_b
          c23 = lem_compile_Com_correct_terminating s c1 s' ce c (pc + b_len) stk ca_c1
          c34 = lem_one_ssteps c s3 s4 
                  (ISBranch c (pc + b_len + c1_len) stk s' c2_len (pc + b_len + c1_len + 1 + c2_len) ? ia_brc)
      False -> lem_many_ssteps c s1 s2 s3 c12 c23 ? ((lem_codelen_app b_cod (app c1_cod (Cons br_int c2_cod))) &&& (lem_codelen_app c1_cod (Cons br_int c2_cod)))
        where 
          s2  = Conf (pc + b_len + c1_len + 1) stk s
          s3  = Conf (pc + b_len + c1_len + 1 + c2_len) stk s'
          c12 = lem_compile_BExp_correct c pc stk s b 0 (c1_len + 1) ca_b
          c23 = lem_compile_Com_correct_terminating s c2 s' ce c (pc + b_len + c1_len + 1) stk ca_c2
              
lem_compile_Com_correct_terminating s (While b c') s' (CExecWhileD _ _ _) c pc stk ca
  = let 
      b_cod  = compile_BExp b 0 (c_len + 1)
      c_cod  = compile_Com c'
      ex_cod = (Cons (IBranch (-(c_len + b_len + 1))) Nil)
      b_len  = codelen b_cod 
      c_len  = codelen c_cod 
      b_val  = bval b s

      {-@ ca_b  :: Prop (CodeAt c pc b_cod) @-}
      ca_b   = lem_code_at_app_left c pc b_cod (app c_cod ex_cod) ca
    in lem_compile_BExp_correct c pc stk s b 0 (c_len + 1) ca_b ? ((lem_codelen_app b_cod (app c_cod ex_cod)) &&& (lem_codelen_app c_cod ex_cod))
        
lem_compile_Com_correct_terminating s (While b c') s' (CExecWhileL _ _ _ m _ ce1 ce2) c pc stk ca 
  = let 
      b_cod  = compile_BExp b 0 (c_len + 1)
      c_cod  = compile_Com c'
      ex_cod = (Cons br_int Nil)
      br_int = (IBranch (-(c_len + b_len + 1)))
      b_len  = codelen b_cod 
      c_len  = codelen c_cod 
      b_val  = bval b s
      s1     = Conf pc stk s
      s2     = Conf (pc + b_len) stk s
      s3     = Conf (pc + b_len + c_len) stk m
      s4     = Conf pc stk m
      s5     = Conf (pc + b_len + c_len + 1) stk s'
      c12    = lem_compile_BExp_correct c pc stk s b 0 (c_len + 1) ca_b
      c23    = lem_compile_Com_correct_terminating s c' m ce1 c (pc + b_len) stk ca_c
      c34    = lem_one_ssteps c s3 s4 (ISBranch c (pc + b_len + c_len) stk m (-(c_len + b_len + 1)) pc ? ia_brc)
      c45    = lem_compile_Com_correct_terminating m (While b c') s' ce2 c pc stk ca ? ((lem_codelen_app b_cod (app c_cod ex_cod)) &&& (lem_codelen_app c_cod ex_cod))

      {-@ ca_b  :: Prop (CodeAt c pc b_cod) @-}
      {-@ ca_c :: Prop (CodeAt c {pc + b_len} c_cod) @-}
      ca_b   = lem_code_at_app_left c pc b_cod (app c_cod ex_cod) ca
      ca_br  = lem_code_at_app_right c pc b_cod (app c_cod ex_cod) ca
      ca_c  = lem_code_at_app_left c (pc + b_len) c_cod ex_cod ca_br
      ca_cr = lem_code_at_app_right c (pc + b_len) c_cod ex_cod ca_br
      ia_brc = lem_code_at_head c (pc + b_len + c_len) br_int Nil ca_cr 

    in lem_four_ssteps c s1 s2 s3 s4 s5 c12 c23 c34 c45 ? ((lem_codelen_app b_cod (app c_cod ex_cod)) &&& (lem_codelen_app c_cod ex_cod))


{-@ thm_compile_Program_correct_terminating :: s:_ -> c:_ -> s':_ -> Prop (CExec s c s') -> (MachineTerminates (compileProgram c) s s')
  @-}
thm_compile_Program_correct_terminating :: State -> Com -> State -> CExec -> MachineTerminates
thm_compile_Program_correct_terminating _ _ _ _ = undefined
-}