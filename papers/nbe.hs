-- Normalisation by evaluation for the computational lambda-calculus +
-- sums using either an accumulation monad over binding trees or a
-- continuation monad

import Data.Maybe
import Control.Monad.State
import Control.Monad.Cont

-- The object language is Moggi's computational lambda calculus
-- extended with sums. We use a HOAS representation for input and a
-- FOAS representation for intentional manipulation.

type Var = String

-- FOAS
data Exp = Var Var
         | Lam Var Exp
         | App Exp Exp
         | Inl Exp
         | Inr Exp
         | Case Exp Var Exp Var Exp
         | Let Var Exp Exp

instance Show Exp where
    show (Var x) = x
    show (Lam x e) = "\\" ++ x ++ " -> " ++ show e
    show (App e e') = "(" ++ show e ++ ") (" ++ show e' ++ ")"
    show (Inl e) = "Left (" ++ show e ++ ")"
    show (Inr e) = "Right (" ++ show e ++ ")"
    show (Case e x1 e1 x2 e2) =
         "case (" ++ show e ++ ") of Left " ++
                  x1 ++ " -> (" ++ show e1 ++"); Right " ++
                  x2 ++ " -> (" ++ show e2 ++ ")"
    show (Let x e e') = "let " ++ x ++ " = (" ++ show e ++ ") in " ++ "(" ++ show e' ++ ")"

-- HOAS
class CompLam exp where
  lam :: (exp -> exp) -> exp
  app :: exp -> exp -> exp
  inl :: exp -> exp
  inr :: exp -> exp
  case_ :: exp -> (exp -> exp) -> (exp -> exp) -> exp
  let_ :: exp -> (exp -> exp) -> exp

-- the type of closed HOAS terms
type Hoas = forall exp . CompLam exp => exp

-- convert a closed HOAS term to the
-- corresponding FOAS term
hoasToExp :: Hoas -> Exp
hoasToExp v = evalGen v 0

instance CompLam (Gen Exp) where
    lam f = do x <- nextName
               e <- f (return (Var x))
               return$ Lam x e
    v1 `app` v2 = do e1 <- v1
                     e2 <- v2
                     return$ App e1 e2
    inl v = do e <- v
               return$ Inl e
    inr v = do e <- v
               return$ Inr e
    case_ v l r = do e <- v
                     x1 <- nextName
                     x2 <- nextName
                     e1 <- l (return (Var x1))
                     e2 <- r (return (Var x2))
                     return$ Case e x1 e1 x2 e2
    let_ v f = do e <- v
                  x <- nextName
                  e' <- f (return (Var x))
                  return$ Let x e e'

-- Types
infixl 9 :+:
infixr 5 :->

-- We build up simple types from: abstract base types (A,B,C), the
-- function type constructor (->), and the sum type constructor (Either).

-- some abstract base types
data A
data B
data C

-- syntactic sugar for sums
type a :+: b = Either a b

-- a GADT of simple type representations
data Rep :: * -> * where
     A :: Rep A
     B :: Rep B
     C :: Rep C
     (:->) :: Rep a -> Rep b -> Rep (a->b)
     (:+:) :: Rep a -> Rep b -> Rep (a:+:b)

instance Show (Rep a) where
    show A = "A"
    show B = "B"
    show C = "C"
    show (r1 :-> r2) = "(" ++ show r1 ++ "->" ++ show r2 ++ ")"
    show (r1 :+: r2) = "(" ++ show r1 ++ ":+:" ++ show r2 ++ ")"

-- The Representable type class allows us to smoothly bridge the gap between
-- metalanguage types and object language type representations.
--
-- Note that this type class is closed by construction, as the Rep GADT
-- only admits simple type representations.
class Representable a where
    rep :: Rep a

instance Representable A where rep = A
instance Representable B where rep = B
instance Representable C where rep = C

instance (Representable a, Representable b) => Representable (a->b) where
    rep = rep :-> rep

instance (Representable a, Representable b) => Representable (a:+:b) where
    rep = rep :+: rep

-- Typed HOAS
class TCompLam exp where
  tlam :: (Representable a, Representable b) => (exp a -> exp b) -> exp (a->b)
  tapp :: (Representable a, Representable b) => exp (a->b) -> exp a -> exp b
  tinl :: (Representable a, Representable b) => exp a -> exp (a:+:b)
  tinr :: (Representable a, Representable b) => exp b -> exp (a:+:b)
  tcase :: (Representable a, Representable b, Representable c) =>
            exp (a:+:b) -> (exp a -> exp c) -> (exp b -> exp c) -> exp c
  tlet :: (Representable a, Representable b) => exp a -> (exp a -> exp b) -> exp b

-- the type of closed HOAS terms of type a
type THoas a = forall (exp :: * -> *). TCompLam exp => exp a

-- convert a typed closed HOAS term to the
-- corresponding FOAS term
thoasToExp :: THoas a -> Exp
thoasToExp v = evalGen (unT v) 0

-- expressions with names and a phantom type attached
newtype T a = T {unT :: Gen Exp}

-- we could get rid of all the boxing (T) and unboxing (unT) of the T
-- datatype if Haskell had better support for parameterised monads
instance TCompLam T where
    tlam f = T$ do x <- nextName
                   e <- unT$ f (T$ return (Var x))
                   return (Lam x e)
    v1 `tapp` v2 = T$ do e1 <- unT v1
                         e2 <- unT v2
                         return (App e1 e2)
    tinl v = T$ do e <- unT v
                   return (Inl e)
    tinr v = T$ do e <- unT v
                   return (Inr e)
    tcase v l r = T$ do e <- unT v
                        x1 <- nextName
                        x2 <- nextName
                        e1 <- unT$ l (T$ return (Var x1))
                        e2 <- unT$ r (T$ return (Var x2))
                        return (Case e x1 e1 x2 e2)
    tlet v f = T$ do e <- unT v
                     x <- nextName
                     e' <- unT$ f (T$ return (Var x))
                     return (Let x e e')


--- environments
type Env a = [(Var, a)]

empty :: Env a
empty = []

extend :: [(Var, a)] -> Var -> a -> [(Var, a)]
extend env x v = (x, v):env

--- use the state monad for name generation
type Gen = State Int

nextName :: Gen Var
nextName = do { i <- get; put (i+1); return ("x" ++ show i) }

evalGen :: Gen a -> Int -> a
evalGen = evalState

--- The accumulation monad over binding trees

-- The nodes consist of let bindings and case bindings.
-- The leaves are values.
data Acc a = Val a
           | LetB Var Exp (Acc a)
           | CaseB Exp Var (Acc a) Var (Acc a)

instance Monad Acc where
    return v = Val v
    Val v >>= f = f v
    LetB x e m >>= f =
        LetB x e (m >>= f)
    CaseB e x1 m1 x2 m2 >>= f =
        CaseB e x1 (m1 >>= f) x2 (m2 >>= f)

-- flatten an expression tree to an expression
flatten :: Acc Exp -> Exp
flatten (Val e) = e
flatten (LetB x e t) = Let x e (flatten t)
flatten (CaseB v x1 t1 x2 t2) =
    Case v x1 (flatten t1) x2 (flatten t2)

--- Residualising monads

-- the monad obtained by pre-composing name generation with
-- the accumulation monad
newtype GenAcc a = GA {unGA :: Gen (Acc a)}
instance Monad GenAcc where
    return = GA . return . return
    m >>= k =        
        GA (do c <- unGA m
               case c of
                 Val v -> unGA (k v)
                 LetB x e m ->
                     do t <- unGA (GA (return m) >>= k)
                        return (LetB x e t)
                 CaseB e x1 m1 x2 m2 ->
                     do t1 <- unGA (GA (return m1) >>= k)
                        t2 <- unGA (GA (return m2) >>= k)
                        return (CaseB e x1 t1 x2 t2))

-- continuation-based residualising monad
type ContGenExp = Cont (Gen Exp)

--- operations for the residualising monad
class Monad m => Residualising m where
    -- lift a computation from Gen to m
    gamma :: Gen a -> m a
    -- collect bindings from the residualising monad
    collect :: m Exp -> Gen Exp
    -- register a let binding in the residualising monad
    bind :: Exp -> m Var
    -- register a case binding in the residualising monad
    binds :: Exp -> m (Var :+: Var)

instance Residualising GenAcc where
    gamma f = GA (do v <- f; return (return v))
    collect (GA f) = do t <- f
                        return (flatten t)
    bind e =
        GA (do x <- nextName
               return$ LetB x e (Val x))
    binds e =
        GA (do x1 <- nextName
               x2 <- nextName
               return$ CaseB e x1 (Val (Left x1))
                               x2 (Val (Right x2)))

instance Residualising ContGenExp where
    gamma f = Cont (\k -> do m <- f; k m)
    collect (Cont f) = f return
    bind e = Cont (\k ->
                   do x <- nextName
                      e' <- k x
                      return (Let x e e'))
    binds e = Cont (\k ->
                    do x1 <- nextName
                       x2 <- nextName
                       e1 <- k (Left x1)
                       e2 <- k (Right x2)
                       return (Case e x1 e1 x2 e2))

--- semantics

-- values and computations
data SemV m = Neutral Exp
            | Fun (SemV m -> SemC m)
            | Sum (SemV m :+: SemV m)
type SemC m = m (SemV m)

--- NBE

-- the type of a residualising evaluator
type ResEval m = Env (SemV m) -> Exp -> SemC m

-- The normalisation function is parameterised by the evaluator
-- allowing us to choose between the accumulation monad and the
-- continuation monad.
norm :: Residualising m => ResEval m -> Rep a -> THoas a -> Exp
norm eval a e = evalGen (reifyC a (eval empty (thoasToExp e))) 0

-- concrete normalisation functions
normAcc = norm (eval :: ResEval GenAcc)
normCont = norm (eval :: ResEval ContGenExp)

-- Untyped version
normU :: Residualising m => ResEval m -> Rep a -> Hoas -> Exp
normU eval a e = evalGen (reifyC a (eval empty (hoasToExp e))) 0

normAccU = normU (eval :: ResEval GenAcc)
normContU = normU (eval :: ResEval ContGenExp)

-- reify a computation
reifyC :: Residualising m => Rep a -> SemC m -> Gen Exp
reifyC a c = collect (do v <- c; gamma (reifyV a v))

-- reify a value
reifyV :: Residualising m => Rep a -> SemV m -> Gen Exp
reifyV A (Neutral e) = return e
reifyV B (Neutral e) = return e
reifyV C (Neutral e) = return e
reifyV (a :-> b) (Fun f) =
    do x <- nextName
       e <- reifyC b (do v <- reflectV a x; f v)
       return$ Lam x e
reifyV (a :+: b) (Sum (Left v)) =
    do e <- reifyV a v
       return$ Inl e
reifyV (a :+: b) (Sum (Right v)) =
    do e <- reifyV b v
       return$ Inr e

-- reflect a neutral computation expression (i.e. application) as a computation
reflectC :: Residualising m => Rep a -> Var -> Exp -> SemC m
reflectC a x e =
    do x <- bind (App (Var x) e)
       reflectV a x   

-- reflect a neutral value expression (i.e. variable) as a computation
reflectV :: Residualising m => Rep a -> Var -> SemC m
reflectV A x = return (Neutral (Var x))
reflectV B x = return (Neutral (Var x))
reflectV C x = return (Neutral (Var x))
reflectV (a :-> b) x =
    return (Fun (\v -> do e <- gamma (reifyV a v); reflectC b x e))
reflectV (a :+: b) x =
    do v <- binds (Var x)
       case v of
         Left x1 ->
             do v1 <- reflectV a x1
                return (Sum (Left v1))
         Right x2 ->
             do v2 <- reflectV b x2
                return (Sum (Right v2))

--- A monadic evaluator

-- it seems necessary to have injFun return
-- a computation rather than a value in order to satisfy
-- the GHC type inference algorithm

-- interpretting functions
class FunInt v m where
    injFun :: (v -> m v) -> m v
    projFun :: v -> (v -> m v)

-- interpretting sums
class SumInt v where
    injSum :: v :+: v -> v
    projSum :: v -> v :+: v

instance Residualising m => FunInt (SemV m) m where
    injFun f = return (Fun f)
    projFun = \(Fun f) -> f

instance Residualising m => SumInt (SemV m) where
    injSum = Sum
    projSum = \(Sum s) -> s

eval :: (Monad m, FunInt a m, SumInt a) => Env a -> Exp -> m a
eval env (Var x) =
    return (fromJust (lookup x env))
eval env (Lam x e) =
    injFun (\v -> eval (extend env x v) e)
eval env (App e1 e2) =
    do
      v1 <- eval env e1
      v2 <- eval env e2
      projFun v1 v2
eval env (Let x e1 e2) =
    do 
      v <- eval env e1
      eval (extend env x v) e2
eval env (Inl e) =
    do
      v <- eval env e
      return (injSum (Left v))
eval env (Inr e) =
    do
      v <- eval env e
      return (injSum (Right v))
eval env (Case e x1 e1 x2 e2) =
    do
      v <- eval env e
      case projSum v of
        Left v  -> eval (extend env x1 v) e1
        Right v -> eval (extend env x2 v) e2
