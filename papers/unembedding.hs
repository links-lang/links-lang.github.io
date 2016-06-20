-- Code accompanying the paper "Unembedding domain-specific languages"
-- by Bob Atkey, Sam Lindley and Jeremy Yallop

-- Requires GHC 6.10

{-# LANGUAGE
      GADTs,
      KindSignatures,
      RankNTypes,
      TypeFamilies,
      TypeOperators,
      ScopedTypeVariables,
      EmptyDataDecls,
      TypeSynonymInstances,
      ImpredicativeTypes,
      PatternGuards
 #-}

import Data.Maybe
import Data.Set (Set)

-- Type equality combinator
data Eql :: * -> * -> * where
    Refl :: Eql a a

ecast :: forall a b. Eql a b -> forall f. f a -> f b
ecast Refl x = x

-- Some arithmetic stuff that we'll need later
plus :: Nat n -> Nat m -> Nat (n :+: m)
plus NatZ     m = m
plus (NatS n) m = NatS (plus n m)

trans :: Eql a b -> Eql b c -> Eql a c
trans Refl Refl = Refl

succEql :: Eql a b -> Eql (Succ a) (Succ b)
succEql Refl = Refl

assoc :: forall a b c. Nat a -> Nat b -> Nat c -> Eql ((a :+: b) :+: c) (a :+: (b :+: c))
assoc NatZ     b c = Refl
assoc (NatS a) b c = Refl `trans` succEql (assoc a b c) `trans` Refl

plus_1 :: forall x. Nat x -> Eql (Succ x) (x :+: Succ Zero)
plus_1 NatZ     = Refl
plus_1 (NatS x) = case plus_1 x of Refl -> Refl

class UntypedLambda exp where
    lam :: (exp -> exp) -> exp
    app :: exp -> exp -> exp

type Hoas = forall exp. UntypedLambda exp => exp

example1 :: Hoas
example1 = lam (\x -> lam (\y -> x `app` y))

numeral :: Integer -> Hoas
numeral n = lam (\s -> (lam (\z -> body s z n)))
  where body s z 0 = z
        body s z n = s `app` (body s z (n-1))

newtype Size = Size { size :: Integer }

instance UntypedLambda Size where
  lam f     = Size $ 1 + size (f (Size 1))
  x `app` y = Size $ 1 + size x + size y

getSize :: Hoas -> Integer
getSize term = size term

instance UntypedLambda Value where
    lam f            = VFunc f
    (VFunc f) `app` y = f y

eval :: Hoas -> Value
eval term = term

data DBTerm = Var Int
            | Lam DBTerm
            | App DBTerm DBTerm
            deriving (Show,Eq)

newtype DB = DB { unDB :: Int -> DBTerm }

instance UntypedLambda DB where
    lam f   = DB $ \i-> let v = \j-> Var (j-(i+1))
                         in
                          Lam (unDB (f (DB v)) (i+1))
    app x y = DB $ \i-> App (unDB x i) (unDB y i)

toTerm :: Hoas -> DBTerm
toTerm v = unDB v 0

type Hoas' = forall exp.UntypedLambda exp => [exp] -> exp

toTerm' :: Hoas' -> DBTerm
toTerm' v = unDB w 0
  where w     = v (env 0)
        env j = DB (\i-> Var (i+j)) : env (j+1)

usesOf n (Var m)     = if n == m then 1 else 0
usesOf n (Lam t)     = usesOf (n+1) t
usesOf n (App s t)   = usesOf n s + usesOf n t

lift m p (Var n)  | n < p     = Var n
                  | otherwise = Var (n+m)
lift m p (Lam body)  = Lam (lift m (p+1) body)
lift m p (App s t)   = App (lift m p s) (lift m p t)

subst m t (Var n) | n == m    = t
                  | n > m     = Var (n-1)
                  | otherwise = Var n
subst m t (Lam s)    = Lam (subst (m+1) (lift 1 0 t) s)
subst m t (App s s') = App (subst m t s) (subst m t s')

shrink (Var n)   = Var n
shrink (Lam t)   = Lam (shrink t)
shrink (App s t) = case s' of
      Lam u | usesOf 0 u <= 1 -> shrink (subst 0 t' u)
      _                       -> App s' t'
    where s' = shrink s
          t' = shrink t

fromTerm' :: DBTerm -> Hoas'
fromTerm' (Var i)   env = env !! i
fromTerm' (Lam t)   env = lam (\x -> fromTerm' t (x:env))
fromTerm' (App x y) env = 
   fromTerm' x env `app` fromTerm' y env

fromTerm :: DBTerm -> Hoas
fromTerm term = fromTerm' term []

data Zero
data Succ a

data Fin :: * -> * where
   FinZ :: Fin (Succ a)
   FinS :: Fin a -> Fin (Succ a)

integerOfFin :: Fin a -> Integer
integerOfFin FinZ     = 0
integerOfFin (FinS n) = 1 + integerOfFin n

instance Show (Fin a) where
    show = show . integerOfFin

data WFTerm :: * -> * where
   WFVar :: Fin a -> WFTerm a
   WFLam :: WFTerm (Succ a) -> WFTerm a
   WFApp :: WFTerm a -> WFTerm a -> WFTerm a

instance Show (WFTerm a) where
    show (WFVar f)   = "(Var " ++ show f ++ ")"
    show (WFLam t)   = "(Lam " ++ show t ++ ")"
    show (WFApp x y) = "(App " ++ show x ++ " " ++ show y ++ ")"

data Nat :: * -> * where
   NatZ :: Nat Zero
   NatS :: Nat a -> Nat (Succ a)

newtype WFDB = WFDB { unWFDB :: forall j. Nat j -> WFTerm j }

natToFin :: Nat a -> Fin (Succ a)
natToFin NatZ     = FinZ
natToFin (NatS n) = FinS (natToFin n)

weaken :: Fin a -> Fin (Succ a)
weaken FinZ     = FinZ
weaken (FinS n) = FinS (weaken n)

shift :: Nat j -> Nat i -> Fin j
shift NatZ     _        = undefined
shift (NatS x) NatZ     = natToFin x
shift (NatS x) (NatS y) = weaken $ shift x y

instance UntypedLambda WFDB where
    lam f = WFDB $
            \i-> let v = \j-> WFVar (shift j i)
                  in
                   WFLam (unWFDB (f (WFDB v)) (NatS i))
    x `app` y = WFDB $
            \i-> WFApp (unWFDB x i) (unWFDB y i)

toWFTerm :: Hoas -> WFTerm Zero
toWFTerm v = unWFDB v NatZ

data WFEnv :: * -> * -> * where
  WFEmpty :: WFEnv exp Zero
  WFExtend :: WFEnv exp n -> exp -> WFEnv exp (Succ n)

lookWF :: WFEnv exp n -> Fin n -> exp
lookWF WFEmpty _                 = undefined --impossible
lookWF (WFExtend _ v) FinZ       = v
lookWF (WFExtend env _) (FinS n) = lookWF env n

type WFHoas' n =
  forall exp.UntypedLambda exp => WFEnv exp n -> exp

toWFTerm' :: Nat n -> WFHoas' n -> WFTerm n
toWFTerm' n v = unWFDB (v (makeEnv n)) n
  where
    makeEnv :: Nat n -> WFEnv WFDB n
    makeEnv NatZ = WFEmpty
    makeEnv (NatS i) =
      WFExtend
        (makeEnv i)
        (WFDB (\j-> WFVar (shift j i)))

toWFHoas' :: WFTerm n -> WFHoas' n
toWFHoas' (WFVar n) = \env -> lookWF env n
toWFHoas' (WFLam t) =
  \env -> lam (\x -> toWFHoas' t (WFExtend env x))
toWFHoas' (WFApp f p) =
  \env -> toWFHoas' f env `app` toWFHoas' p env

toWFHoas :: WFTerm Zero -> Hoas 
toWFHoas t = toWFHoas' t WFEmpty

class Booleans exp where
    true  :: exp
    false :: exp
    cond  :: exp -> exp -> exp -> exp

not = lam (\x -> cond x false true)

class (Booleans exp, UntypedLambda exp) =>
    BooleanLambda exp

not :: BooleanLambda exp => exp

instance Booleans Size where
    true  = Size $ 1
    false = Size $ 1
    cond c t e = Size $ size c + size t + size e

data Value = VFunc (Value -> Value) | VTrue | VFalse

instance Booleans Value where
    true  = VTrue
    false = VFalse
    cond VTrue  t _ = t
    cond VFalse _ e = e

class PairsAndSums exp where
    pair :: exp -> exp -> exp
    inl  :: exp -> exp
    inr  :: exp -> exp

class BasicPatternMatch exp where
    pair_match :: exp -> ((exp,exp) -> exp) -> exp
    sum_match  :: exp -> (exp -> exp) -> (exp -> exp)
                                                  -> exp

data Id a          = V a
data Pair f1 f2 a  = f1 a :*: f2 a
data Inl f a       = Inl (f a)
data Inr f a       = Inr (f a)

data Pattern :: (* -> *) -> * -> * where
    PVar  :: Pattern Id (Succ Zero)
    PPair :: Nat x -> Pattern f1 x -> Pattern f2 y ->
                         Pattern (Pair f1 f2) (x :+: y)
    PInl  :: Pattern f x -> Pattern (Inl f) x
    PInr  :: Pattern f x -> Pattern (Inr f) x

type family   n :+: m        :: *
type instance Zero     :+: n = n
type instance (Succ n) :+: m = Succ (n :+: m)

data Case exp = forall f n. Case (Pattern f n) (f exp -> exp)

class PatternMatch exp where
    match :: exp -> [Case exp] -> exp

matcher0 x = match x
    [ Case (PPair (NatS NatZ) PVar PVar) $
                           \(V x :*: V y) -> pair x y
    , Case (PInl  PVar) $ \(Inl (V x)) -> x ]

data IPat f = forall n. IPat (Nat n) (Pattern f n)

class ImplicitPattern f where
    patRep :: IPat f

clause :: forall f exp.
    ImplicitPattern f => (f exp -> exp) -> Case exp
clause body = case patRep of
               IPat _ pattern -> Case pattern body

instance ImplicitPattern Id where
    patRep = IPat (NatS NatZ) PVar
instance (ImplicitPattern f1, ImplicitPattern f2) => ImplicitPattern (Pair f1 f2) where
    patRep = case (patRep, patRep) of
               (IPat n1 p1, IPat n2 p2) -> IPat (plus n1 n2) (PPair n1 p1 p2)
instance ImplicitPattern f => ImplicitPattern (Inl f) where
    patRep = case patRep of
               IPat n p -> IPat n (PInl p)
instance ImplicitPattern f => ImplicitPattern (Inr f) where
    patRep = case patRep of
               IPat n p -> IPat n (PInr p)

matcher x = match x
    [ clause $ \(V x :*: V y) -> pair x y
    , clause $ \(Inl (V x)) -> x ]

class TypedLambda0 exp where
    tlam0 :: (exp a -> exp b) -> exp (a -> b)
    tapp0 :: exp (a -> b) -> exp a -> exp b

type THoas0 a = forall exp. TypedLambda0 exp => exp a

example3 :: THoas0 (Bool -> (Bool -> Bool) -> Bool)
example3 = tlam0 (\x -> tlam0 (\y -> y `tapp0` x))

data Rep :: * -> * where
     Bool :: Rep Bool
     (:->) :: (Representable a, Representable b) => 
           Rep a -> Rep b -> Rep (a->b)

class Representable a where rep :: Rep a

instance Representable Bool where rep = Bool

instance (Representable a, Representable b) =>
    Representable (a->b) where
        rep = rep :-> rep

instance Show (Rep a) where
    show Bool = "bool"
    show (r1 :-> r2) =
      "(" ++ show r1 ++ "->" ++ show r2 ++ ")"

cast :: Rep a -> Rep b -> Maybe (forall f. f a -> f b)

-- prove that two type representations are equal
eqRep :: Rep a -> Rep b -> Maybe (Eql a b)
eqRep Bool Bool = return Refl
eqRep (a :-> b) (a' :-> b') =
  do { Refl <- eqRep a a';  Refl <- eqRep b b' ;  return Refl }

cast r1 r2 =
  do
    Refl <- eqRep r1 r2
    return id

class TypedLambda exp where
  tlam :: (Representable a, Representable b) =>
    (exp a -> exp b) -> exp (a->b)
  tapp :: (Representable a, Representable b) =>
    exp (a -> b) -> exp a -> exp b

type THoas a = forall exp. TypedLambda exp => exp a

example4 :: (Representable a, Representable b) =>
              THoas ((a -> b) -> a -> b)
example4 = tlam (\x -> tlam (\y -> x `tapp` y))

example5 =
 toTTerm (example4 :: THoas ((Bool->Bool)->Bool->Bool))

tlam' ::
  (Representable a, Representable b, TypedLambda exp) =>
    Rep a -> (exp a -> exp b) -> exp (a->b)
tlam' _ = tlam 

example7 :: (Representable a) => THoas (a -> a)
example7 = tlam (\x -> tlam (\y -> y))
            `tapp` (tlam' Bool (\z -> z))

newtype TEval a = TEval { unTEval :: a }

instance TypedLambda TEval where
    tlam f                 = TEval (unTEval . f . TEval)
    TEval f `tapp` TEval a = TEval (f a) 

data Ctx :: * -> * where
   CtxZ :: Ctx ()
   CtxS :: Representable a => Ctx ctx -> Ctx (a, ctx)

data Index :: * -> * -> * where
   IndexZ :: Index (a, ctx) a
   IndexS :: Index ctx a -> Index (b, ctx) a

intOfIndex :: Index ctx a -> Int
intOfIndex IndexZ     = 0
intOfIndex (IndexS i) = 1 + intOfIndex i

instance Show (Index ctx a) where
    show = show . intOfIndex

data TTerm :: * -> * -> * where
   TVar :: Representable a => Index ctx a -> TTerm ctx a
   TLam :: (Representable a, Representable b) =>
             TTerm (a, ctx) b -> TTerm ctx (a -> b)
   TApp :: (Representable a, Representable b) =>
          TTerm ctx (a->b) -> TTerm ctx a -> TTerm ctx b

showT :: TTerm ctx a -> String
showT (TVar i) = "(Var " ++ show i ++ ")"
showT (TLam (t::TTerm (b, ctx) a)) =
  "(Lam_" ++ show (rep::Rep b) ++ " " ++ showT t ++ ")"
showT (TApp x y) =
  "(App " ++ showT x ++ " " ++ showT y ++ ")"

instance Show (TTerm ctx a) where
    show = showT

newtype TDB a =
  TDB { unTDB :: forall ctx. Ctx ctx -> TTerm ctx a }

instance TypedLambda TDB where
  tlam (f::TDB a -> TDB b) =
    TDB$ \i->
     TLam (unTDB (f (TDB$ \j-> TVar (tshift j (CtxS i))))
          (CtxS i))
  (TDB x) `tapp` (TDB y) = TDB$ \i-> TApp (x i) (y i)

len :: Ctx n -> Int
len CtxZ       = 0
len (CtxS ctx) = 1 + len ctx

tshift' :: Int -> Ctx j -> Ctx (a, i) -> Index j a
tshift' _ CtxZ     _        = undefined
tshift' 0 (CtxS _) (CtxS _) = fromJust (cast rep rep) IndexZ
tshift' n (CtxS c1) c2      = IndexS (tshift' (n-1) c1 c2)

tshift :: Ctx j -> Ctx (a, i) -> Index j a
tshift c1 c2 = tshift' (len c1 - len c2) c1 c2

data TEnv :: (* -> *) -> * -> * where
   TEmpty :: TEnv exp ()
   TExtend :: TEnv exp ctx -> exp a -> TEnv exp (a, ctx)

lookT :: TEnv exp ctx -> Index ctx a -> exp a
lookT (TExtend _   v) IndexZ     = v
lookT (TExtend env _) (IndexS n) = lookT env n

type THoas' ctx a = forall (exp :: * -> *).
  TypedLambda exp => TEnv exp ctx -> exp a

toTHoas' :: TTerm ctx a -> THoas' ctx a
toTHoas' (TVar n)   = \env -> lookT env n
toTHoas' (TLam t)   =
  \env -> tlam (\x -> toTHoas' t (TExtend env x))
toTHoas' (TApp f p) =
  \env -> toTHoas' f env `tapp` toTHoas' p env

toTHoas :: TTerm () a -> THoas a
toTHoas t = toTHoas' t TEmpty

toTTerm' :: Ctx ctx -> THoas' ctx a -> TTerm ctx a
toTTerm' ctx v = unTDB w ctx
  where  w = v (makeEnv ctx)
         makeEnv :: Ctx ctx -> TEnv TDB ctx
         makeEnv CtxZ = TEmpty
         makeEnv (CtxS j) =
           TExtend (makeEnv j)
             (TDB (\i-> TVar (tshift i (CtxS j))))

toTTerm :: THoas a -> TTerm () a
toTTerm v = unTDB v CtxZ

class ArithExpr exp where
    let_    :: exp -> (exp -> exp) -> exp
    integer :: Int -> exp
    binop   :: (Int -> Int -> Int) -> exp -> exp -> exp

type AExpr = forall exp. ArithExpr exp => exp

example8 :: AExpr
example8 = let_ (integer 8) $ \x ->
           let_ (integer 9) $ \y ->
            binop (+) x y

data UnitypedStateOps t a l m = USTOps
    { ret  :: a -> m
    , new  :: t -> (l -> m) -> m
    , lkup :: l -> (t -> m) -> m
    , upd  :: l -> t -> m -> m }

newtype UnitypedST t l a =
   UST { unUST :: forall m. UnitypedStateOps t a l m -> m }

instance Monad (UnitypedST t l) where
    return x   = UST $ \ops -> ret ops x
    UST x >>= f =
      UST $ \ops -> x (USTOps (\a -> unUST (f a) ops)
                         (new ops) (lkup ops) (upd ops))

newU :: t -> UnitypedST t l l
newU x = UST $ \ops -> new ops x (ret ops)

lkupU :: l -> UnitypedST t l t
lkupU l = UST $ \ops -> lkup ops l (ret ops)

updU :: l -> t -> UnitypedST t l ()
updU l x = UST $ \ops -> upd ops l x (ret ops ())

runUnitypedST :: (forall l. UnitypedST t l a) -> a

runUnitypedST = undefined

data StateOps a l m = StateOps
    { tret  :: a -> m
    , tnew  :: forall t. t -> (l t -> m) -> m
    , tlkup :: forall t. l t -> (t -> m) -> m
    , tupd  :: forall t. l t -> t -> m -> m }

type ST l a = forall l m. StateOps a l m -> m

class TypedBooleans exp where
  ttrue  :: exp Bool
  tfalse :: exp Bool
  tcond  :: exp Bool -> exp a -> exp a -> exp a 

class (TypedBooleans exp, TypedLambda exp) => Mobile exp

data URep = UBool | URep :--> URep deriving (Show, Read)

data MTerm = MVar Int | MLam URep MTerm | MApp MTerm MTerm
           | MTrue | MFalse | MCond MTerm MTerm MTerm
              deriving (Show, Read)

newtype MDB a = MDB { unMDB :: Int -> MTerm }

marshal :: (forall exp. Mobile exp => exp a) -> String
marshal t = show (unMDB t 0)

data Typed :: (* -> *) -> * where
  (:::) :: Representable a => exp a -> Rep a -> Typed exp

toHoas :: (TypedLambda exp, TypedBooleans exp) =>
    MTerm -> [Typed exp] -> Maybe (Typed exp)

unmarshal :: String ->
  (forall exp. Mobile exp => Maybe (Typed exp))
unmarshal s = toHoas (read s) []

instance Mobile MDB

idx :: Int -> [a] -> Maybe a
idx n = listToMaybe . drop n

infixr :-->

data SomeType where Typ :: Representable a => Rep a -> SomeType

asURep :: Rep a -> URep
asURep Bool = UBool
asURep (f :-> t) = asURep f :--> asURep t

asRep :: URep -> (forall a. (Representable a) =>Rep a -> b) -> b
asRep UBool k = k Bool
asRep (f :--> t) k = asRep f $ \f' -> asRep t $ \t' -> k (f' :-> t')

instance TypedLambda MDB where
    tlam (f :: MDB a -> MDB b)  = MDB$ \i -> MLam (asURep (rep :: Rep a)) ((unMDB.f.MDB) (\j -> MVar (j-i-1)) (i+1))
    MDB x `tapp` MDB y = MDB$ \i -> x i `MApp` y i

instance TypedBooleans MDB where
    ttrue  = MDB$ \_ -> MTrue
    tfalse = MDB$ \_ -> MFalse
    tcond (MDB c) (MDB t) (MDB e) = MDB$ \i -> MCond (c i) (t i) (e i)

tc  :: MTerm -> [SomeType] -> Maybe SomeType
tc (MVar i)      env = idx i env
tc (MLam ty e)   env = asRep ty (\ty -> do
  Typ b <- tc e (Typ ty : env)
  return$ Typ (ty :-> b))
tc (f `MApp` p)  env = do
  Typ (a :-> b) <- tc f env
  Typ a'        <- tc p env
  Refl          <- eqRep a a'
  return$ Typ b
tc MTrue         env = return$ Typ Bool
tc MFalse        env = return$ Typ Bool
tc (MCond c t e) env = do
  Typ Bool <- tc c env
  Typ a    <- tc t env
  Typ b    <- tc e env
  Refl     <- eqRep a b
  return$ Typ b

toHoas (MVar i)      env = idx i env
toHoas (MLam ty e)   env = asRep ty (\ty -> do
  Typ b <- tc e (Typ ty : map typeOf env)
  return$ (tlam (\v -> unType b (fromJust (toHoas e (v ::: ty : env))))) ::: (ty :-> b))
    where
      typeOf :: Typed exp -> SomeType
      typeOf (_ ::: t) = Typ t
      unType :: Rep a -> Typed exp -> exp a
      unType t (e ::: t') | Just Refl <- eqRep t' t = e
toHoas (f `MApp` p)  env = do
  f ::: (a :-> b) <- toHoas f env
  p ::: a'        <- toHoas p env
  Refl            <- eqRep a a'
  return $ tapp f p ::: b
toHoas MTrue         env = return$ ttrue  ::: Bool
toHoas MFalse        env = return$ tfalse ::: Bool
toHoas (MCond c t e) env = do
  c' ::: Bool <- toHoas c env
  t' ::: a    <- toHoas t env
  e' ::: b    <- toHoas e env
  Refl        <- eqRep a b
  return$ tcond c' t' e' ::: b

instance TypedBooleans TEval where
    ttrue = TEval True
    tfalse = TEval False
    tcond (TEval True) t _ = t
    tcond (TEval False) _ e = e

instance Mobile TEval

example9 = 
    let not :: Mobile exp => exp (Bool -> Bool)
        not = tlam (\x -> tcond x tfalse ttrue)
        string = marshal not
        restored = fromJust$ unTag (Bool :-> Bool) $ fromJust (unmarshal string)
        not' = unTEval restored
    in
    [not' True, not' False]

unTag :: Rep a -> Typed exp -> Maybe (exp a)
unTag t (e ::: t') = do
  Refl <- eqRep t t'
  return e

class TypedSets exp where
 empty  :: exp (Set a)
 single :: exp a -> exp (Set a)
 union  :: exp (Set a) -> exp (Set a) -> exp (Set a)
 for :: exp (Set a) -> (exp a->exp (Set b)) -> exp (Set b)

class (TypedLambda exp, TypedBooleans exp, TypedUnit exp,
       TypedPairs exp, TypedSets exp) => NRC exp

data NTerm =
   NVar Integer | NLam NTerm | NApp NTerm NTerm
 | NUnit
 | NPair NTerm NTerm | NP1 NTerm | NP2 NTerm
 | NT | NF | NCond NTerm NTerm NTerm
 | NEmpty | NSingle NTerm
 | NUnion NTerm NTerm | NFor NTerm NTerm
     deriving Show

class TypedUnit exp where
  unit :: exp ()

class TypedPairs exp where
  (**) :: exp a -> exp b -> exp (a, b)
  p1   :: exp (a, b) -> exp a
  p2   :: exp (a, b) -> exp b

class Exp exp where
    lit :: Int -> exp
    add :: exp -> exp -> exp

instance Exp String where
    lit v   = show v
    add l r = l ++ " + " ++ r

class Exp exp => NegExp exp where
    neg :: exp -> exp

instance NegExp String where
    neg e = "-(" ++ e ++ ")"

instance Exp Int where
    lit v   = v
    add l r = l + r

instance NegExp Int where
    neg e = -e

