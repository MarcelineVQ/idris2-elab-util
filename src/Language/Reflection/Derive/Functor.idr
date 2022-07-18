module Language.Reflection.Derive.Functor

import public Language.Reflection.Pretty
-- import public Language.Reflection.Syntax
-- import public Language.Reflection.Types

-- import Language.Reflection

import Data.Stream
import Data.String

import Data.IORef
import Control.Monad.State

import Data.DPair

import Data.SortedMap

import Language.Reflection.Derive
%language ElabReflection

--------------------------------------------------
-- MkFC regex:
-- \(MkFC (.*?)(\)\))
-- \(MkFC (.*?)(\)\))(.*?)(\)\))
--------------------------------------------------

public export
data Polarity = Neg | Pos

Show Polarity where
  show Neg = "Neg"
  show Pos = "Pos"

export
not : Polarity -> Polarity
not Pos = Neg
not Neg = Pos

||| Tag for how to treat the arguments of a function.
||| Norm = negative -> positive
||| Flip = positive -> negative
public export
data Polarity' = Norm | Flip

Show Polarity' where
  show Norm = "Norm"
  show Flip = "Flip"

export
not' : Polarity' -> Polarity'
not' Norm = Flip
not' Flip = Norm

public export
data TagTree
  = SkipT -- field to be left alone, either being placed back in as-is (map) or skipped (foldMap)
  | TargetT -- field is our target type
  | AppT TagTree TagTree -- field involves application of `f` and may require nested use of map/foldMap/traverse
  | TupleT (TagTree,TagTree,List TagTree) -- fields of the tuple
  | FunctionT Polarity' TagTree TagTree -- field is of a function type that uses our hole paramater somewhere
  -- Polarity: 

Eq TagTree where
  x == y = ?sdsdffssdffdf

-- TODO ???
Show TagTree where
  show SkipT = "SkipT"
  show TargetT = "TargetT"
  show (AppT x y) = "AppT"
  show (TupleT x) = "TupleT"
  show (FunctionT p x y) = "FunctionT"


||| Compute a tag tree from a type TTImp, tracking nestings of pi argument polarity
export
ttToTagTree : (target : TTImp) -> TTImp -> TagTree
ttToTagTree t v@(IVar fc nm) = if v == t then TargetT else SkipT
ttToTagTree t (IPi fc rig pinfo mnm argTy retTy) = case (ttToTagTree t argTy) of
    FunctionT p l r => FunctionT Norm (FunctionT (not' p) l r) (ttToTagTree t retTy)
    r => FunctionT Norm r (ttToTagTree t retTy)
ttToTagTree t a@(IApp _ l r) = case unPair a of
    (x :: y :: zs) => TupleT (ttToTagTree t x, ttToTagTree t y, ttToTagTree t <$> zs)
    _             => AppT (ttToTagTree t l) (ttToTagTree t r)
  where
    unPair : TTImp -> List TTImp
    unPair (IApp _ `(Pair ~l) r) = l :: unPair r; unPair tt = [tt]
ttToTagTree t _ = SkipT

hasTarget : TagTree -> Bool
hasTarget SkipT = False
hasTarget TargetT = True
hasTarget (AppT x y) = hasTarget x || hasTarget y
hasTarget (TupleT (x,y,zs)) = hasTarget x || hasTarget y || any hasTarget zs
hasTarget (FunctionT p x y) = hasTarget x || hasTarget y

mutual
  ||| Is the `t`arget type used in a negative argument position?
  ||| e.g. (t -> a) or ((b -> t) -> a)
  ||| Note that nesting to the left continously flips the polarity.
  ||| (neg -> pos) to the left of -> becomes (pos -> neg).
  ||| In effect ((a -> b) -> c) is not contravariant in a, even though (a -> b) is.
  export
  hasNegTargetTT : TagTree -> Bool
  hasNegTargetTT SkipT = False
  hasNegTargetTT TargetT = False
  hasNegTargetTT (AppT x y) = hasNegTargetTT x || hasNegTargetTT y
  hasNegTargetTT (TupleT (x,y,zs)) = hasNegTargetTT x || hasNegTargetTT y || any hasNegTargetTT zs
  hasNegTargetTT (FunctionT Norm l r) = hasTarget' l || hasNegTargetTT r
  hasNegTargetTT (FunctionT Flip l r) = hasTarget' r || hasNegTargetTT l

  private
  hasTarget' : TagTree -> Bool
  hasTarget' SkipT = False
  hasTarget' TargetT = True
  hasTarget' (AppT x y) = hasTarget x || hasTarget y
  hasTarget' (TupleT (x,y,zs)) = hasTarget x || hasTarget y || any hasTarget zs
  hasTarget' f@(FunctionT _ _ _) = hasNegTargetTT f

baf : hasNegTargetTT (ttToTagTree `(b) `((b -> a) -> b)) = False
baf = Refl

baf' : hasNegTargetTT (ttToTagTree `(b) `((b -> a) -> (a -> f b) -> b)) = True
baf' = Refl

baf'' : hasNegTargetTT (ttToTagTree `(b) `((((b -> a) -> a) -> a) -> b)) = True
baf'' = ?dsffsdsfd

hasFunctionT : TagTree -> Bool
hasFunctionT SkipT = False
hasFunctionT TargetT = False
hasFunctionT (AppT x y) = hasFunctionT x || hasFunctionT y
hasFunctionT (TupleT (x,y,zs)) = hasFunctionT x || hasFunctionT y || any hasFunctionT zs
hasFunctionT (FunctionT _ _ _) = True


||| Prune any TagTree branches without TargetT somewhere
||| This prevents wasteful things like casing on tuples without values we care about
export
pruneSkipped : TagTree -> TagTree
pruneSkipped SkipT = SkipT
pruneSkipped TargetT = TargetT
pruneSkipped (AppT x y) = case (hasTarget x, hasTarget y) of
                             (True,True) => AppT (pruneSkipped x) (pruneSkipped y)
                             (False,True) => AppT SkipT (pruneSkipped y)
                             (True,False) => AppT (pruneSkipped x) SkipT
                             _ => SkipT
pruneSkipped (TupleT (x,y,zs)) = case (hasTarget x, hasTarget y, any hasTarget zs) of
                                    (False,False,False) => SkipT
                                    _ => TupleT (pruneSkipped x,pruneSkipped y, map pruneSkipped zs)
pruneSkipped (FunctionT p x y) = case (hasTarget x, hasTarget y) of
                             (True,True) => FunctionT p (pruneSkipped x) (pruneSkipped y)
                             (False,True) => FunctionT p SkipT (pruneSkipped y)
                             (True,False) => FunctionT p (pruneSkipped x) SkipT
                             _ => SkipT
-- ^ Is the above correct? Does pruning not affect polarity?

record FParamCon  where
  constructor MkFConField
  name : Name
  args : List (TagTree, ExplicitArg)

public export
record FParamTypeInfo where
  constructor MkFParamTypeInfo
  name   : Name
  params : Vect (S paramCountMinusOne) (Name,TTImp)
  appliedTy : TTImp -- fully applied type
  oneHoleType : TTImp -- applied type minus hole
  holeType :  (Name,TTImp) -- the hole param
  cons : Vect conCount FParamCon

export
deepestAp : TTImp -> TTImp
deepestAp (IApp fc s u) = deepestAp u
deepestAp tt = tt

-- alternatively could use calcArgTypesWithParams
iVarAnywhere : (name : TTImp) -> TTImp -> Bool
iVarAnywhere n na@(IVar _ _) = n == na
iVarAnywhere n (IApp fc s t) = iVarAnywhere n s || iVarAnywhere n t
iVarAnywhere _ _ = False

-- Special pi case since we can't just map them
export
findAp : (targ : TTImp) -> TTImp -> Maybe TTImp
findAp t (IApp fc s u@(IVar _ _)) = if u == t then Just s else Nothing
findAp t (IApp fc s pi@(IPi _ _ _ _ l r)) = if iVarAnywhere t l || iVarAnywhere t r then Just s else Nothing
findAp t (IApp fc s u) = IApp fc s <$> findAp t u
findAp t _ = Nothing

export
||| Filter used params for ones that are applied to our `l`ast param
||| and also supertypes of those. e.g. g (f a) (h l) implies Functor (g (f a)) and Functor h
argTypesWithParamsAndApps : (taget : TTImp) -> (params : List TTImp) -> List TTImp
argTypesWithParamsAndApps l ss = 
    let b = mapMaybe (findAp l) ss
        c = concatMap (\t => List.mapMaybe (findAp (deepestAp t)) b) b
    in map deepestAp b ++ c
-- ^ find apps that use l at the end:
-- e.g.  `h l --> h`  and  `g (f a) (h l) --> (g (f a)) h`
-- Then also find apps that use those apps:
-- e.g. (g (f a)) h = g (f a)


-- TODO, also consider when layering contras makes them non-contra
-- Does this happen? It sounds familiar
data Borp : Type -> Type -> Type where
  MkBorp : (c -> a -> a -> c -> a -> c) -> Borp c a
Functor (Borp c) where
  map f (MkBorp g) = MkBorp $ \c => ?dsfsdf

export
||| Turn any name into a Basic name
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

varStream : String -> Stream Name
varStream s = map (fromString . ("\{s}_" ++) . show) [the Int 1 ..]

export
toBasicName' : Name -> TTImp
toBasicName' = var . toBasicName

export
||| Determine how nested, by application, our target is.
countLevels : (target : Name) -> TTImp -> Maybe Nat
countLevels t (IApp _ s u) = S <$> countLevels t u
countLevels t (IVar _ nm) = if nm == t then Just 0 else Nothing
countLevels _ _ = Nothing

export
unLevel' : TTImp -> (n ** Vect (S n) TTImp)
unLevel' tt@(IApp _ s u) =
  case unLevel' u of
    (k ** imps) => (S k ** (s :: imps))
unLevel' tt = (Z ** [tt]) -- level 0 is the base

-- TODO make this more reliable. Checking TargetF would help a lot
export
||| Is our target parameter in the datatype itself but not in any constructor fields
isPhantomArg : Name -> DeriveUtil -> Bool
isPhantomArg arg g = let b = filter (not . isRecursive) . concatMap explicitArgs $ g.typeInfo.cons
                         c = (concatMap paramTypes b)
                         c' = filter (iVarAnywhere (var arg)) c
                   in not $ length c' > 0

||| Is our target parameter in the datatype itself but not in any constructor fields
isPhantom : FParamTypeInfo -> Bool
isPhantom fp = any (not . hasTarget) $ concatMap (map fst . args) fp.cons

||| Is our target type used in a pi type
isLastParamInPi : (target : TTImp) -> (body : TTImp) -> Bool
isLastParamInPi t (IApp fc _ _) = False -- starts with app? not pi
isLastParamInPi t tt = isLastParamInPi' t tt
  where
    isLastParamInPi' : (target : TTImp) -> (body : TTImp) -> Bool
    isLastParamInPi' t (IPi fc rig pinfo mnm argTy retTy) = t == argTy || iVarAnywhere t retTy || isLastParamInPi t retTy
    -- isLastParamInPi' t (IPi fc rig pinfo mnm argTy retTy) = t == argTy || t == retTy || isLastParamInPi t retTy
    isLastParamInPi' t (IApp fc s u) = t == s || isLastParamInPi t u
    isLastParamInPi' t tt = False

||| Is our target type used contravariantly in a pi type
isLeftParamOfPi : (target : TTImp) -> (body : TTImp) -> Bool
isLeftParamOfPi t (IPi fc rig pinfo mnm argTy retTy) = t == argTy || isLeftParamOfPi t retTy
isLeftParamOfPi t (IApp fc s u) = isLeftParamOfPi t s || isLeftParamOfPi t u
isLeftParamOfPi t tt = False


makeFParamCon : (holeType : Name) -> ParamCon -> FParamCon
makeFParamCon t (MkParamCon name explicitArgs) =
  MkFConField name $ map (\r => (pruneSkipped $ ttToTagTree (var t) r.tpe, r)) explicitArgs

-- Failure implies its not a `Type -> Type` type
makeFParamTypeInfo : DeriveUtil -> Maybe FParamTypeInfo
makeFParamTypeInfo g = do
    tiParams@(_ :: _)       <- pure g.typeInfo.params | _ => Nothing
    let params = Vect.fromList tiParams
    (holeTypeName, IType _) <- pure $ last params     | _ => Nothing
    let (oneHoleTT,holeTypeTT) = splitLastVar g.appliedType
        fpcons = fromList $ makeFParamCon holeTypeName <$> g.typeInfo.cons
    pure $ MkFParamTypeInfo g.typeInfo.name params g.appliedType oneHoleTT (holeTypeName,holeTypeTT) fpcons
  where
    -- we've already rejected types without proper params so this should be safe
    splitLastVar : TTImp -> (TTImp,TTImp)
    splitLastVar (IApp _ y l) = (y,l)
    splitLastVar tt = (tt,tt)

-- SortedMap has issues reifying the use of lookup :(
-- NameMap : Type -> Type
-- NameMap a = SortedMap Name a
namespace NameMap
  export
  NameMap : Type -> Type
  NameMap a = List (Name,a)

  -- nub gross, but we don't have all that many params to search
  export
  insert : Eq a => Name -> a -> NameMap a -> NameMap a
  insert n1 n2 nm = nub $ (n1,n2) :: nm

  export
  lookup : Name -> NameMap a -> Maybe a
  lookup n nm = List.lookup n nm

  export
  member : Name -> NameMap a -> Bool
  member n nm = isJust $ NameMap.lookup n nm
  
  export
  empty : NameMap a
  empty = []

  export
  mapNameMap : (a -> b) -> NameMap a -> NameMap b
  mapNameMap f nm = Prelude.map (\(x,y) => (x, f y)) nm

  export
  size : NameMap a -> Nat
  size = length

  export
  withStrm : (a -> b -> c) -> NameMap a -> Stream b -> NameMap c
  withStrm f [] (v :: vs) = []
  withStrm f ((n,x) :: xs) (v :: vs) = (n, f x v) :: withStrm f xs vs


collectNames : NameMap Name -> TTImp -> NameMap Name
collectNames m (IVar _ nm) = insert nm nm m
collectNames m (IPi _ rig pinfo mnm argTy retTy)
  = foldl {t=List} collectNames (maybe m (\n => insert n n m) mnm) [argTy,retTy]
collectNames m (IApp _ s t) = foldl {t=List} collectNames m [s,t]
collectNames m _ = m

replaceNames : NameMap Name -> TTImp -> TTImp
replaceNames m (IVar fc nm) = IVar fc $ fromMaybe nm (lookup nm m)
replaceNames m (IPi fc rig pinfo mnm argTy retTy)
  = IPi fc rig pinfo (mnm >>= (`lookup`m)) (replaceNames m argTy) (replaceNames m retTy)
replaceNames m (IApp fc s t) = IApp fc (replaceNames m s) (replaceNames m t)
replaceNames m tt = tt

private
Ord Name where
  compare x y = compare (nameStr x) (nameStr y)

lappend : List a -> Stream a -> Stream a
lappend [] ss = ss
lappend (x :: xs) ss = x :: lappend xs ss

nameSrc : Stream String
nameSrc = numa nats
  where
    alpha : List String
    alpha = ["a","b","c","d","e"]
    numa : Stream Nat -> Stream String
    numa (Z :: ns) = alpha `lappend` numa ns
    numa (n :: ns) = map (++ show n) alpha `lappend` numa ns

export
collectAndReplace : TTImp -> TTImp
collectAndReplace tt =
    let d = collectNames (empty {a=Name}) tt
        rs = withStrm (\x,y => case x of MN _ _ => fromString y; _ => x) d nameSrc
        -- rs = withStrm (\x,y => case x of MN _ _ => fromString y; _ => x) d (map nameStr $ varStream "arg")
    in  replaceNames rs tt

export
oneHoleImplementationType : (iface : TTImp) -> (reqImpls : List Name) -> FParamTypeInfo -> DeriveUtil -> TTImp
oneHoleImplementationType iface reqs fp g =
    let appIface = iface .$ fp.oneHoleType
        functorVars = argTypesWithParamsAndApps (snd fp.holeType) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (iface .$) functorVars ++ map (\n => app (var n) fp.oneHoleType) reqs
        ty = piAllImplicit autoArgs (toList . map fst $ init fp.params)
    -- in collectAndReplace ty
    in ty

------------------------------------------------------------
-- Failure reporting
------------------------------------------------------------

failDerive : (where' : String) -> (why : String) -> String
failDerive where' why = "Failure deriving \{where'}: \{why}"

piFail : String -> (dtName : String) -> String
piFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used in a function type."

contraFail : (impl : String) -> (dtName : String) -> String
contraFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used in argument to a function type."

oneHoleFail : (impl : String) -> (dtName : String) -> String
oneHoleFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its type does not end in Type -> Type."

------------------------------------------------------------

fetchFreshVar : MonadState (Stream Nat) m => String -> m Name
fetchFreshVar s = do (x :: xs) <- get
                     () <- put xs
                     pure $ UN (Basic $ s ++ show x)

replicateA : Applicative m => (n : Nat) -> m a -> m (Vect n a)
replicateA Z act = pure []
replicateA (S k) act = [| act :: replicateA k act |]

||| Stateful so that we can ensure unique variables
export
ttGenMap' : (tt : TagTree) -> (var : TTImp) -> State (Stream Nat) TTImp
ttGenMap' SkipT x = pure x
ttGenMap' TargetT x = pure `(f ~x)
ttGenMap' (AppT l TargetT) x = pure `(map f ~x)
ttGenMap' (AppT l r) x = do
    n <- fetchFreshVar "y"
    pure $ `(map ~(lambdaArg n .=> !(ttGenMap' r (var n))) ~x)
ttGenMap' (TupleT (t1,t2,ts)) x = do
    names <- map var <$> replicateA (2 + length ts) (fetchFreshVar "t")
    let lhs = Vect.foldr1 (\n,acc => `(MkPair ~n ~acc)) names
        tts = zip (t1 :: t2 :: fromList ts) names
    rhs <- Vect.foldr1 (\l,r => `(MkPair ~l ~r)) <$> traverse (uncurry ttGenMap') tts
    pure `(case ~x of ~lhs => ~rhs)
ttGenMap' (FunctionT _ l r) x = do
    n <- fetchFreshVar "p"
    pure $ lambdaArg n .=> !(ttGenMap' r (x .$ !(ttGenMap' l (var n))))


-- fixity of .=> is weird

export
genMapTT' : DeriveUtil -> FParamTypeInfo -> (target : Name) -> TTImp
genMapTT' g fp t = lambdaArg "z" .=> (iCase (var "z") implicitFalse $
                     case (isPhantom fp, length fp.cons) of
                       (_, 0) => [impossibleClause `(_)]
                       (True, _) => [] -- [`(_ = believe_me z)]
                       _ => clauses)
-- genMapTT' g fp t = if isPhantom fp && length fp.cons > 0
                    -- then `(believe_me)
                    -- else lambdaArg "z" .=> iCase (var "z") implicitFalse
                          -- (if length fp.cons == 0
                            --  then [impossibleClause `(_)]
                            --  else clauses)
-- genMapTT' g fp t = lambdaArg "z" .=> iCase (var "z") implicitFalse clauses
  where
    lhss : Vect cc FParamCon -> Vect cc TTImp
    lhss = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

    rhss : Vect cc FParamCon -> Vect cc TTImp
    -- rhss = map (\pc => appAll pc.name (map (\(tag, arg) => (genMap (toBasicName arg.name) arg.tpe) .$ (toBasicName' arg.name)) pc.args))
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) => (evalState nats $ ttGenMap' (pruneSkipped $ ttToTagTree (var t) arg.tpe) (toBasicName' arg.name))) pc.args))

    clauses : List Clause
    clauses = toList $ zipWith (.=) (lhss fp.cons) (rhss fp.cons)

mkFunctorImpl : DeriveUtil -> FParamTypeInfo -> TTImp
mkFunctorImpl g fp = `(MkFunctor $ \f => ~(genMapTT' g fp (fst fp.holeType)))

-- This should reject types where the last arg is used contravariantly anywhere
||| Derives a `Functor` implementation for the given data type
||| and visibility.
export
FunctorVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FunctorVis vis g = do
    let iname = "Functor"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeFParamTypeInfo g
      | _ => fail (oneHoleFail iname dtName)
    when (any hasNegTargetTT (concatMap (map fst . args) fp.cons)) $ fail (contraFail iname dtName) -- reject contravariant uses of the hole type
    pure $ MkInterfaceImpl iname vis []
             (mkFunctorImpl g fp)
             (oneHoleImplementationType `(Functor) [] fp g)

||| Alias for `FunctorVis Public`.
export
Functor : DeriveUtil -> Elab InterfaceImpl
Functor = FunctorVis Public

[EndoS] Semigroup (a -> a) where
  f <+> g = \x => f (g x)

[Endo] Monoid (a -> a) using EndoS where
  neutral = id

public export %inline
defaultFoldr : Foldable t => (func : a -> b -> b) -> (init : b) -> (input : t a) -> b
defaultFoldr f acc xs = foldMap @{%search} @{Endo} f xs acc

-- special case for no cons: impossible pattern
-- special case for phantoms: _ = belive_me, phantoms use their target var nowhere
-- do these cases make sense for Foldable?
export
genFoldMapTT : DeriveUtil -> FParamTypeInfo -> (target : Name) -> TTImp
-- genFoldMapTT g fp t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
--                      then `(believe_me)
--                      else lambdaArg "x" .=> iCase (var "x") implicitFalse
--                           (if length g.typeInfo.cons == 0
--                              then [impossibleClause `(_)]
--                              else clauses)
--   where
--     mutual
--       -- split, make new tags for each, doRules on each, combine
--       doTuple : TTImp -> (k ** Vect (S (S k)) TTImp) -> TTImp
--       doTuple name (k ** fields) =
--             let names = map var $ Stream.take (S (S k)) $ varStream "t"
--                 tags = map (tagField' (fst fp.holeType)) fields
--                 tagged = zip tags names
--                 tupL = foldr1 (\n,ns => `(MkPair ~(n) ~ns) ) names
--                 tupR = foldl1 (\acc,x => `(~acc <+> ~x)) (map (uncurry doRule) tagged)
--             in  iCase name `(_) [tupL .= tupR]

--       doRule : FieldTag -> TTImp -> TTImp
--       doRule SkipF       name = `(neutral)
--       doRule (AppF k)    name = foldl {t=List} (\acc,_ => `(foldMap ~acc)) `(f) (take k [0 ..]) .$ name
--       doRule (TupleF k)  name = doTuple name k
--       doRule FunctionFV  name = name -- Will not occur for Foldable. How to have compiler guarantee?
--       doRule FunctionFCo name = name -- Will not occur for Foldable. How to have compiler guarantee?
--       -- ^ Making compiler checked guarantees for the above two cases seems fairly onerous to me
--       -- with what I've tried so far.

--     lhss : Vect cc FParamCon -> Vect cc TTImp
--     lhss = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

--     rhss : Vect cc FParamCon -> Vect cc TTImp
--     rhss = map (\pc => case (map (\(tag, arg) => doRule tag (toBasicName' arg.name)) pc.args) of
--                          [] => `(neutral) -- case to avoid repeating work, e.g. neutral <+> ...
--                          (r :: rs) => foldl (\acc,x => `(~acc <+> ~x)) r rs)

--     clauses : List Clause
--     clauses = toList $ zipWith (.=) (lhss fp.cons) (rhss fp.cons)

-- This should actually quote a known Foldable and edit it via field-name, to keep up-to-date automatically.
-- e.g.
-- let x : Foldbale (List Char)
--     x = %search
-- z <- quote x
-- impl = [edit foldr field and foldMap fields] z
mkFoldableImpl : DeriveUtil -> FParamTypeInfo -> TTImp
mkFoldableImpl g fp = `(MkFoldable 
                       defaultFoldr
                       (\f,z,t => foldr (flip (.) . flip f) id t z)
                       (\xs => foldr {acc = Lazy Bool} (\ _,_ => False) True xs)
                       (\fm,a0 => foldl (\ma, b => ma >>= flip fm b) (pure a0))
                       (foldr (::) [])
                       (\f => ~(genFoldMapTT g fp (fst fp.holeType)))
                       )

-- This should reject types where the last arg is used in functions
||| Derives a `Foldable` implementation for the given data type
||| and visibility.
export
FoldableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FoldableVis vis g = do
    let iname = "Foldable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeFParamTypeInfo g
      | _ => fail (oneHoleFail iname dtName)
    when (any hasFunctionT (concatMap (map fst . args) fp.cons)) $ fail (piFail iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkFoldableImpl g fp)
             (oneHoleImplementationType `(Foldable) [] fp g)

||| Alias for `FoldableVis Public`.
export
Foldable : DeriveUtil -> Elab InterfaceImpl
Foldable = FoldableVis Public

-- special case for no cons: impossible pattern
-- special case for phantoms: _ = belive_me, phantoms use their target var nowhere
-- do these cases make sense for Foldable?
export
genTraverseTT : DeriveUtil -> FParamTypeInfo -> (target : Name) -> TTImp
-- genTraverseTT g fp t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
--                       then `(believe_me)
--                       else lambdaArg "x" .=> iCase (var "x") implicitFalse
--                            (if length g.typeInfo.cons == 0
--                               then [impossibleClause `(_)]
--                               else clauses)
--   where
--     mutual
--       -- -- split, make new tags for each, doRules on each, recombine
--       -- doTuple : TTImp -> (k ** Vect (S (S k)) TTImp) -> TTImp
--       -- doTuple name (k ** fields) =
--       --       let names = Stream.take (S (S k)) $ map (fromString . ("t_" ++) . show) [the Int 1 ..]
--       --           namedTT = zip (map var names) fields
--       --           tagged = zip (map (tagField' (fst fp.holeType)) fields) namedTT
--       --       in case (init tagged, last tagged) of
--       --             (xs, (ltag,ln,lt)) =>
--       --               let tupL = foldr (\n,ns => `(MkPair ~(n) ~ns) ) ln (map (fst . snd) xs)
--       --                   tupR = foldr (\(tag,n,t),tt => `(MkPair) .$ (doRule (tag,n,t)) .$ tt) (doRule (ltag,ln,lt)) xs
--       --               in  iCase name `(_) [tupL .= tupR]

--       -- split, make new tags for each, doRules on each, combine
--       doTuple : TTImp -> (k ** Vect (S (S k)) TTImp) -> TTImp
--       doTuple name (k ** fields) =
--             let names = map var $ Stream.take (S (S k)) $ varStream "t"
--                 tags = map (tagField' (fst fp.holeType)) fields
--                 tagged = zip tags names
--                 tupL = foldr1 (\n,ns => `(MkPair ~(n) ~ns) ) names
--                 tupR = foldr1 (\t,tt => `(MkPair) .$ t .$ tt) (map (uncurry doRule) tagged)
--             in  iCase name `(_) [tupL .= tupR]

--       doRule : FieldTag -> TTImp -> TTImp
--       doRule SkipF       name = name
--       doRule (AppF k)    name = foldl {t=List} (\acc,_ => `(traverse ~acc)) `(f) (take k [0 ..]) .$ name
--       doRule (TupleF k)  name = doTuple name k
--       doRule FunctionFV  name = name -- Will not occur for Traversable. How to have compiler guarantee?
--       doRule FunctionFCo name = name -- Will not occur for Traversable. How to have compiler guarantee?

--     rhss : Vect cc FParamCon -> Vect cc TTImp
--     rhss = map (\pc => foldl (\acc,x => `(~acc <*> ~x)) `(pure ~(var pc.name))
--                  (map (\(tag, arg) => doRule tag (toBasicName' arg.name)) pc.args))

--     lhss : Vect cc FParamCon -> Vect cc TTImp
--     lhss = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

--     -- rhss : Vect cc FParamCon -> Vect cc TTImp
--     -- rhss = map (\pc => case (map (\(tag, arg) => doRule (tag, toBasicName' arg.name, arg.tpe)) pc.args) of
--     --                      [] => `(neutral)
--     --                      (r :: rs) => foldl (\acc,x => `(~acc <+> ~x)) r rs)

--     clauses : List Clause
--     clauses = toList $ zipWith (.=) (lhss fp.cons) (rhss fp.cons)

mkTraversableImpl : DeriveUtil -> FParamTypeInfo -> TTImp
mkTraversableImpl g fp = `(MkTraversable
                       (\f => ~(genTraverseTT g fp (fst fp.holeType)))
                       )

public export
getBaseImplementation' : (x : Type) -> Elab x
getBaseImplementation' implTy = do
  tpe <- quote implTy
  let d = `( let x = %search in the ~tpe x )
  z <- check {expected=implTy} d
  pure z

||| Derives a `Traversable` implementation for the given data type
||| and visibility.
export
TraversableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
TraversableVis vis g = do
    let iname = "Traversable"
        dtName = nameStr $ g.typeInfo.name
    Just fp <- pure $ makeFParamTypeInfo g
      | _ => fail (oneHoleFail iname dtName)
    when (any hasFunctionT (concatMap (map fst . args) fp.cons)) $ fail (piFail iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkTraversableImpl g fp)
             (oneHoleImplementationType `(Traversable) [`{Functor},`{Foldable}] fp g)

||| Alias for `TraversableVis Public`.
export
Traversable : DeriveUtil -> Elab InterfaceImpl
Traversable = TraversableVis Public

getStuff : Name -> Elab ()
getStuff n = do
  -- tyinfo <- getInfo' n
  eff <- getParamInfo' n
  let g = genericUtil eff
  Just fp <- pure $ makeFParamTypeInfo g
    | _ => fail "no"
  -- r1 <- FunctorVis Public g
  -- r2 <- FoldableVis Public g
  -- logTerm "functorType" 0 "impl" $ impl r1
  -- logTerm "functorType" 0 "type" $ r1.type
  logMsg "wew1" 0 $ show $ map snd fp.params
  logMsg "tags" 0 $ show $ map (map fst . args) fp.cons
  logMsg "wew2" 0 $ show $ g.argTypesWithParams
  logMsg "wew3" 0 $ show $ (argTypesWithParamsAndApps (snd fp.holeType) g.argTypesWithParams)

  
  pure ()

{-

data Raf : Type -> Type -> Type where
  -- MkRaf : a -> b -> Maybe b -> (a,b) -> (a -> a -> b) -> Raf a b
  -- MkRaf : (a,b) -> Raf a b
  -- MkRaf : a -> b -> Maybe b -> (a,b) -> Raf a b
  MkRaf : a -> b -> Maybe b -> (a -> b) -> (a,b,a,Char) -> (Int -> Bool -> Char) -> Raf a b

data Forf a = MkForf (a -> a)
Functor Forf where
  map f (MkForf g) = MkForf $ \x => ?dsfsdf_0 -- contra


data Foo = MkFoo

data FooEnum = FooEnum1 | FooEnum2 | FooEnum3

data FooA a = MkFooA a
%runElab derive' `{FooA} [Functor]
tFooA : let t = (MkFooA 'a') in map Prelude.id t = t
tFooA = Refl

data FooA' : (x : Type) -> Type where
  MkFooA' : a -> FooA' a
%runElab derive' `{FooA'} [Functor]
tFooA' : let t = (MkFooA' 'a') in map Prelude.id t = t
tFooA' = Refl

data FooA2 a = MkFooA2 | MkFooA2' a

%runElab derive' `{FooA2} [Functor]
tFooA2 : let t = (MkFooA2' 'c') in map Prelude.id t = t
tFooA2 = Refl

data FooA3 a = MkFooA3 | MkFooA3' a | MkFooA3'' (FooA3 a)

%runElab derive' `{FooA3} [Functor]
tFooA3 : let t = (MkFooA3'' (MkFooA3' 'c')) in map Prelude.id t = t
tFooA3 = Refl

data FooAF : (Type -> Type) -> Type -> Type where
  MkFooAF : a -> FooAF f a
  MkFooAF' : f a -> FooAF f a
  MkFooAF'' : FooAF f a -> FooAF f a

%runElab derive' `{FooAF} [Functor]
tFooAF : let t = (MkFooAF' {f=Maybe} (Just 'c')) in map Prelude.id t = t
tFooAF = ?sdffd

data FooA4 a = MkFooA4 | MkFooA4' a | MkFooA4'' (FooA3 a) | MkFooA4''' (Either Int (FooA4 a))

%runElab derive' `{FooA4} [Functor]
tFooA4 : let t = (MkFooA4''' (Right $ MkFooA4'' (MkFooA3' 'c'))) in map Prelude.id t = t
tFooA4 = Refl

public export
data FooAK a = MkFooAK

%runElab derive' `{FooAK} [Functor]
tFooAK : let t = MkFooAK in map Prelude.id t = t
tFooAK = Refl

public export
data FooAK2 a b c = MkFooAK2 b

public export
data FooAKG2 : Type -> Type -> Type -> Type where
  MkFooAKG2 : b -> FooAKG2 a b c

public export
record FooAKR2 (a : Type) b (c : Type) where
  constructor MkFooAKR2
  faffo : b
--------------------------------------------------

-- No reason to case, phantoms can merely be treated as the new type
-- A var is phantom if it isn't used anywhere in the constructors
export
Functor FooAK where
  map _ = believe_me

export
Functor (FooAK2 a b) where
  map _ = believe_me 

export
Functor (FooAKR2 a b) where
  map _ = believe_me

export
Functor (FooAKG2 a b) where
  map _ = believe_me

-- similarily for void
-- A var is void when there aren't any constructors to use it
data VoidFoo : Type -> Type where

Functor VoidFoo where
  map _ _ impossible

export
foof : (a -> b) -> VoidFoo a -> VoidFoo b
foof = \f,x => case x of _ impossible

data Foo2 a = MkFoo2 a a

data Tree1 a = Leaf1 | Branch1 (Tree1 a) a (Tree1 a)
data Tree1' a = Leaf1' | Branch1' (Tree1' a) a (Tree1' a)

-- the default generated Foldable for Tree is depth first, as opposed to this which is breadth-first
export
[off] Foldable Tree1 where
  foldr f acc Leaf1 = acc
  foldr f acc (Branch1 x y z) = f y (foldr f (foldr f acc z) x)


data Tree2 a = Leaf2 a | Branch2 (Tree2 a) (Tree2 a)

data Tree3 a = Leaf3 | Branch3 (Tree1 a) a (Tree2 a)

data F1 a b = MkF1 (a -> b)

data F1' a b c = MkF1' (a -> b -> c)

Functor (F1' a b) where
  map f (MkF1' g) = MkF1' $ \q,r => f (g q r)

public export
data F2 a b c = EmptyF2 | PureF2 a | MkF2 c (a -> b)

data F2' : Type -> Type -> Nat -> Type -> Type where
  EmptyF2' : F2' a b 0 c
  PureF2' : a -> F2' a b 1 c
  MkF2' : c -> (a -> b) -> F2' a b 2 c

data F2'' : Type -> Type -> Type -> Type where
  EmptyF2'' : F2'' a b c
  PureF2'' : a -> F2'' a b c
  MkF2'' : c -> Either Char (b -> c) -> F2'' a b c

data F3 : Type -> (Type -> Type) -> Type -> Type where
  MkF3 : (a -> f b) -> F3 a f b

data F4 a b = MkF4 (b -> a)
data F5 : (f : Type -> Type) -> Type -> Type -> Type where
  MkF5 : (b -> f a) -> (a -> f b) -> F5 f a b

-- Functor Tree1 where
--   map f Leaf1 = Leaf1
--   map f (Branch1 x y z) = Branch1 (map f x) (f y) (map f z)

-- Functor Tree2 where
--   map f (Leaf2 x) = Leaf2 (f x)
--   map f (Branch2 x z) = Branch2 (map f x) (map f z)

-- Functor Tree3 where
--   map f Leaf3 = Leaf3
--   map f (Branch3 x y z) = Branch3 (map f x) (f y) (map f z)

Functor (F2 a b) where
  map f EmptyF2 = EmptyF2
  map f (PureF2 x) = PureF2 x
  map f (MkF2 x g) = MkF2 (f x) g

Functor (F1 a) where
  map f (MkF1 g) = MkF1 $ f . g

-- I need to determine if any parameters guard the use of the final param, in which case they also need Functor, e.g.:
Functor f' => Functor (F3 a f') where
  map f (MkF3 g) = MkF3 $ map f . g
-- In the above case idris will be unable to locate an instance for f, if we don't do this
-- This is distinct from if it was, say, (a -> Either a b), since idris can search directly to see if (Either a) has a Functor instance

Functor (F4 a) where
  map f (MkF4 g) = MkF4 $ \b => ?sdfds -- let r = contramap g?dsffsd ?sdfd b

data Foo' : (Type -> Type -> Type) -> Type -> (Type -> Type) -> Type -> Type where
  MkFoo' : g (f b) a -> f a -> a -> Foo' g b f a

Functor f => Functor (g (f b)) => Functor (Foo' g b f) where
  map h (MkFoo' x y z) = MkFoo' (map h x) (map h y) (h z)


Foldable FooA where
  foldr = defaultFoldr
  foldMap f (MkFooA x) = f x

-- F2 demonstrates that if `c` is used nowhere then we are forced to use neutral
-- It also shows that g isn't possible to use, so we don't
Foldable (F2 a b) where
  foldr = defaultFoldr
  foldMap f EmptyF2 = neutral
  foldMap f (PureF2 x) = neutral
  foldMap f (MkF2 x g) = f x

Traversable (F2 a b) where
  traverse f EmptyF2 = pure EmptyF2
  traverse f (PureF2 x) = pure $ PureF2 x
  traverse f (MkF2 x g) = (\r => MkF2 r g) <$> f x

export
infoF2 : TypeInfo
infoF2 = getInfo "F2"

export
infoF3 : TypeInfo
infoF3 = getInfo "F3"

export
infoF4 : ParamTypeInfo
infoF4 = getParamInfo "F4"

export
infoF4F : FParamTypeInfo
infoF4F = case makeFParamTypeInfo (genericUtil infoF4) of
            Just x => x
            Nothing => believe_me 0

data FooTup a = MkFooTup (Int,a,Char)

data FooTup2 a b = MkFooTup2 (Int,a,b,Char)

export
infoFooTup : ParamTypeInfo
infoFooTup = getParamInfo "FooTup"

export
infoFooTup2 : ParamTypeInfo
infoFooTup2 = getParamInfo "FooTup2"


export
infoFooTup2F : FParamTypeInfo
infoFooTup2F = case makeFParamTypeInfo (genericUtil infoFooTup2) of
            Just x => x
            Nothing => believe_me 0

export
infoFooTupF : FParamTypeInfo
infoFooTupF = case makeFParamTypeInfo (genericUtil infoFooTup) of
            Just x => x
            Nothing => believe_me 0

export
infoRaf : ParamTypeInfo
infoRaf = getParamInfo "Raf"

export
infoRafF : FParamTypeInfo
infoRafF = case makeFParamTypeInfo (genericUtil infoRaf) of
            Just x => x
            Nothing => believe_me 0

%runElab derive' `{Raf} [Functor]

borb' : let t = (MkRaf 'a' Z (Just Z) (const Z) ('a',Z,'a','c') (\_,_ => 'f')) in map Prelude.id t = t
borb' = Refl

export
infoFooA4p : ParamTypeInfo
infoFooA4p = getParamInfo "FooA4"

export
infoFooAF : ParamTypeInfo
infoFooAF = getParamInfo "FooAF"

export
infoVoidFoo : ParamTypeInfo
infoVoidFoo = getParamInfo "VoidFoo"

-- %runElab getStuff `{VoidFoo}

data T a = T1 Int a | T2 (T a)
data S a b = S1 (List b) | S2 (a, b, b)
data H : Type -> Type -> Type where
  H1 :  (List b) -> H a b
  H1' : (0 r : b) -> (List b) -> H a b
  H2 : (a, b, b) -> H a b

export
infoT : ParamTypeInfo
infoT = getParamInfo "T"

export
infoS : ParamTypeInfo
infoS = getParamInfo "S"

export
infoH : ParamTypeInfo
infoH = getParamInfo "H"

-- %runElab derive' `{T} [Functor]
-- %runElab derive `{S} [Functor]

-- instance Functor (S a) where
--   fmap f (S1 bs)    = S1 (fmap f bs)
--   fmap f (S2 (p,q)) = S2 (a, fmap f q)



data Fraf : (Type -> Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkFraf : (gorp : g (f a) (h b)) -> Fraf g f h a b
%runElab derive' `{Fraf} [Functor]
tFraf1 : let t = (MkFraf (Right $ Just 'c'))
         in  map {f=Fraf Either Maybe Maybe Bool} Prelude.id t = t
tFraf1 = Refl
tFraf2 : let t = (MkFraf (Left (Nothing {ty = Bool})))
         in  map {f=Fraf Either Maybe Maybe Bool} Prelude.id t = t
tFraf2 = Refl

export
infoFraf : ParamTypeInfo
infoFraf = getParamInfo "Fraf"

export
infoFrafF : FParamTypeInfo
infoFrafF = case makeFParamTypeInfo (genericUtil infoFraf) of
            Just x => x
            Nothing => believe_me 0
%runElab getStuff `{Fraf}


data FooAZ : Type -> Type -> (Type -> Type) -> Type where
  MkFooAZ : a -> FooAZ a b f

-- %runElab derive' `{F1} [Functor] -- function type
-- %runElab derive' `{F4} [Functor] -- contra
-- %runElab derive' `{FooAZ} [Functor] -- not (Type -> Type)


%runElab derive' `{FooA} [Foldable,Traversable]
-- %runElab derive' `{FooA'} [Foldable]
-- %runElab derive' `{FooA2} [Foldable]
-- %runElab derive' `{FooA3} [Foldable]
-- %runElab derive' `{FooAF} [Foldable]
-- %runElab derive' `{F2} [Foldable]

-- next type to explore, one pi is applied recheck the rules
data Bobo : (Type -> Type) -> Type -> Type -> Type where
  MkBobo : (a -> f b) -> Bobo f a b

-- next type to explore, one pi is applied recheck the rules
data BoboT : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type where
  MkBoboT : (f b, b, d a) -> BoboT d f a b

%runElab getStuff `{Bobo}
-- %runElab derive' `{Bobo} [Functor,Foldable,Traversable]
%runElab derive' `{Bobo} [Functor]

%runElab getStuff `{BoboT}
%runElab derive' `{BoboT} [Foldable]

{-
-- This works in haskell, though it's a pain to test!
-- it's just a long-winded way to map f b and f (a -> b)
dd = MkDD (\i1 i2 -> (i1,Just 'c', (\i3 vc -> (Just chr))))
MkDD vc = fmap @(DD Maybe Int) toUpper dd
(x,y,z) = vc 1 2
y = Just 'C'
Just g = z 1 'd'
g 105 = 'I'
g 73 = 'I'
-}

-}
-- This is looping during FunctorVis for some reason. fp is fine
data DooDad : (Type -> Type) -> Type -> Type -> Type where
  -- MkDooDad : f (a -> b) -> DooDad f a b
  MkDooDad : f b -> DooDad f a b

data DooDad2 : (Type -> Type -> Type) -> (Type -> Type)-> (Type -> Type) -> Type -> Type -> Type where
  MkDooDad2 : (g (f a) (h (a -> b))) -> DooDad2 g f h a b

Functor h => Functor (g (f a)) => Functor (DooDad2 g f h a) where
  map f (MkDooDad2 x) = MkDooDad2 $ map (\y => map (\y',b => f (y' b)) y) x


data ContraDad : Type -> Type -> Type where
  -- MkContraDad : (Int -> a) -> ContraDad a
  -- MkContraDad : ((Int -> Int) -> a) -> ContraDad a b
  -- MkContraDad : ((Char -> Int) -> a) -> ContraDad a
  -- MkContraDad : ((b -> a) -> b) -> ContraDad a b
  MkContraDad : ((((b -> a) -> a) -> a) -> b) -> ContraDad a b

Functor (ContraDad a) where
  map f (MkContraDad z) = MkContraDad $ \p0 => f (z (\p1 => p0 (\p2 => p1 (\p3 => p2 (f p3)))))


-- Functor (ContraDad a) where
  -- map f (MkContraDad g) = MkContraDad $ ?sdsdf

-- This is looping during FunctorVis for some reason. fp is fine
data DooDadL : Type -> Type -> Type where
  MkDooDadL : ((b -> a) -> a -> b) -> DooDadL a b

Functor (DooDadL a) where
  map f (MkDooDadL z) = MkDooDadL $ \b1,b2 => f (z (\y => b1 (f y)) b2)
-- given
-- \b1,b2 => f (z (\y => f (b1 y)) b2)

data DooDadLT : (Type -> Type) -> (Type -> Type) -> Type -> Type -> Type -> Type where
  -- MkDooDadLT : ((b -> a) -> (((a,b,c) -> a) -> f (g b)) -> b) -> DooDadLT f g c a b
  -- MkDooDadLT : ((b -> a) -> (f (g b) -> b)) -> DooDadLT f g c a b
  MkDooDadLT : ((a -> b) -> b) -> DooDadLT f g c a b

-- Functor f => Functor g => Functor (DooDadLT f g h i) where
  -- map f (MkDooDadLT g) = MkDooDadLT $ \z => ?dsdsdfsfsdf
-- Functor f => Functor g => Functor (DooDadLT f g h i) where
--   map f (MkDooDadLT z) = MkDooDadLT $ \p0,p2 => f
--     (z (\p1 => p0 (f p1)) (\p3 => map (map ?sdfe)
--          (p2 (\p4 => p3 (case p4 of (t5,t6,t7) => (t5, ?dsf, t7))))))


-- %runElab getStuff `{DooDad}
-- %runElab getStuff `{DooDad2}
%runElab derive' `{DooDad} [Functor]
%runElab derive' `{DooDad2} [Functor]
%runElab derive' `{ContraDad} [Functor]

{-

-- Regrettably, this won't check if Foldable is missing until you use traverse
-- %runElab getStuff `{Tree1}
%runElab derive' `{Tree1} [Functor,Foldable,Traversable]
{-

-- Foldable Tree1 where
  -- foldr f acc xs = ?dsfdsffd

-- Traversable Tree1 where
  -- traverse f x = ?dsfdsffd

-- %runElab derive' `{Tree2} [Foldable]
-- %runElab derive' `{Tree3} [Foldable]

-- This should be an error but it's not! We've already derived this!
-- It won't even error when you use map oddly enough.
Functor FooA where
  map f (MkFooA x) = MkFooA (f x)

-}