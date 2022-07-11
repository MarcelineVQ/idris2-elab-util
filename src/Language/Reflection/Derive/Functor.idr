module Language.Reflection.Derive.Functor

import public Language.Reflection.Pretty
-- import public Language.Reflection.Syntax
-- import public Language.Reflection.Types

-- import Language.Reflection

import Language.Reflection.Derive
%language ElabReflection

--------------------------------------------------
-- MkFC regex:
-- \(MkFC (.*?)(\)\))
-- \(MkFC (.*?)(\)\))(.*?)(\)\))
--------------------------------------------------

data FieldTag
  = SkipF -- field to be left alone, either being placed back in as-is (map) or skipped (foldMap)
  | TargetF -- field can have `f` applied directly
  | AppF Nat -- depth -- field will require a nested use of map/foldMap/traverse
  | TupleF Nat -- width
  | FunctionFV -- field is of a function type that uses our hole paramater somewhere
  | FunctionFCo -- co being a covariant use of our hole parameter

sameTag : FieldTag -> FieldTag -> Bool
sameTag SkipF       SkipF       = True
sameTag TargetF     TargetF     = True
sameTag (AppF _)    (AppF _)    = True
sameTag (TupleF _)  (TupleF _)  = True
sameTag FunctionFV  FunctionFV  = True
sameTag FunctionFCo FunctionFCo = True
sameTag _           _           = False

record FParamCon  where
  constructor MkFConField
  name : Name
  args : List (FieldTag, ExplicitArg)
  -- fieldtag assists in making lhs = rhs and also for quick checking of the form. e.g., we can ask if there's any function types, and further if any of them are contra

public export
record FParamTypeInfo where
  constructor MkFParamTypeInfo
  name   : Name
  params : Vect (S paramCountMinusOne) (Name,TTImp)
  appliedTy : TTImp -- fully applied type
  oneHoleType : TTImp -- applied type minus hole
  holeType :  (Name,TTImp) -- the hole param
  cons : Vect conCount FParamCon

fpHasTag : FParamTypeInfo -> FieldTag -> Bool
fpHasTag fp tag = or $ map (\pc => delay $ any (\(t,_) => sameTag tag t) pc.args) fp.cons

{-
IApp _ -- potential
  (IApp _ -- potential
    (IVar _ (UN (Basic "g"))) -- potential
    (IApp _ -- potential
      (IVar _ (UN (Basic "f"))) -- potential
      (IVar _ (UN (Basic "a"))))) -- potential
  (IApp _
    (IVar _ (UN (Basic "h"))) -- potential
    (IVar _ (UN (Basic "b")))) -- target
-}

-- TODO, is this good enough? What about some case like:
-- argTypesWithParamsAndApps (var b) [g (f a) (h b)] = ???
-- clearly b is used but it's not a direct application.
-- Observe Fraf below, which does this.
-- So what I need is to find (h b), like I do anyway, but also then find uses of (h b)
export
deepestAp : TTImp -> TTImp
deepestAp (IApp fc s u) = deepestAp u
deepestAp tt = tt

-- searchAp : (target : TTImp) -> TTImp -> (TTImp -> b) -> Maybe b

export
findAp : (targ : TTImp) -> TTImp -> Maybe TTImp
findAp t (IApp fc s u@(IVar _ _)) = if u == t then Just s else Nothing
findAp t (IApp fc s u) = IApp fc s <$> findAp t u
findAp t _ = Nothing

export
||| Filter used params for ones that are applied to our `l`ast param
||| and also supertypes of those. e.g. g (f a) (h b) implies Functor (g (f a)) and Functor h
argTypesWithParamsAndApps : (taget : TTImp) -> (params : List TTImp) -> List TTImp
argTypesWithParamsAndApps l ss = 
    let b = mapMaybe (findAp l) ss
        c = concatMap (\t => List.mapMaybe (findAp (deepestAp t)) b) b
    in map deepestAp b ++ c

-- TODO, also consider when layering contras makes them non-contra
-- Does this happen? It sounds familiar
data Borp : Type -> Type -> Type where
  MkBorp : (c -> a -> a -> c -> a -> c) -> Borp c a
Functor (Borp c) where
  map f (MkBorp g) = MkBorp $ \c => ?dsfsdf

-- TODO As written my machinery fails to find uses of b in Fraf at all!

-- Functor (g (f a)) => Functor h => Functor (Fraf g f h a) where
--   map d (MkFraf gorp) = MkFraf $ map (map d) gorp

export
||| Turn any name into a Basic name
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

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
||| Apply an arbitrary nesting of TTImps
||| e.g. appLevels 3 `{k} `(map) = map (map (map k))
appLevels : Name -> TTImp -> Nat -> TTImp
appLevels n _  Z = var n
appLevels n fn (S k) = fn .$ (appLevels n fn k)

iVarAnywhere : (name : Name) -> TTImp -> Bool
iVarAnywhere n (IVar _ na) = n == na
iVarAnywhere n (IApp fc s t) = iVarAnywhere n s || iVarAnywhere n t
iVarAnywhere _ _ = False

export
||| Is our target parameter in the datatype itself but not in any constructor fields
isPhantomArg : Name -> DeriveUtil -> Bool
isPhantomArg arg g = let b = filter (not . isRecursive) . concatMap explicitArgs $ g.typeInfo.cons
                         c = (concatMap paramTypes b)
                        --  c' = filter (\case IVar _ na => na == arg; _ => False) c
                         c' = filter (iVarAnywhere arg) c
                   in not $ length c' > 0

||| Is our target type used in a pi type
isLastParamInPi : (target : TTImp) -> (body : TTImp) -> Bool
isLastParamInPi t (IPi fc rig pinfo mnm argTy retTy) = t == argTy || t == retTy || isLastParamInPi t retTy
isLastParamInPi t (IApp fc s u) = isLastParamInPi t s || isLastParamInPi t u
isLastParamInPi t tt = False

||| Is our target type used contravariantly in a pi type
isLeftParamOfPi : (target : TTImp) -> (body : TTImp) -> Bool
isLeftParamOfPi t (IPi fc rig pinfo mnm argTy retTy) = t == argTy || isLeftParamOfPi t retTy
isLeftParamOfPi t (IApp fc s u) = isLeftParamOfPi t s || isLeftParamOfPi t u
isLeftParamOfPi t tt = False


-- Doesn't really need to be Vect given how we use it so far
export
unTuple' : (tupName : Name) -> TTImp -> (n ** Vect n TTImp)
unTuple' tupName tt@(IApp _ (IApp _ (IVar _ nm) l) r) =
  case unTuple' tupName r of
    (k ** imps) => if toBasicName nm == toBasicName tupName then (S k ** (l :: imps)) else (k ** imps)
unTuple' tupName tt = (1 ** [tt])

export
unTuple'' : (tupName : Name) -> TTImp -> List TTImp
unTuple'' tupName tt@(IApp _ (IApp _ (IVar _ nm) l) r) =
  case unTuple'' tupName r of
    imps => if toBasicName nm == toBasicName tupName then (l :: imps) else imps
unTuple'' tupName tt = [tt]

tagField' : (holeType : Name) -> (arg : TTImp) -> FieldTag
tagField' t arg = case unTuple' "Pair" arg of
  (S (S z) ** xs) => TupleF (S (S z))
  _               => if isLeftParamOfPi (var t) arg
                      then FunctionFCo -- target is a contravariant argument to a pi type
                      else if isLastParamInPi (var t) arg
                        then FunctionFV -- target is an argument to a pi type
                        else case countLevels t arg of
                          Nothing => SkipF   -- target not in field's type
                          Just Z  => TargetF -- target is field's only type
                          Just n  => AppF n  -- target is nested in field's type

makeFParamCon : (holeType : Name) -> ParamCon -> FParamCon
makeFParamCon t (MkParamCon name explicitArgs) =
  MkFConField name $ map (\r => (tagField' t r.tpe, r)) explicitArgs

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

export
oneHoleImplementationType : (iface : TTImp) -> (reqImpls : List Name) -> FParamTypeInfo -> DeriveUtil -> TTImp
oneHoleImplementationType iface reqs fp g =
    let appIface = iface .$ fp.oneHoleType
        functorVars = argTypesWithParamsAndApps (snd fp.holeType) g.argTypesWithParams
        autoArgs = piAllAuto appIface $ map (iface .$) functorVars ++ map (\n => app (var n) fp.oneHoleType) reqs
     in piAllImplicit autoArgs (toList . map fst $ init fp.params)

------------------------------------------------------------
-- Failure reporting
------------------------------------------------------------

failDerive : (where' : String) -> (why : String) -> String
failDerive where' why = "Failure deriving \{where'}: \{why}"

piFail : String -> (dtName : String) -> String
piFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used in a function type."

contraFail : (impl : String) -> (dtName : String) -> String
contraFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its final parameter is used contravariantly in a function type."

oneHoleFail : (impl : String) -> (dtName : String) -> String
oneHoleFail s dtName = failDerive (s ++ " for \{dtName}") "Can't be derived as its type does not end in Type -> Type."

------------------------------------------------------------

appNE : (xs : List a) -> (l : a) -> NonEmpty (xs ++ [l])
appNE [] l = IsNonEmpty
appNE (x :: xs) l = IsNonEmpty


export
genMapTT : DeriveUtil -> FParamTypeInfo -> (target : Name) -> TTImp
genMapTT g fp t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
                    then `(believe_me)
                    else lambdaArg "z" .=> iCase (var "z") implicitFalse
                          (if length g.typeInfo.cons == 0
                             then [impossibleClause `(_)]
                             else clauses)
  where
    run : Name -> TTImp -> TTImp
    run n a = fromMaybe (toBasicName' n) (appLevels "f" `(map) <$> countLevels t a)

    doPi : TTImp -> TTImp -> TTImp
    doPi name tt = case unPi tt of
                (x, y) => let names = map (fromString . ("p_" ++) . show) [1 .. length x]
                              args = zip names x
                          in  foldr (\(n,arg),tt => lambdaArg n .=> tt) (var "f" .$ foldl (.$) name (map var names)) args

    mutual
      -- split, make new tags for each, doRules on each, recombine
      -- should actually check in doRule if the tuple uses our target type in the first place
      doTuple : TTImp -> TTImp -> TTImp
      doTuple name tt' =
        case unTuple'' "Pair" tt' of -- repeated work, bundle this in the tag?
          [] => `(?asdSDfd) -- won't happen
          ts@(_::_) => 
            let count = length ts
                names = map (fromString . ("t_" ++) . show) [1 .. count]
                namedTT = zip (map var names) ts
                tagged = zip (map (tagField' (fst fp.holeType)) ts) namedTT
            in case splitAt (count `minus` 1) tagged of
                  (xs,[(ltag,ln,lt)]) =>
                    let tupL = foldr (\n,ns => `(MkPair ~(n) ~ns) ) ln (map (fst . snd) xs)
                        tupR = foldr (\(tag,n,t),tt => `(MkPair) .$ (doRule (tag,n,t)) .$ tt) (doRule (ltag,ln,lt)) xs
                    in  iCase name `(_) [tupL .= tupR]
                  _ => `(?dsdffd) -- won't happen

      doRule : (FieldTag, TTImp, TTImp) -> TTImp
      doRule (SkipF, name, tpe) = name
      doRule (TargetF, name, tpe) = appLevels "f" `(map) Z .$ name
      doRule ((AppF k), name, tpe) = appLevels "f" `(map) k .$ name
      doRule ((TupleF k), name, tpe) = doTuple name tpe
      doRule (FunctionFV, name, tpe) = doPi name tpe
      doRule (FunctionFCo, name, tpe) = name -- Will not occur.

    lhss : Vect cc FParamCon -> Vect cc TTImp
    lhss = map (\pc => appNames pc.name (map (toBasicName . name . snd) pc.args))

    rhss : Vect cc FParamCon -> Vect cc TTImp
    rhss = map (\pc => appAll pc.name (map (\(tag, arg) => doRule (tag, toBasicName' arg.name, arg.tpe)) pc.args))

    clauses : List Clause
    clauses = toList $ zipWith (.=) (lhss fp.cons) (rhss fp.cons)

mkFunctorImpl : DeriveUtil -> FParamTypeInfo -> TTImp
mkFunctorImpl g fp = `(MkFunctor $ \f => ~(genMapTT g fp (fst fp.holeType)))

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
    when (fpHasTag fp FunctionFCo) $ fail (contraFail iname dtName) -- reject contravariant uses of the hole type
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
genFoldMapTT : DeriveUtil -> (target : Name) -> TTImp
genFoldMapTT g t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
                     then `(believe_me)
                     else lambdaArg "x" .=> iCase (var "x") implicitFalse
                          (if length g.typeInfo.cons == 0
                             then [impossibleClause `(_)]
                             else clauses)
  where
    -- countLevels is what's filtering un-needed arguments while it also checks the depth of foldMaps needed
    doRule : ExplicitArg -> Maybe TTImp
    doRule (MkExplicitArg name tpe paramTypes isRecursive _) =
      [| (appLevels "f" `(foldMap) <$> countLevels t tpe) .$ Just (toBasicName' name) |]

    lhss : List ParamCon -> List TTImp
    lhss = map (\pc => appNames pc.name (map (toBasicName . name) pc.explicitArgs))

    rhss : List ParamCon -> List TTImp
    rhss = map (\pc => case (mapMaybe doRule pc.explicitArgs) of
                         [] => `(neutral)
                         (r :: rs) => foldl (\acc,x => `(~acc <+> ~x)) r rs)

    clauses : List Clause
    clauses = zipWith (.=) (lhss g.typeInfo.cons) (rhss g.typeInfo.cons)

-- This should actually quote a known Foldable and edit it via field-name, to keep up-to-date automatically.
-- e.g.
-- let x : Foldbale (List Char)
--     x = %search
-- z <- quote x
-- impl = [edit foldr field and foldMap fields] z
mkFoldableImpl : DeriveUtil -> TTImp
mkFoldableImpl g = `(MkFoldable 
                       defaultFoldr
                       (\f,z,t => foldr (flip (.) . flip f) id t z)
                       (\xs => foldr {acc = Lazy Bool} (\ _,_ => False) True xs)
                       (\fm,a0 => foldl (\ma, b => ma >>= flip fm b) (pure a0))
                       (foldr (::) [])
                       (\f => ~(genFoldMapTT g (fromMaybe "notAFoldableType" . map fst $ last' g.typeInfo.params)))
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
    when (fpHasTag fp FunctionFV) $ fail (piFail iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkFoldableImpl g)
             (oneHoleImplementationType `(Foldable) [] fp g)

||| Alias for `FoldableVis Public`.
export
Foldable : DeriveUtil -> Elab InterfaceImpl
Foldable = FoldableVis Public

-- special case for no cons: impossible pattern
-- special case for phantoms: _ = belive_me, phantoms use their target var nowhere
-- do these cases make sense for Foldable?
export
genTraverseTT : DeriveUtil -> (target : Name) -> TTImp
genTraverseTT g t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
                      then `(believe_me)
                      else lambdaArg "x" .=> iCase (var "x") implicitFalse
                           (if length g.typeInfo.cons == 0
                              then [impossibleClause `(_)]
                              else clauses)
  where
    -- countLevels is what's filtering un-needed arguments while it also checks the depth of foldMaps needed
    doRule : ExplicitArg -> TTImp
    doRule (MkExplicitArg name tpe paramTypes isRecursive _) = fromMaybe (toBasicName' name) $
      [| (appLevels "f" `(traverse) <$> countLevels t tpe) .$ Just (toBasicName' name) |]

    lhss : List ParamCon -> List TTImp
    lhss = map (\pc => appNames pc.name (map (toBasicName . name) pc.explicitArgs))

    rhss : List ParamCon -> List TTImp
    rhss = map (\pc => foldl (\acc,x => `(~acc <*> ~x)) `(pure ~(var pc.name))
                 (map doRule pc.explicitArgs))

    clauses : List Clause
    clauses = zipWith (.=) (lhss g.typeInfo.cons) (rhss g.typeInfo.cons)

mkTraversableImpl : DeriveUtil -> TTImp
mkTraversableImpl g = `(MkTraversable
                       (\f => ~(genTraverseTT g (fromMaybe "notATraversableType" . map fst $ last' g.typeInfo.params)))
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
    when (fpHasTag fp FunctionFV) $ fail (piFail iname dtName) -- reject uses of the hole type in functions
    pure $ MkInterfaceImpl iname vis []
             (mkTraversableImpl g)
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
  r <- FunctorVis Public g
  logTerm "functorType" 0 "" $ impl r
  logTerm "functorType" 0 "" $ r.type
  logMsg "wew" 0 $ show fp.params

  
  pure ()

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

-- %runElab derive' `{FooA} [Functor,Foldable,Traversable]
-- %runElab derive' `{FooA'} [Foldable]
-- %runElab derive' `{FooA2} [Foldable]
-- %runElab derive' `{FooA3} [Foldable]
-- %runElab derive' `{FooAF} [Foldable]
-- %runElab derive' `{F2} [Foldable]

-- Regrettably, this won't check if Foldable is missing until you use traverse
%runElab derive' `{Tree1} [Functor,Traversable]


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
