module Language.Reflection.Derive.Functor

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types

import System

import Language.Reflection
import Language.Reflection.Syntax

import Prelude.Interfaces -- MkFunctor

import Data.String
import Text.PrettyPrint.Prettyprinter.Doc
import Text.PrettyPrint.Prettyprinter.Render.String

import Data.Contravariant

import Language.Reflection.Derive
%language ElabReflection

data Foo = MkFoo

data FooEnum = FooEnum1 | FooEnum2 | FooEnum3

data FooA a = MkFooA a
data FooA' : (x : Type) -> Type where
  MkFooA' : a -> FooA' a

data FooA2 a = MkFooA2 | MkFooA2' a

data FooA3 a = MkFooA3 | MkFooA3' a | MkFooA3'' (FooA3 a)

data FooAF : (Type -> Type) -> Type -> Type where
  MkFooAF : a -> FooAF f a
  MkFooAF' : f a -> FooAF f a
  MkFooAF'' : FooAF f a -> FooAF f a


data FooA4 a = MkFooA4 | MkFooA4' a | MkFooA4'' (FooA3 a) | MkFooA4''' (Either Int (FooA4 a))

public export
data FooAK a = MkFooAK

--------------------------------------------------
-- These constructors are all the same
--------------------------------------------------
{-
MkData FooAK2
                  (IPi.  (MW ExplicitArg : IType)
                      -> (MW ExplicitArg : IType)
                      -> (MW ExplicitArg : IType)
                      -> IType)
                  []
                  [ MkTy MkFooAK2
                         (IPi.  (MW ExplicitArg : IBindVar b)
                             -> (IApp. IVar FooAK2
                                     $ IBindVar a
                                     $ IBindVar b
                                     $ IBindVar c)) ]
-}
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

Functor Tree1 where
  map f Leaf1 = Leaf1
  map f (Branch1 x y z) = Branch1 (map f x) (f y) (map f z)

Functor Tree2 where
  map f (Leaf2 x) = Leaf2 (f x)
  map f (Branch2 x z) = Branch2 (map f x) (map f z)

Functor Tree3 where
  map f Leaf3 = Leaf3
  map f (Branch3 x y z) = Branch3 (map f x) (f y) (map f z)

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

comap : Functor f => (a -> b) -> (f b -> f a)
comap g x = ?comap_rhs


data Casetag = DoNothing | ApplyF | FmapF | Func

--------------------------------------------------

%macro
spitError : String -> Elab a
spitError = fail

export
||| Does the datatype have the shape: data Foo : ... -> Type -> Type where ...
hasOneHoleShape : Data -> Bool
hasOneHoleShape = \case (MkData _ _ tycon _ datacons) => examineTyCon tycon
                        (MkLater _ _ tycon) => examineTyCon tycon
  where
    examineTyCon : (tycon : TTImp) -> Bool
    examineTyCon (IPi _ _ _ _ (IType _) (IType _)) = True
    examineTyCon (IPi _ _ _ _ _ retTy) = examineTyCon retTy
    examineTyCon _ = False

hasOneHoleShape' : ParamTypeInfo -> Bool
hasOneHoleShape' pt = case last' (params pt) of
                   Just (_, IType _) => True; _ => False

init' : List a -> List a
init' (x :: xs@(_ :: _)) = x :: init xs
init' [x] = []
init' [] = []


public export
record FParamTypeInfo where
  constructor MkFParamTypeInfo
  name   : Name
  params : List1 (Name,TTImp)
  cons   : List ParamCon

record DeriveUtil' where
  constructor MkDeriveUtil

  ||| The underlying type info containing the list and names
  ||| of data constructors plus their arguments as well as
  ||| the data type's name and type arguments.
  typeInfo           : FParamTypeInfo

  ||| Split fully applied data type, i.e. (`var "Either" .$ var "a", var "b")
  oneHoleAppliedType        : (TTImp,TTImp)

  ||| The names of type parameters
  paramNames         : List1 Name

  ||| Types of constructor arguments where at least one
  ||| type parameter makes an appearance. These are the
  ||| `tpe` fields of `ExplicitArg` where `hasParam`
  ||| is set to true and `isRecursive` is set
  ||| to false. See the documentation of `ExplicitArg`
  ||| when this is the case
  argTypesWithParams : List TTImp


data Foo' : (Type -> Type -> Type) -> Type -> (Type -> Type) -> Type -> Type where
  MkFoo' : g (f b) a -> f a -> a -> Foo' g b f a

Functor f => Functor (g (f b)) => Functor (Foo' g b f) where
  map h (MkFoo' x y z) = MkFoo' (map h x) (map h y) (h z)

-- write way to determine that a functor for g and f are needed.
-- check is the left/innermost of App is a param and the
-- right/outermost of App is our dropped param

-- It's becoming clear I want a type to track the dropped parameter and the
-- one-hole full type

-- need a way to ask for other Functor instances e.g. with MkFoo : f (g a)
-- iow we need to check what fields use a AND check which of those are direct
-- applications of parameters. argTypesWithParams are merely used vars
-- data Foo g f a = MkFoo (g (f a) a) a

export
||| Filter used params for ones that are applied to our `l`ast param
argTypesWithParamsAndApps : TTImp -> List TTImp -> List TTImp
argTypesWithParamsAndApps l ss = mapMaybe slice ss
  where
    slice : TTImp -> Maybe TTImp
    slice (IApp fc s u) = if u == l then Just s else Nothing
    slice _ = Nothing

export
oneHoleImplementationType : (iface : TTImp) -> DeriveUtil -> TTImp
oneHoleImplementationType iface (MkDeriveUtil _ appTp names argTypesWithParams) =
    let (vars,l) = dropLastVar appTp
        appIface = iface .$ vars
        mapTemplate = appIface
        functorVars = argTypesWithParamsAndApps l argTypesWithParams
        autoArgs = piAllAuto appIface $ map (iface .$) functorVars
     in piAllImplicit autoArgs (init' names)
  where
    dropLastVar : TTImp -> (TTImp,TTImp)
    dropLastVar (IApp _ y l) = (y,l)
    dropLastVar tt = (tt,tt)


export
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

export
toBasicName' : Name -> TTImp
toBasicName' = var . UN . Basic . nameStr

export
countLevels : (target : Name) -> TTImp -> Maybe Nat
countLevels t (IApp _ s u) = S <$> countLevels t u
countLevels t (IVar _ nm) = if nm == t then Just 0 else Nothing
countLevels _ _ = Nothing

export
countTupleLevels : TTImp -> Nat
countTupleLevels (IApp _ (IApp _ (IVar _ "Pair") _) u) = S $ countTupleLevels u
countTupleLevels _ = 0

export
appLevels : Name -> TTImp -> Nat -> TTImp
appLevels n _  Z = var n
appLevels n fn (S k) = fn .$ (appLevels n fn k)

export
isPhantomArg : Name -> DeriveUtil -> Bool
isPhantomArg arg g = let b = filter (not . isRecursive) . concatMap explicitArgs $ g.typeInfo.cons
                         c = (concatMap paramTypes b)
                         c' = filter (\case IVar _ na => na == arg; _ => False) c
                   in not $ length c' > 0

export
specialCases : (target : Name) -> DeriveUtil -> List Clause -> List Clause
specialCases t g cs = if length (g.typeInfo.cons) == 0
                         then [impossibleClause `(_)]
                         else if isPhantomArg t g
                                 then [`(_) .= `(believe_me)]
                                 else cs

Functor (F1' a b) where
  map f (MkF1' g) = MkF1' $ \q,r => f (g q r)

peepo : Name -> TTImp -> (List (Arg False), TTImp) -> Maybe TTImp
peepo n fn ([], (IVar _ nm)) = if n == nm then Just ?dsffd else Nothing
peepo n fn ([], _) = Nothing
peepo n fn (((MkArg count piInfo name type) :: xs), y) = ?dsf_3

export
isTuple : TTImp -> Bool
isTuple (IApp _ s u) = isTuple s
isTuple (IVar _ nm) = if toBasicName nm == "Pair" then True else False
isTuple _ = False

-- make a pattern for each constructor based on the type, fill the rhs in based on the rules
-- special case for phantoms: _ = believe_me, phantoms use their target var nowhere
-- special case for no cons: impossible pattern
export
genMapTT : DeriveUtil -> (funImpl : Name) -> (target : Name) -> TTImp
genMapTT g fn t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
                     then `(believe_me)
                     else lambdaArg "x" .=> iCase (var "x") implicitFalse
                          (if length g.typeInfo.cons == 0
                              then [impossibleClause `(_)]
                              else clauses)
  where
    doRule : ExplicitArg -> TTImp
    doRule (MkExplicitArg name tpe paramTypes isRecursive _) = fromMaybe (toBasicName' name) $ ru tpe
      where
        ru : TTImp -> Maybe TTImp
        -- Special tuple case
        -- Tuple cases are basically bundles of fields
        ru a@(IApp _ s u) = if not (isTuple a)
          then [| (appLevels fn `(map) <$> countLevels t a) .$ Just (toBasicName' name) |]
          else let tsize = countTupleLevels a
               in Nothing --Just $ iCase (toBasicName' name) implicitFalse $ ?dffd
        -- Special function case
        ru p@(IPi _ rig pinfo mnm argTy retTy) = peepo t (var fn) (unPi p)
        -- General case, cover bare IVars and Apps
        ru tt = [| (appLevels fn `(map) <$> countLevels t tt) .$ Just (toBasicName' name) |]

    lhss : List ParamCon -> List TTImp
    lhss = map (\pc => appNames pc.name (map (toBasicName . name) pc.explicitArgs))

    rhss : List ParamCon -> List TTImp
    rhss = map (\pc => appAll pc.name (map doRule pc.explicitArgs))

    clauses : List Clause
    clauses = zipWith (.=) (lhss g.typeInfo.cons) (rhss g.typeInfo.cons)

mkFunctorImpl : DeriveUtil -> TTImp
mkFunctorImpl g = `(MkFunctor) .$ (lambdaArg "f" .=> (genMapTT g "f" (fromMaybe "notAFunctorableType" . map fst $ last' g.typeInfo.params)))

-- This should reject types where the last arg is used contravariantly anywhere
||| Derives a `Functor` implementation for the given data type
||| and visibility.
export
FunctorVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FunctorVis vis g = do
  if hasOneHoleShape' (g.typeInfo)
    then pure $ MkInterfaceImpl "Functor" vis [] (mkFunctorImpl g) (oneHoleImplementationType `(Functor) g)
    else fail $ show g.typeInfo.name ++ "'s type does not end in Type -> Type, and so cannot derive Functor."

||| Alias for `EqVis Public`.
export
Functor : DeriveUtil -> Elab InterfaceImpl
Functor = FunctorVis Public

[EndoS] Semigroup (a -> a) where
  f <+> g = \x => f (g x)

[Endo] Monoid (a -> a) using EndoS where
  neutral = id

public export %inline
defaultFoldr : (tee : Foldable t) => (func : a -> b -> b) -> (init : b) -> (input : t a) -> b
defaultFoldr f acc xs = foldMap @{tee} @{Endo} f xs acc

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


-- special case for no cons: impossible pattern
-- special case for phantoms: _ = belive_me, phantoms use their target var nowhere
-- do these cases make sense for Foldable?
export
genFoldMapTT : DeriveUtil -> (funImpl : Name) -> (target : Name) -> TTImp
genFoldMapTT g fn t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
                     then `(believe_me)
                     else lambdaArg "x" .=> iCase (var "x") implicitFalse
                          (if length g.typeInfo.cons == 0
                              then [impossibleClause `(_)]
                              else clauses)
  where
    -- countLevels is what's filtering un-needed arguments while it also checks the depth of foldMaps needed
    doRule : ExplicitArg -> Maybe TTImp
    doRule (MkExplicitArg name tpe paramTypes isRecursive _) =
      [| (appLevels fn `(foldMap) <$> countLevels t tpe) .$ Just (toBasicName' name) |]

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
                       (\f => ~(genFoldMapTT g "f" (fromMaybe "notAFoldableType" . map fst $ last' g.typeInfo.params)))
                       )

-- This should reject types where the last arg is used in functions
||| Derives a `Foldable` implementation for the given data type
||| and visibility.
export
FoldableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
FoldableVis vis g = if hasOneHoleShape' (g.typeInfo) {- also check that no function types use the hole type -}
    then pure $ MkInterfaceImpl "Foldable" vis [] (mkFoldableImpl g) (oneHoleImplementationType `(Foldable) g)
    else fail $ show g.typeInfo.name ++ "'s type does not end in Type -> Type, and so cannot derive Foldable."
                    
||| Alias for `EqVis Public`.
export
Foldable : DeriveUtil -> Elab InterfaceImpl
Foldable = FoldableVis Public

-- special case for no cons: impossible pattern
-- special case for phantoms: _ = belive_me, phantoms use their target var nowhere
-- do these cases make sense for Foldable?
export
genTraverseTT : DeriveUtil -> (funImpl : Name) -> (target : Name) -> TTImp
genTraverseTT g fn t = if isPhantomArg t g && length (g.typeInfo.cons) > 0
                     then `(believe_me)
                     else lambdaArg "x" .=> iCase (var "x") implicitFalse
                          (if length g.typeInfo.cons == 0
                              then [impossibleClause `(_)]
                              else clauses)
  where
    -- countLevels is what's filtering un-needed arguments while it also checks the depth of foldMaps needed
    doRule : ExplicitArg -> TTImp
    doRule (MkExplicitArg name tpe paramTypes isRecursive _) = fromMaybe (toBasicName' name) $
      [| (appLevels fn `(traverse) <$> countLevels t tpe) .$ Just (toBasicName' name) |]


    lhss : List ParamCon -> List TTImp
    lhss = map (\pc => appNames pc.name (map (toBasicName . name) pc.explicitArgs))

    rhss : List ParamCon -> List TTImp
    rhss = map (\pc => foldl (\acc,x => `(~acc <*> ~x)) `(pure ~(var pc.name))
                 (map doRule pc.explicitArgs))

    clauses : List Clause
    clauses = zipWith (.=) (lhss g.typeInfo.cons) (rhss g.typeInfo.cons)

mkTraversableImpl : DeriveUtil -> TTImp
mkTraversableImpl g = `(MkTraversable
                       (\f => ~(genTraverseTT g "f" (fromMaybe "notATraversableType" . map fst $ last' g.typeInfo.params)))
                       )

-- This should reject types where the last arg is used in functions
||| Derives a `Traversable` implementation for the given data type
||| and visibility.
export
TraversableVis : Visibility -> DeriveUtil -> Elab InterfaceImpl
TraversableVis vis g = if hasOneHoleShape' (g.typeInfo) {- also check that no function types use the hole type -}
    then pure $ MkInterfaceImpl "Traversable" vis [] (mkTraversableImpl g) (oneHoleImplementationType `(Traversable) g)
    else fail $ show g.typeInfo.name ++ "'s type does not end in Type -> Type, and so cannot derive Traversable."
                    
||| Alias for `EqVis Public`.
export
Traversable : DeriveUtil -> Elab InterfaceImpl
Traversable = TraversableVis Public

-- for Foo a = MkFoo a  get con infos
-- filter each con for whether they mention `a` mebership
-- non-mention means we don't mess with it, `id`, use means we apply `f` or `map f` as appropriate

-- in Foo2, the type of Foo2 is Type -> Type, the type of MkFoo2 is a -> a -> MkFoo2 a
-- We only want to fucks with types that end in Type -> Type

getStuff : Elaboration m => Name -> m ()
getStuff n = do
  -- tyinfo <- getInfo' n
  eff <- getParamInfo' n
  -- logMsg "" 0 (show $ tyinfo.name)
  -- the pprinter does an assload of nat figuring that shits up the compile time
  -- logMsg "freaf" 0 $ renderString . layoutPretty defaultLayoutOptions $ (indent 2 $ vsep ["", pretty {ann = ()} eff, "",""])
  let usedArgs = calcArgTypesWithParams eff
  -- logMsg "usedArgs" 0 $ show usedArgs
  let g = genericUtil eff
  -- let b = doFunctor eff g
  let r = oneHoleImplementationType `(Traversable) g
  let b = implementationType `(Eq) g
  let r = mkTraversableImpl g
  logMsg "functorType" 0 $ show r

  
  -- logMsg "functorType" 0 $ show eff.name
  -- logMsg "functorTypePTypes" 0 $ show $ map (show . map paramTypes . explicitArgs) eff.cons
  -- logMsg "functorTypeTPE" 0 $ show $ map (show . map tpe . explicitArgs) eff.cons

  -- logTerm "functorType" 0 "" $ b
  
  pure ()
  
export
infoF2 : TypeInfo
infoF2 = getInfo "F2"

export
infoF3 : TypeInfo
infoF3 = getInfo "F3"

export
infoF4 : TypeInfo
infoF4 = getInfo "F4"

export
infoF5 : TypeInfo
infoF5 = getInfo "F5"

export
infoFoo' : TypeInfo
infoFoo' = getInfo "Foo'"

export
infoFooA : TypeInfo
infoFooA = getInfo "FooA"

export
infoFooAp : ParamTypeInfo
infoFooAp = getParamInfo "FooA"

export
infoFooA3 : TypeInfo
infoFooA3 = getInfo "FooA3"

export
infoFooA3p : ParamTypeInfo
infoFooA3p = getParamInfo "FooA3"

export
infoFooA4 : TypeInfo
infoFooA4 = getInfo "FooA4"

export
infoFooA4p : ParamTypeInfo
infoFooA4p = getParamInfo "FooA4"

export
infoFooAF : ParamTypeInfo
infoFooAF = getParamInfo "FooAF"

export
infoVoidFoo : ParamTypeInfo
infoVoidFoo = getParamInfo "VoidFoo"

-- %runElab getStuff `{F2}
-- %runElab getStuff `{F3}
-- %runElab getStuff `{F4}
-- %runElab getStuff `{F5}
%runElab getStuff `{FooAK}
%runElab getStuff `{FooAK2}
%runElab getStuff `{VoidFoo}
-- %runElab derive `{Foo2} [Functor]
-- %runElab derive `{FooAK} [Functor]

-- %runElab derive `{Foo} [Functor]
-- %runElab derive `{FooEnum} [Functor]

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

%runElab getStuff `{Tree1}


%runElab derive' `{FooA} [Functor]
%runElab derive' `{FooA'} [Foldable]
%runElab derive' `{FooA2} [Foldable]
%runElab derive' `{FooA3} [Foldable]
%runElab derive' `{FooAF} [Foldable]
%runElab derive' `{F2} [Foldable]
%runElab derive' `{Tree1} [Foldable,Traversable]
%runElab derive' `{Tree2} [Foldable]
%runElab derive' `{Tree3} [Foldable]

Traversable Tree1 where
  -- traverse f Leaf1 = [| Leaf1 |]
  traverse f Leaf1 = pure Leaf1
  -- traverse f (Branch1 x y z) = [| Branch1 (traverse f x) (f y) (traverse f z) |]
  traverse f (Branch1 x y z) = pure Branch1 <*> traverse f x <*> f y <*> traverse f z




Traversable Tree2 where
  traverse f x = ?dfsdf2

Traversable Tree3 where
  traverse f x = ?dfsdf3

-- %runElab derive `{FooA2} [Functor]
-- %runElab derive `{FooA3} [Functor]
-- %runElab derive `{FooA4} [Functor]
-- -- %runElab derive `{FooAF} [Functor] -- ?s
-- %runElab derive `{FooAK} [Functor,Foldable]
-- %runElab derive `{FooAK2} [Functor]
-- %runElab derive `{FooAKG2} [Functor]
-- %runElab derive `{FooAKR2} [Functor]
-- %runElab derive `{VoidFoo} [Functor,Foldable]
-- %runElab derive `{Foo2} [Functor]
-- %runElab derive `{Tree1} [Functor]
-- %runElab derive `{Tree2} [Functor]
-- %runElab derive `{Tree3} [Functor]
-- %runElab derive `{F1} [Functor]
-- %runElab derive `{F2} [Functor]
-- %runElab derive `{F3} [Functor]
-- %runElab derive `{F2'} [Functor] -- indices should actually be ok
-- %runElab derive `{F2''} [Functor] -- nested a -> b
-- %runElab derive `{F4} [Functor]
-- %runElab derive `{F5} [Functor]
-- %runElab derive `{Casetag} [Functor]
-- %runElab derive `{Foo} [Functor]
-- %runElab derive `{Foo} [Functor]
-- %runElab derive `{Foo} [Functor]
