module Language.Reflection.Derive.Newtype

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

-- not newtype
data Foo = MkFoo

-- not newtype
data FooEnum = FooEnum1 | FooEnum2 | FooEnum3

-- newtype
data FooA a = MkFooA a

-- newtype
data FooInt = MkFooInt Int

-- not newtype
data FooA2 a = MkFooA2 | MkFooA2' a

-- not newtype
data FooAK a = MkFooAK

-- newtype
data F1 a b = MkF1 (a -> b)

-- newtype
data F1' : (Type -> Type) -> Type -> Type -> Type where
  MkF1' : (a -> f b) -> F1' f a b

-- newtype
data F1'' : (Type -> Type) -> Type -> Type -> Type -> Type where
  MkF1'' : (a -> b -> f c) -> F1'' f a b c

Num a => Num (FooA a) where
  (MkFooA x) + (MkFooA y) = MkFooA (x + y)
  (MkFooA x) * (MkFooA y) = MkFooA (x * y)
  fromInteger x = MkFooA $ fromInteger x

Num FooInt where
  (MkFooInt x) + (MkFooInt y) = MkFooInt (x + y)
  (MkFooInt x) * (MkFooInt y) = MkFooInt (x * y)
  fromInteger x = MkFooInt $ fromInteger x

Num b => Num (F1 a b) where
  (MkF1 f) + (MkF1 g) = MkF1 (\x => f x + g x)
  (MkF1 f) * (MkF1 g) = MkF1 (\x => f x * g x)
  fromInteger i = MkF1 (\_ => fromInteger i)

Num (f b) => Num (F1' f a b) where
  (MkF1' f) + (MkF1' g) = MkF1' (\x => f x + g x)
  (MkF1' f) * (MkF1' g) = MkF1' (\x => f x * g x)
  fromInteger i = MkF1' (\_ => fromInteger i)

Num (f c) => Num (F1'' f a b c) where
  (MkF1'' f) + (MkF1'' g) = MkF1'' (\x,y => f x y + g x y)
  (MkF1'' f) * (MkF1'' g) = MkF1'' (\x,y => f x y * g x y)
  fromInteger i = MkF1'' (\_,_ => fromInteger i)

init' : List a -> List a
init' (x :: xs@(_ :: _)) = x :: init xs
init' [x] = []
init' [] = []


-- Is it worthwhile to find out if the presence of the %noNewtype pragma can be discovered
||| Check if this type is a Newtype.
||| A newtype has one data constructor with one non-erased field.
isNewType : ParamTypeInfo -> Bool
isNewType pt = case pt.cons of
                 [con] => length (filter (\arg => arg.uses /= M0) con.explicitArgs) == 1
                 _ => False


||| Given a `TTImp` representing an interface, generates
||| the type of the implementation function with all type
||| parameters applied and auto implicits specified.
|||
||| Example: Given the `DeriveUtil` info of `Either`, this
||| will generate the following type for input ``(Eq)`:
|||
||| ```idris example
||| {0 a : _} -> {0 b : _} -> Eq a => Eq b => Eq (Either a b)
||| ```

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

-- examine this instructive case:
-- foo (MkFoo x)@a y@Int (MkFoo z)@a = MkFoo $ foo x y a
-- This also needs special consideration for function-typed fields
export
implementationTypeNT : (iface : TTImp) -> DeriveUtil -> TTImp
implementationTypeNT iface (MkDeriveUtil _ appTp names argTypesWithParams) =
    let appIface = iface .$ appTp
        implVars = argTypesWithParams -- vars which imply needed impls e.g. Num b required for F1
        autoArgs = piAllAuto appIface $ map (iface .$) implVars
     in piAllImplicit autoArgs names
  where
    break : TTImp -> (TTImp,TTImp)
    break (IApp _ y l) = (y,l)
    break tt = (tt,tt)


export
toBasicName : Name -> Name
toBasicName = UN . Basic . nameStr

export
toBasicName' : Name -> TTImp
toBasicName' = var . UN . Basic . nameStr

export
appLevels : Name -> TTImp -> Nat -> TTImp
appLevels n _  Z = var n
appLevels n fn (S k) = fn .$ (appLevels n fn k)

-- examine this instructive case:
-- foo (MkFoo x)@a y@Int (MkFoo z)@a = MkFoo $ foo x y a
-- This also needs special consideration for function-typed fields
-- each arg is a field of the record to define
export
genMapTT : (datatypeUtil : DeriveUtil) -> (implField : ExplicitArg) -> TTImp
genMapTT g field = `(_)
-- scan each field for our target type

--                      then `(believe_me)
--                      else lambdaArg "x" .=> iCase (var "x") implicitFalse
--                           (if length g.typeInfo.cons == 0
--                               then [impossibleClause `(_)]
--                               else clauses)
--   where
--     doRule : ExplicitArg -> TTImp
--     doRule (MkExplicitArg name tpe paramTypes isRecursive) = fromMaybe (toBasicName' name) $ ru tpe
--       where
--         ru : TTImp -> Maybe TTImp
--         -- Special function case
--         ru (IPi _ rig pinfo mnm argTy (IVar _ nm)) =
--           if nm /= t then Nothing else Just $ lambdaArg "q" .=> var fn .$ (toBasicName' name .$ var "q") -- TODO CHANGE
--         -- General case, cover bare IVars and Apps
--         ru tt = [| (appLevels fn `(map) <$> countLevels t tt) .$ Just (toBasicName' name) |]

--     lhss : List ParamCon -> List TTImp
--     lhss = map (\pc => appNames pc.name (map (toBasicName . name) pc.explicitArgs))

--     rhss : List ParamCon -> List TTImp
--     rhss = map (\pc => appAll pc.name (map doRule pc.explicitArgs))

--     clauses : List Clause
--     clauses = zipWith (.=) (lhss g.typeInfo.cons) (rhss g.typeInfo.cons)

-- map genMapTT over each field and collect
mkFunctorImpl : (conName : Name) -> (datatypeUtil : DeriveUtil) -> (fields : List ExplicitArg) -> TTImp
mkFunctorImpl conName g fields = appAll conName $ map (genMapTT g) fields

||| Derives an implementation of the given interface for the given newtype.
export
NewtypeAnyVis : Name -> Visibility -> (newtypeUtil : DeriveUtil) -> Elab InterfaceImpl
NewtypeAnyVis n vis g = do
  h <- genericUtil <$> getParamInfo' n
  (MkParamTypeInfo _ _ cs) <- pure $ h.typeInfo
  (con :: Nil) <- pure cs | _ => fail "not a single constructor"
  fields <- pure (con.explicitArgs)
  if isNewType g.typeInfo
    then pure $ MkInterfaceImpl "Functor" vis [] (mkFunctorImpl (name con) g fields) (implementationTypeNT (var n) g)
    else fail $ show g.typeInfo.name ++ " is not a newtype."

||| Alias for `EqVis Public`.
export
Newtype : Name -> DeriveUtil -> Elab InterfaceImpl
Newtype n = NewtypeAnyVis n Public

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
  -- logTerm "freafo" 0 "" $ impl b
  -- logTerm "freafo" 0 "" $ type b
  -- logTerm "freafo1" 0 "" $ type b
  -- logTerm "functorType" 0 "" $ r
  logMsg "functorType" 0 $ show usedArgs
  logMsg "functorType" 0 $ show $ implementationTypeNT `(Num) g

  
  -- logMsg "functorType" 0 $ show eff.name
  -- logMsg "functorTypePTypes" 0 $ show $ map (show . map paramTypes . explicitArgs) eff.cons
  -- logMsg "functorTypeTPE" 0 $ show $ map (show . map tpe . explicitArgs) eff.cons

  -- logTerm "functorType" 0 "" $ b
  
  pure ()
  
export
infoFoo' : TypeInfo
infoFoo' = getInfo "Foo'"

export
infoNum : ParamTypeInfo
infoNum = getParamInfo "Num"

export
infoFooA : TypeInfo
infoFooA = getInfo "FooA"

export
infoFooAp : ParamTypeInfo
infoFooAp = getParamInfo "FooA"

export
infoF1'' : ParamTypeInfo
infoF1'' = getParamInfo "F1''"

data N : Type -> Type -> Type where
  N1 : (0 _ : a) -> (a -> b) -> N a b

data T a = T1 Int a | T2 (T a)
data S a b = S1 (List b) | S2 (a, b, b)
data H : Type -> Type -> Type where
  H1 :  (List b) -> H a b
  H1' : (0 r : b) -> (List b) -> H a b
  H2 : (a, b, b) -> H a b

export
infoN : ParamTypeInfo
infoN = getParamInfo "N"

export
infoT : ParamTypeInfo
infoT = getParamInfo "T"

export
infoS : ParamTypeInfo
infoS = getParamInfo "S"

export
infoH : ParamTypeInfo
infoH = getParamInfo "H"

||| macro version of `getParamInfo`.
export %macro
getInfo' : Name -> Elab (List (Name, NameInfo))
getInfo' = getInfo

export
getInfo'' : List (Name, NameInfo)
getInfo'' = getInfo' `{Functor}

-- getInfo'' : List (Name, NameInfo)
-- getInfo'' = %runElab getInfo''

%runElab getStuff `{F1}
-- %runElab derive' `{FooA} [Newtype `{Num}]

main : IO ()
main = pure ()
