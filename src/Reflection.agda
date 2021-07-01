{-# OPTIONS --type-in-type #-}

module Reflection where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Word

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Associativity, Precedence, Fixity
-------------------------------------------------------------------------------

data Associativity : Set where
  LeftAssoc : Associativity
  RightAssoc : Associativity
  NonAssoc : Associativity

{-# BUILTIN ASSOC Associativity #-}
{-# BUILTIN ASSOCLEFT LeftAssoc #-}
{-# BUILTIN ASSOCRIGHT RightAssoc #-}
{-# BUILTIN ASSOCNON NonAssoc #-}
{-# COMPILE GHC Associativity = data MAlonzo.RTE.Assoc (MAlonzo.RTE.LeftAssoc | MAlonzo.RTE.RightAssoc | MAlonzo.RTE.NonAssoc) #-}

data Precedence : Set where
  Related : Float -> Precedence
  Unrelated : Precedence

{-# BUILTIN PRECEDENCE Precedence #-}
{-# BUILTIN PRECRELATED Related #-}
{-# BUILTIN PRECUNRELATED Unrelated #-}
{-# COMPILE GHC Precedence = data MAlonzo.RTE.Precedence (MAlonzo.RTE.Related | MAlonzo.RTE.Unrelated) #-}

data Fixity : Set where
  Fixity: : Associativity -> Precedence -> Fixity

{-# BUILTIN FIXITY Fixity #-}
{-# BUILTIN FIXITYFIXITY Fixity: #-}
{-# COMPILE GHC Fixity = data MAlonzo.RTE.Fixity (MAlonzo.RTE.Fixity) #-}

-------------------------------------------------------------------------------
-- Name
-------------------------------------------------------------------------------

postulate Name : Set

{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name -> Name -> Bool
  primQNameLess : Name -> Name -> Bool
  primShowQName : Name -> String
  primQNameFixity : Name -> Fixity

-------------------------------------------------------------------------------
-- Meta
-------------------------------------------------------------------------------

postulate Meta : Set

{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta -> Meta -> Bool
  primMetaLess : Meta -> Meta -> Bool
  primShowMeta : Meta -> String
  primMetaToNat : Meta -> Nat

-------------------------------------------------------------------------------
-- Visibility, Relevance, ArgInfo, Arg
-------------------------------------------------------------------------------

-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : Set where
  Visible Hidden Instance : Visibility

{-# BUILTIN HIDING Visibility #-}
{-# BUILTIN VISIBLE Visible #-}
{-# BUILTIN HIDDEN Hidden #-}
{-# BUILTIN INSTANCE Instance #-}

-- Arguments can be relevant or irrelevant.
data Relevance : Set where
  Relevant Irrelevant : Relevance

{-# BUILTIN RELEVANCE Relevance #-}
{-# BUILTIN RELEVANT Relevant #-}
{-# BUILTIN IRRELEVANT Irrelevant #-}

-- Arguments also have a quantity.
data Quantity : Set where
  Quantity0 QuantityOmega : Quantity

{-# BUILTIN QUANTITY Quantity #-}
{-# BUILTIN QUANTITY-0 Quantity0 #-}
{-# BUILTIN QUANTITY-ω QuantityOmega #-}

-- Relevance and quantity are combined into a modality.
data Modality : Set where
  Modality: : (r : Relevance) (q : Quantity) -> Modality

{-# BUILTIN MODALITY Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR Modality: #-}

data ArgInfo : Set where
  ArgInfo: : (v : Visibility) (m : Modality) -> ArgInfo

data Arg (a : Set) : Set where
  Arg: : (i : ArgInfo) (x : a) -> Arg a

{-# BUILTIN ARGINFO ArgInfo #-}
{-# BUILTIN ARGARGINFO ArgInfo: #-}
{-# BUILTIN ARG Arg #-}
{-# BUILTIN ARGARG Arg: #-}

-------------------------------------------------------------------------------
-- Abstraction
-------------------------------------------------------------------------------

data Abstraction (a : Set) : Set where
  Abstraction: : (s : String) (x : a) -> Abstraction a

{-# BUILTIN ABS Abstraction #-}
{-# BUILTIN ABSABS Abstraction: #-}

-------------------------------------------------------------------------------
-- Literal
-------------------------------------------------------------------------------

data Literal : Set where
  NatLit : (n : Nat) -> Literal
  Word64Lit : (n : Word64) -> Literal
  FloatLit : (x : Float) -> Literal
  CharLit : (c : Char) -> Literal
  StringLit : (s : String) -> Literal
  NameLit : (x : Name) -> Literal
  MetaLit : (x : Meta) -> Literal

{-# BUILTIN AGDALITERAL Literal #-}
{-# BUILTIN AGDALITNAT NatLit #-}
{-# BUILTIN AGDALITWORD64 Word64Lit #-}
{-# BUILTIN AGDALITFLOAT FloatLit #-}
{-# BUILTIN AGDALITCHAR CharLit #-}
{-# BUILTIN AGDALITSTRING StringLit #-}
{-# BUILTIN AGDALITQNAME NameLit #-}
{-# BUILTIN AGDALITMETA MetaLit #-}

-------------------------------------------------------------------------------
-- Term, Sort, Pattern, Clause
-------------------------------------------------------------------------------

data Term : Set
data Sort : Set
data Pattern : Set
data Clause : Set
Type = Term

data Term where
  VarTerm : (x : Nat) (args : List (Arg Term)) -> Term
  ConTerm : (c : Name) (args : List (Arg Term)) -> Term
  DefTerm : (f : Name) (args : List (Arg Term)) -> Term
  LamTerm : (v : Visibility) (t : Abstraction Term) -> Term
  PatLamTerm : (cs : List Clause) (args : List (Arg Term)) -> Term
  PiTerm : (a : Arg Type) (b : Abstraction Type) -> Term
  SortTerm : (s : Sort) -> Term
  LitTerm : (l : Literal) -> Term
  MetaTerm : (x : Meta) -> List (Arg Term) -> Term
  UnknownTerm : Term

data Sort where
  SetSort : (t : Term) -> Sort
  LitSort : (n : Nat) -> Sort
  PropSort : (t : Term) -> Sort
  PropLitSort : (n : Nat) -> Sort
  InfSort : (n : Nat) -> Sort
  UnknownSort : Sort

data Pattern where
  ConPat : (c : Name) (ps : List (Arg Pattern)) -> Pattern
  DotPat : (t : Term) -> Pattern
  VarPat : (x : Nat) -> Pattern
  LitPat : (l : Literal) -> Pattern
  ProjPat : (f : Name) -> Pattern
  AbsurdPat : (x : Nat) -> Pattern -- absurd patterns counts as variables

data Clause where
  NormalClause : (tel : List (DPair String \ _ -> Arg Type))
    -> (ps : List (Arg Pattern))
    -> (t : Term)
    -> Clause
  AbsurdClause : (tel : List (DPair String \ _ -> Arg Type))
    -> (ps : List (Arg Pattern))
    -> Clause

{-# BUILTIN AGDATERM Term #-}
{-# BUILTIN AGDASORT Sort #-}
{-# BUILTIN AGDACLAUSE Clause #-}

{-# BUILTIN AGDATERMVAR VarTerm #-}
{-# BUILTIN AGDATERMCON ConTerm #-}
{-# BUILTIN AGDATERMDEF DefTerm #-}
{-# BUILTIN AGDATERMMETA MetaTerm #-}
{-# BUILTIN AGDATERMLAM LamTerm #-}
{-# BUILTIN AGDATERMEXTLAM PatLamTerm #-}
{-# BUILTIN AGDATERMPI PiTerm #-}
{-# BUILTIN AGDATERMSORT SortTerm #-}
{-# BUILTIN AGDATERMLIT LitTerm #-}
{-# BUILTIN AGDATERMUNSUPPORTED UnknownTerm #-}

{-# BUILTIN AGDASORTSET SetSort #-}
{-# BUILTIN AGDASORTLIT LitSort #-}
{-# BUILTIN AGDASORTPROP PropSort #-}
{-# BUILTIN AGDASORTPROPLIT PropLitSort #-}
{-# BUILTIN AGDASORTINF InfSort #-}
{-# BUILTIN AGDASORTUNSUPPORTED UnknownSort #-}

{-# BUILTIN AGDAPATTERN Pattern #-}
{-# BUILTIN AGDAPATCON ConPat #-}
{-# BUILTIN AGDAPATDOT DotPat #-}
{-# BUILTIN AGDAPATVAR VarPat #-}
{-# BUILTIN AGDAPATLIT LitPat #-}
{-# BUILTIN AGDAPATPROJ ProjPat #-}
{-# BUILTIN AGDAPATABSURD AbsurdPat #-}

{-# BUILTIN AGDACLAUSECLAUSE NormalClause #-}
{-# BUILTIN AGDACLAUSEABSURD AbsurdClause #-}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

data Definition : Set where
  Fun : (cs : List Clause) -> Definition
  DataType : (pars : Nat) (cs : List Name) -> Definition
  RecordType : (c : Name) (fs : List (Arg Name)) -> Definition
  DataCons : (d : Name) -> Definition
  Axiom : Definition
  PrimFun : Definition

{-# BUILTIN AGDADEFINITION Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF Fun #-}
{-# BUILTIN AGDADEFINITIONDATADEF DataType #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF RecordType #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR DataCons #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE Axiom #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE PrimFun #-}

-------------------------------------------------------------------------------
-- ErrorPart
-------------------------------------------------------------------------------

data ErrorPart : Set where
  StrErr : String -> ErrorPart
  TermErr : Term -> ErrorPart
  NameErr : Name -> ErrorPart

{-# BUILTIN AGDAERRORPART ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING StrErr #-}
{-# BUILTIN AGDAERRORPARTTERM TermErr #-}
{-# BUILTIN AGDAERRORPARTNAME NameErr #-}

-------------------------------------------------------------------------------
-- TC
-------------------------------------------------------------------------------

postulate
  TC : Set -> Set
  returnTC : a -> TC a
  bindTC : TC a -> (a -> TC b) -> TC b
  unify : Term -> Term -> TC Unit
  typeError : List ErrorPart -> TC a
  inferType : Term -> TC Type
  checkType : Term -> Type -> TC Term
  normalise : Term -> TC Term
  reduce : Term -> TC Term
  catchTC : TC a -> TC a -> TC a
  quoteTC : a -> TC Term
  unquoteTC : Term -> TC a
  getContext : TC (List (Arg Type))
  extendContext : Arg Type -> TC a -> TC a
  inContext : List (Arg Type) -> TC a -> TC a
  freshName : String -> TC Name
  declareDef : Arg Name -> Type -> TC Unit
  declarePostulate : Arg Name -> Type -> TC Unit
  defineFun : Name -> List Clause -> TC Unit
  getType : Name -> TC Type
  getDefinition : Name -> TC Definition
  blockOnMeta : Meta -> TC a
  commitTC : TC Unit
  isMacro : Name -> TC Bool

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : Bool -> TC a -> TC a

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String -> Nat -> List ErrorPart -> TC Unit

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : TC a -> TC a

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : TC (DPair a \ _ -> Bool) -> TC a

{-# BUILTIN AGDATCM TC #-}
{-# BUILTIN AGDATCMRETURN returnTC #-}
{-# BUILTIN AGDATCMBIND bindTC #-}
{-# BUILTIN AGDATCMUNIFY unify #-}
{-# BUILTIN AGDATCMTYPEERROR typeError #-}
{-# BUILTIN AGDATCMINFERTYPE inferType #-}
{-# BUILTIN AGDATCMCHECKTYPE checkType #-}
{-# BUILTIN AGDATCMNORMALISE normalise #-}
{-# BUILTIN AGDATCMREDUCE reduce #-}
{-# BUILTIN AGDATCMCATCHERROR catchTC #-}
{-# BUILTIN AGDATCMQUOTETERM quoteTC #-}
{-# BUILTIN AGDATCMUNQUOTETERM unquoteTC #-}
{-# BUILTIN AGDATCMGETCONTEXT getContext #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extendContext #-}
{-# BUILTIN AGDATCMINCONTEXT inContext #-}
{-# BUILTIN AGDATCMFRESHNAME freshName #-}
{-# BUILTIN AGDATCMDECLAREDEF declareDef #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE declarePostulate #-}
{-# BUILTIN AGDATCMDEFINEFUN defineFun #-}
{-# BUILTIN AGDATCMGETTYPE getType #-}
{-# BUILTIN AGDATCMGETDEFINITION getDefinition #-}
{-# BUILTIN AGDATCMBLOCKONMETA blockOnMeta #-}
{-# BUILTIN AGDATCMCOMMIT commitTC #-}
{-# BUILTIN AGDATCMISMACRO isMacro #-}
{-# BUILTIN AGDATCMWITHNORMALISATION withNormalisation #-}
{-# BUILTIN AGDATCMDEBUGPRINT debugPrint #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS noConstraints #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE runSpeculative #-}
