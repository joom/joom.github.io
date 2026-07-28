/-
Checked with Lean 4.32.1.

Rejected declarations are wrapped in `#guard_msgs`; they are part of the
test rather than commented examples.
-/

universe u v w

inductive Forall₂ {α : Type u} {β : Type v} (R : α → β → Prop) :
    List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons : R a b → Forall₂ R as bs →
      Forall₂ R (a :: as) (b :: bs)

theorem Forall₂.length
    {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Forall₂ R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Forall₂.comp
    {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (step : ∀ {a b c}, R a b → S b c → T a c)
    (hab : Forall₂ R as bs) (hbc : Forall₂ S bs cs) :
    Forall₂ T as cs := by
  induction hab generalizing cs with
  | nil =>
      cases hbc
      exact .nil
  | cons hr hrs ih =>
      cases hbc with
      | cons hs hss => exact .cons (step hr hs) (ih hss)

inductive Term where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → List Term → Term

inductive Ty where
  | base : String → Ty
  | arrow : List Ty → Ty → Ty

abbrev Ctx := List (String × Ty)

/- Direct nesting through `Forall₂` is accepted. -/

inductive ParRed : Term → Term → Prop where
  | var : ParRed (.var x) (.var x)
  | lam : ParRed body body' → ParRed (.lam x body) (.lam x body')
  | app : ParRed fn fn' → Forall₂ ParRed args args' →
      ParRed (.app fn args) (.app fn' args')

inductive Subty : Ty → Ty → Prop where
  | refl : Subty t t
  | arrow : Forall₂ Subty argsB argsA → Subty retA retB →
      Subty (.arrow argsA retA) (.arrow argsB retB)

/- `Forall₂ (EvalCaptured env)` is rejected because `env` is constructor-local. -/

inductive Val where
  | num : Int → Val
  | closure : String → Term → List (String × Val) → Val

abbrev Env := List (String × Val)

/--
error: (kernel) invalid nested inductive datatype 'Forall₂', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive EvalCaptured : Env → Term → Val → Prop where
  | app : EvalCaptured env fn (.closure param body cenv) →
      Forall₂ (EvalCaptured env) args vals →
      EvalCaptured cenv body result →
      EvalCaptured env (.app fn args) result

mutual
  inductive Eval : Env → Term → Val → Prop where
    | var : (x, value) ∈ env → Eval env (.var x) value
    | lam : Eval env (.lam x body) (.closure x body env)
    | app : Eval env fn (.closure param body cenv) →
        EvalArgs env args vals →
        Eval cenv body result →
        Eval env (.app fn args) result

  inductive EvalArgs : Env → List Term → List Val → Prop where
    | nil : EvalArgs env [] []
    | cons : Eval env term value → EvalArgs env terms values →
        EvalArgs env (term :: terms) (value :: values)
end

inductive JSON where
  | null : JSON
  | str : String → JSON
  | num : Int → JSON
  | arr : List JSON → JSON
  | obj : List (String × JSON) → JSON

inductive Schema where
  | any : Schema
  | strS : Schema
  | numS : Schema
  | arrS : Schema → Schema
  | objS : List (String × Schema) → Schema

/- Direct recursion through `And` and `Exists` is accepted. -/

inductive AndAccepted : Nat → Nat → Prop where
  | step (s j) : (AndAccepted s j ∧ True) → AndAccepted s j

inductive ExistsAccepted : Nat → Nat → Prop where
  | step (s) : (∃ j : Nat, ExistsAccepted s j) → ExistsAccepted s 0

/- `And` nested inside `Forall₂` is rejected. -/

/--
error: (kernel) invalid nested inductive datatype 'And', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive ValidCombined : Schema → JSON → Prop where
  | any : ValidCombined .any json
  | str : ValidCombined .strS (.str value)
  | num : ValidCombined .numS (.num value)
  | arr : (∀ json, json ∈ values → ValidCombined elemSchema json) →
      ValidCombined (.arrS elemSchema) (.arr values)
  | obj :
      Forall₂
        (fun (sf : String × Schema) (jf : String × JSON) =>
          sf.1 = jf.1 ∧ ValidCombined sf.2 jf.2)
        schemaFields jsonFields →
      ValidCombined (.objS schemaFields) (.obj jsonFields)

/- Splitting the relation into two `Forall₂` derivations is accepted. -/

inductive Valid : Schema → JSON → Prop where
  | any : Valid .any json
  | str : Valid .strS (.str value)
  | num : Valid .numS (.num value)
  | arr : (∀ json, json ∈ values → Valid elemSchema json) →
      Valid (.arrS elemSchema) (.arr values)
  | obj :
      Forall₂
        (fun (sf : String × Schema) (jf : String × JSON) =>
          sf.1 = jf.1)
        schemaFields jsonFields →
      Forall₂
        (fun (sf : String × Schema) (jf : String × JSON) =>
          Valid sf.2 jf.2)
        schemaFields jsonFields →
      Valid (.objS schemaFields) (.obj jsonFields)

theorem Valid.dropHead
    (h : Valid (.objS ((sk, ss) :: schemaFields))
      (.obj ((jk, jv) :: jsonFields))) :
    Valid (.objS schemaFields) (.obj jsonFields) := by
  cases h with
  | obj hnames hvalues =>
      cases hnames
      cases hvalues
      exact .obj
        ‹Forall₂ _ schemaFields jsonFields›
        ‹Forall₂ _ schemaFields jsonFields›

theorem Valid.head
    (h : Valid (.objS ((sk, ss) :: schemaFields))
      (.obj ((jk, jv) :: jsonFields))) :
    sk = jk ∧ Valid ss jv := by
  cases h with
  | obj hnames hvalues =>
      cases hnames
      cases hvalues
      exact ⟨‹sk = jk›, ‹Valid ss jv›⟩

/- A specialized mutual relation retains one paired field derivation. -/

mutual
  inductive ValidPaired : Schema → JSON → Prop where
    | any : ValidPaired .any json
    | str : ValidPaired .strS (.str value)
    | num : ValidPaired .numS (.num value)
    | arr : (∀ json, json ∈ values → ValidPaired elemSchema json) →
        ValidPaired (.arrS elemSchema) (.arr values)
    | obj : ValidFields schemaFields jsonFields →
        ValidPaired (.objS schemaFields) (.obj jsonFields)

  inductive ValidFields :
      List (String × Schema) → List (String × JSON) → Prop where
    | nil : ValidFields [] []
    | cons : sk = jk → ValidPaired ss jv →
        ValidFields schemaFields jsonFields →
        ValidFields
          ((sk, ss) :: schemaFields)
          ((jk, jv) :: jsonFields)
end

theorem ValidPaired.dropHead
    (h : ValidPaired (.objS ((sk, ss) :: schemaFields))
      (.obj ((jk, jv) :: jsonFields))) :
    ValidPaired (.objS schemaFields) (.obj jsonFields) := by
  cases h with
  | obj hfields =>
      cases hfields with
      | cons _ _ tail => exact .obj tail

/- The `induction` tactic rejects nested and mutual types. -/

/--
error: The `induction` tactic does not support the type `Term` because it is a nested inductive type

Hint: Consider using the `cases` tactic instead
-/
#guard_msgs in
example (term : Term) : True := by
  induction term <;> trivial

mutual
  inductive Synth : Ctx → Term → Ty → Prop where
    | var : (x, ty) ∈ ctx → Synth ctx (.var x) ty
    | app : Synth ctx fn (.arrow argTys retTy) →
        CheckList ctx args argTys →
        Synth ctx (.app fn args) retTy

  inductive Check : Ctx → Term → Ty → Prop where
    | lam : Check ((x, argTy) :: ctx) body retTy →
        Check ctx (.lam x body) (.arrow [argTy] retTy)
    | sub : Synth ctx term ty → Check ctx term ty

  inductive CheckList : Ctx → List Term → List Ty → Prop where
    | nil : CheckList ctx [] []
    | cons : Check ctx term ty → CheckList ctx terms tys →
        CheckList ctx (term :: terms) (ty :: tys)
end

/--
error: The `induction` tactic does not support the type `Synth` because it is mutually inductive

Hint: Consider using the `cases` tactic instead
-/
#guard_msgs in
example (h : Synth ctx term ty) : True := by
  induction h <;> trivial
