/-
Standalone Lean-core extension of the v46 primitive-preservation criterion.
No theorem here claims that arbitrary neutral interfaces satisfy that criterion.
-/
namespace KernelUniversalAudit

universe u v w z

/-- Local primitive congruence retains both definedness and reduced output. -/
def PrimitivePreserves {A : Type u} {B : Type v}
    {A' : Type w} {B' : Type z}
    (piA : A → A') (piB : B → B') (f : A → Option B) : Prop :=
  ∀ x y, piA x = piA y → (f x).map piB = (f y).map piB

/-- The local map equality implies equality of application domains. -/
theorem primitive_preserves_domain {A : Type u} {B : Type v}
    {A' : Type w} {B' : Type z}
    {piA : A → A'} {piB : B → B'} {f : A → Option B}
    (h : PrimitivePreserves piA piB f) {x y : A}
    (same : piA x = piA y) : f x = none ↔ f y = none := by
  have mapped := h x y same
  cases hx : f x <;> cases hy : f y <;> simp_all

/-- The local map equality preserves the reduced result when both exist. -/
theorem primitive_preserves_output {A : Type u} {B : Type v}
    {A' : Type w} {B' : Type z}
    {piA : A → A'} {piB : B → B'} {f : A → Option B}
    (h : PrimitivePreserves piA piB f) {x y : A} {a b : B}
    (same : piA x = piA y) (hx : f x = some a) (hy : f y = some b) :
    piB a = piB b := by
  have mapped := h x y same
  simpa [hx, hy] using mapped

/-- Domain preservation plus output preservation is exactly local congruence. -/
theorem primitive_preserves_iff {A : Type u} {B : Type v}
    {A' : Type w} {B' : Type z}
    (piA : A → A') (piB : B → B') (f : A → Option B) :
    PrimitivePreserves piA piB f ↔
      (∀ x y, piA x = piA y → (f x = none ↔ f y = none)) ∧
      (∀ x y a b, piA x = piA y → f x = some a → f y = some b →
        piB a = piB b) := by
  constructor
  · intro h
    exact ⟨fun _ _ same => primitive_preserves_domain h same,
      fun _ _ _ _ same hx hy => primitive_preserves_output h same hx hy⟩
  · rintro ⟨hd, ho⟩ x y same
    cases hx : f x with
    | none => rw [(hd x y same).1 hx]
    | some a =>
      cases hy : f y with
      | none => have bad := (hd x y same).2 hy; rw [hx] at bad; cases bad
      | some b => simp only [Option.map_some]; exact congrArg some (ho x y a b same hx hy)

/-- Exact existence and uniqueness of the reduced partial primitive.
Surjectivity concerns only the proposed reduced input sort. -/
theorem exact_primitive_descent {A : Type u} {B : Type v}
    {A' : Type w} {B' : Type z}
    (piA : A → A') (piB : B → B') (f : A → Option B)
    (onto : ∀ a', ∃ a, piA a = a') :
    PrimitivePreserves piA piB f ↔
      ∃ g : A' → Option B',
        (∀ x, g (piA x) = (f x).map piB) ∧
        (∀ h : A' → Option B', (∀ x, h (piA x) = (f x).map piB) → h = g) := by
  classical
  constructor
  · intro h
    let rep : A' → A := fun a' => Classical.choose (onto a')
    have rep_eq : ∀ a', piA (rep a') = a' := fun a' => Classical.choose_spec (onto a')
    let g : A' → Option B' := fun a' => (f (rep a')).map piB
    have commutes : ∀ x, g (piA x) = (f x).map piB := by
      intro x
      exact h (rep (piA x)) x (rep_eq (piA x))
    refine ⟨g, commutes, ?_⟩
    intro other hother
    funext a'
    obtain ⟨a, ha⟩ := onto a'
    rw [← ha, hother a, commutes a]
  · rintro ⟨g, commutes, _⟩ x y same
    rw [← commutes x, ← commutes y, same]

/-- Strict partial composition preserves a relation induced by reduction maps. -/
theorem bind_preserves {A : Type u} {B : Type v}
    {A' : Type w} {B' : Type z}
    (piA : A → A') (piB : B → B')
    {x y : Option A} {f g : A → Option B}
    (same : x.map piA = y.map piA)
    (step : ∀ a b, piA a = piA b → (f a).map piB = (g b).map piB) :
    (x.bind f).map piB = (y.bind g).map piB := by
  cases x with
  | none => cases y <;> simp_all
  | some a =>
    cases y with
    | none => cases same
    | some b => exact step a b (Option.some.inj same)

/-- Typed finite syntax. Arbitrary fixed finite arities can be represented by
explicit typed tuple constructors followed by a unary partial primitive.
The lazy test constructor does not evaluate its unselected branch. -/
inductive Term (Ty : Type u) (Var Const : Ty → Type v)
    (Unary : Ty → Ty → Type v)
    (Binary : Ty → Ty → Ty → Type v)
    (Test : Ty → Type v) : Ty → Type (max u v) where
  | var {s} : Var s → Term Ty Var Const Unary Binary Test s
  | const {s} : Const s → Term Ty Var Const Unary Binary Test s
  | unary {a b} : Unary a b → Term Ty Var Const Unary Binary Test a →
      Term Ty Var Const Unary Binary Test b
  | binary {a b c} : Binary a b c → Term Ty Var Const Unary Binary Test a →
      Term Ty Var Const Unary Binary Test b → Term Ty Var Const Unary Binary Test c
  | branch {a b} : Test a → Term Ty Var Const Unary Binary Test a →
      Term Ty Var Const Unary Binary Test b → Term Ty Var Const Unary Binary Test b →
      Term Ty Var Const Unary Binary Test b

section Terms
variable {Ty : Type u} {Var Const : Ty → Type v}
variable {Unary : Ty → Ty → Type v}
variable {Binary : Ty → Ty → Ty → Type v} {Test : Ty → Type v}
variable {Val : Ty → Type w} {Reduced : Ty → Type z}

/-- Interpretation stores data only; no preservation or soundness field. -/
structure Interpretation (Val : Ty → Type w)
    (Const : Ty → Type v) (Unary : Ty → Ty → Type v)
    (Binary : Ty → Ty → Ty → Type v) (Test : Ty → Type v) where
  constValue : {s : Ty} → Const s → Val s
  unary : {a b : Ty} → Unary a b → Val a → Option (Val b)
  binary : {a b c : Ty} → Binary a b c → Val a → Val b → Option (Val c)
  test : {a : Ty} → Test a → Val a → Option Bool

def eval (I : Interpretation Val Const Unary Binary Test)
    (rho : {s : Ty} → Var s → Val s) :
    {s : Ty} → Term Ty Var Const Unary Binary Test s → Option (Val s)
  | _, .var x => some (rho x)
  | _, .const c => some (I.constValue c)
  | _, .unary op x => (eval I rho x).bind (I.unary op)
  | _, .binary op x y =>
      (eval I rho x).bind (fun a => (eval I rho y).bind (I.binary op a))
  | _, .branch test x yes no =>
      (eval I rho x).bind (fun a =>
        (I.test test a).bind (fun answer => if answer then eval I rho yes else eval I rho no))

/-- The global finite-context result is proved by induction from local checks.
No all-context factorization or global-equivalence field is assumed. -/
theorem eval_preserves
    (I : Interpretation Val Const Unary Binary Test)
    (pi : (s : Ty) → Val s → Reduced s)
    (unary_ok : ∀ {a b} (op : Unary a b) x y,
      pi a x = pi a y → (I.unary op x).map (pi b) = (I.unary op y).map (pi b))
    (binary_ok : ∀ {a b c} (op : Binary a b c) x x' y y',
      pi a x = pi a x' → pi b y = pi b y' →
      (I.binary op x y).map (pi c) = (I.binary op x' y').map (pi c))
    (test_ok : ∀ {a} (op : Test a) x y,
      pi a x = pi a y → I.test op x = I.test op y)
    (rho tau : {s : Ty} → Var s → Val s)
    (same : ∀ {s} (x : Var s), pi s (rho x) = pi s (tau x))
    {s : Ty} (t : Term Ty Var Const Unary Binary Test s) :
    (eval I rho t).map (pi s) = (eval I tau t).map (pi s) := by
  induction t with
  | var x => exact congrArg some (same x)
  | const c => rfl
  | unary op x ih =>
      exact bind_preserves _ _ ih (fun a b hab => unary_ok op a b hab)
  | binary op x y ihx ihy =>
      apply bind_preserves _ _ ihx
      intro a a' haa'
      exact bind_preserves _ _ ihy (fun b b' hbb' => binary_ok op a a' b b' haa' hbb')
  | branch test x yes no ihx ihyes ihno =>
      apply bind_preserves _ _ ihx
      intro a a' haa'
      have ht := test_ok test a a' haa'
      change ((I.test test a).bind _).map _ = ((I.test test a').bind _).map _
      rw [ht]
      cases htest : I.test test a' with
      | none => rfl
      | some b => cases b <;> simp only [Option.bind_some, Bool.false_eq_true,
          ↓reduceIte] <;> assumption

/-- An observer's ordinary output is retained literally, so the preceding
result preserves its value and undefinedness, not merely a coarser label. -/
theorem ordinary_observer_preserved
    (I : Interpretation Val Const Unary Binary Test)
    (pi : (s : Ty) → Val s → Reduced s)
    (unary_ok : ∀ {a b} (op : Unary a b) x y,
      pi a x = pi a y → (I.unary op x).map (pi b) = (I.unary op y).map (pi b))
    (binary_ok : ∀ {a b c} (op : Binary a b c) x x' y y',
      pi a x = pi a x' → pi b y = pi b y' →
      (I.binary op x y).map (pi c) = (I.binary op x' y').map (pi c))
    (test_ok : ∀ {a} (op : Test a) x y,
      pi a x = pi a y → I.test op x = I.test op y)
    (rho tau : {s : Ty} → Var s → Val s)
    (same : ∀ {s} (x : Var s), pi s (rho x) = pi s (tau x))
    {s : Ty} (t : Term Ty Var Const Unary Binary Test s)
    (output_injective : ∀ x y : Val s, pi s x = pi s y → x = y) :
    eval I rho t = eval I tau t := by
  have h := eval_preserves I pi unary_ok binary_ok test_ok rho tau same t
  cases hx : eval I rho t <;> cases hy : eval I tau t <;> simp_all
  exact output_injective _ _ h

end Terms

/-- Exact all-observer criterion at one independently fixed substantive base.
Admission itself remains one of the observations through the explicit first
conjunct. The theorem does not assert its RHS without a primitive proof. -/
def StatusEquivalent {Status : Type u} {Observer : Type v}
    {Answer : Observer → Type w} (polarity : Status → Bool)
    (observe : (o : Observer) → Status → Option (Answer o))
    (x y : Status) : Prop :=
  polarity x = polarity y ∧ ∀ o, observe o x = observe o y

theorem exact_status_criterion {Status : Type u} {Observer : Type v}
    {Answer : Observer → Type w} (polarity : Status → Bool)
    (observe : (o : Observer) → Status → Option (Answer o)) :
    (∀ x y, StatusEquivalent polarity observe x y ↔ polarity x = polarity y) ↔
    (∀ o x y, polarity x = polarity y → observe o x = observe o y) := by
  constructor
  · intro h o x y same
    exact ((h x y).2 same).2 o
  · intro h x y
    exact ⟨And.left, fun same => ⟨same, fun o => h o x y same⟩⟩

/-- A constructive source language whose only raw-status read is admission.
All substantive base reads are retained in their original position. -/
inductive PureTest (Base : Type u) : Type u where
  | base : (Base → Option Bool) → PureTest Base
  | admission : PureTest Base
  | conjunction : PureTest Base → PureTest Base → PureTest Base
  | branch : PureTest Base → PureTest Base → PureTest Base → PureTest Base

def PureTest.eval {Base : Type u} {Status : Type v}
    (polarity : Status → Bool) (base : Base) (status : Status) :
    PureTest Base → Option Bool
  | .base read => read base
  | .admission => some (polarity status)
  | .conjunction left right =>
      (left.eval polarity base status).bind (fun x =>
        (right.eval polarity base status).map (fun y => x && y))
  | .branch test yes no =>
      (test.eval polarity base status).bind (fun answer =>
        if answer then yes.eval polarity base status else no.eval polarity base status)

/-- Binary preservation is proved from the source grammar, with no preservation
law stored in a package and no all-context factorization premise. -/
theorem pure_test_preserves {Base : Type u} {Status : Type v}
    (polarity : Status → Bool) (base : Base) (x y : Status)
    (same : polarity x = polarity y) (test : PureTest Base) :
    test.eval polarity base x = test.eval polarity base y := by
  induction test with
  | base read => rfl
  | admission => exact congrArg some same
  | conjunction left right ihl ihr => simp only [PureTest.eval, ihl, ihr]
  | branch test yes no iht ihy ihn => simp only [PureTest.eval, iht, ihy, ihn]

/-- Full substitution equivalence for every observation in the original,
explicitly generated source language is exactly admission equality. -/
theorem generated_boolean_interface_binary {Base : Type u} {Status : Type v}
    (polarity : Status → Bool) (base : Base) (x y : Status) :
    (∀ test : PureTest Base, test.eval polarity base x = test.eval polarity base y) ↔
      polarity x = polarity y := by
  constructor
  · intro observations
    exact Option.some.inj (observations .admission)
  · intro same test
    exact pure_test_preserves polarity base x y same test
/-- Exact limitation on unrestricted ordinary consumers. This theorem says
nothing about which consumers are lawful in a particular governed interface. -/
theorem all_total_consumers_iff_injective {A : Type u} {B : Type v}
    (pi : A → B) :
    (∀ f : A → A, ∀ x y, pi x = pi y → f x = f y) ↔
      (∀ x y, pi x = pi y → x = y) := by
  constructor
  · intro all x y same
    exact all (fun a => a) x y same
  · intro injective f x y same
    exact congrArg f (injective x y same)

/-- Any nontrivial proposed identification is separated by the identity
observer if that observer is admitted to an unrestricted ordinary output sort.
Its availability in an actual interface is a separate question. -/
theorem identity_observer_separates {A : Type u} {B : Type v}
    (pi : A → B) (x y : A) (same : pi x = pi y) (distinct : x ≠ y) :
    ∃ f : A → A, pi x = pi y ∧ f x ≠ f y :=
  ⟨fun a => a, same, distinct⟩

/-- Injective reductions preserve every total consumer into every codomain. -/
theorem injective_preserves_every_total_consumer
    {A : Type u} {B : Type v} {C : Type w}
    (pi : A → B) (injective : ∀ x y, pi x = pi y → x = y)
    (f : A → C) (x y : A) (same : pi x = pi y) : f x = f y :=
  congrArg f (injective x y same)
#print axioms exact_primitive_descent
#print axioms eval_preserves
#print axioms ordinary_observer_preserved
#print axioms exact_status_criterion
#print axioms generated_boolean_interface_binary
#print axioms all_total_consumers_iff_injective
#print axioms identity_observer_separates

end KernelUniversalAudit