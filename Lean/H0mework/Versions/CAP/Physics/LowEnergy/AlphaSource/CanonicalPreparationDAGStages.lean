import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationDAGEngineSyntax
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDAGSemantic
open PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth
open PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol PreparationVacuumEnginePaidDepth
open scoped BigOperators Topology

-- The recursion has only the C/0 seed and the original residual/JI update.
-- Its previous argument consists of generated syntax, not a realization certificate.
def sourceEngineTerm (k : ℕ) : ClockTerm (sourceEngine k) :=
  Nat.rec (motive:=fun k => ClockTerm (sourceEngine k))
    (by
      intro a j
      have first : j=(0 : Fin 1) := by
        apply Fin.ext
        change j.val=0
        have bound := j.isLt
        change j.val<1 at bound
        omega
      rw [first,sourceEngine_initial]
      split_ifs
      · exact Term.primitive .clock
      · exact zeroS)
    (fun k previous => by
      intro a j
      by_cases old : j.val<k+1
      · have same : j=Fin.castSucc ⟨j.val,old⟩ := Fin.ext rfl
        rw [same,sourceEngine_preserves]
        exact previous _ _
      · have same : j=Fin.last (k+1) := by apply Fin.ext; have := j.isLt; simp only [Fin.val_last]; omega
        rw [same]
        let residual : Fin 4 → Symbol := fun b => forceOrEnergy (k+1) (sourceEngine k) (some b) (Fin.last (k+1))
        have generated : sourceEngine (k+1) a (Fin.last (k+1))=
            -(∑ b : Fin 4,(fun x => (principalForceJacobian x)⁻¹ a b)*residual b) := by
          funext x
          exact sourceEngine_generated k a x
        rw [generated]
        exact Term.negS (Term.sumS (fun b : Fin 4 => Term.mulS (Term.primitive (.inverseJacobian a b))
          (forceOrEnergyTerm (k+1) previous (some b) (Fin.last (k+1)))))) k

def energyTerm (k : ℕ) : SymbolTerm (sourceEngineEnergy k) := by
  cases k with
  | zero => exact forceOrEnergyTerm 0 (sourceEngineTerm 0) none (Fin.last 0)
  | succ k =>
    rw [sourceEngineEnergy_newestExcluded k]
    exact forceOrEnergyTerm (k+1) (sourceEngineTerm k) none (Fin.last (k+1))

def energy_expr (k : ℕ) : Expression .symbol := erase (energyTerm k)

def clock_definition_exprs (k : ℕ) (a : Fin 4) : Expression .symbol :=
  erase (sourceEngineTerm (k+1) a (Fin.last (k+1)))

def residual_exprs (k : ℕ) (a : Fin 4) : Expression .symbol :=
  erase (forceOrEnergyTerm (k+1) (sourceEngineTerm k) (some a) (Fin.last (k+1)))

theorem energy_expr_readback (k : ℕ) : evaluate (energy_expr k)=sourceEngineEnergy k :=
  evaluate_erase _

theorem clock_definition_exprs_readback (k : ℕ) (a : Fin 4) :
    evaluate (clock_definition_exprs k a)=sourceEngine (k+1) a (Fin.last (k+1)) := evaluate_erase _

theorem residual_exprs_readback (k : ℕ) (a : Fin 4) :
    evaluate (residual_exprs k a)=forceOrEnergy (k+1) (sourceEngine k) (some a) (Fin.last (k+1)) := evaluate_erase _

theorem clock_definition_original_JI (k : ℕ) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    evaluate (clock_definition_exprs k a) x=
      ∑ b : Fin 4,coefficientValue (correctionCoefficient a b) x*evaluate (residual_exprs k b) x := by
  rw [clock_definition_exprs_readback,sourceEngine_generated_normalized k a x hx]
  simp only [residual_exprs_readback]

-- Complex-linear extension keeps each unsymmetrized raw Moyal atom, including odd
-- imaginary terms; real projection is used only after the original Jordan sum.
def complexMoyal (r : ℕ) (f g : Phase → ℂ) : Phase → ℂ := fun x =>
  coefficient r (fun y => (f y).re) (fun y => (g y).re) x-
  coefficient r (fun y => (f y).im) (fun y => (g y).im) x+
  Complex.I*(coefficient r (fun y => (f y).re) (fun y => (g y).im) x+
    coefficient r (fun y => (f y).im) (fun y => (g y).re) x)

theorem complexMoyal_real (r : ℕ) (f g : Symbol) (x : Phase) :
    complexMoyal r (fun y => (f y : ℂ)) (fun y => (g y : ℂ)) x=coefficient r f g x := by
  simp [complexMoyal,coefficient_zero_left,coefficient_zero_right]

-- This carrier matches Arena's source/clock/moyal atoms and coefficient/ordered-word
-- polynomial rows. A clock key is bounded by the earlier stage; its value is generated
-- by sourceEngineTerm, so no caller supplies a clock definition or a finished energy.
inductive ArenaExpression (earlier : ℕ) where
  | literal (c : ℝ)
  | source (degree : Fin 3) (slot : Fin 14)
  | clock (level : Fin (earlier+1)) (axis : Fin 4)
  | moyal (r : ℕ) (left right : ArenaExpression earlier)
  | row (coefficient : NormalizedCoefficient) (word : List (ArenaExpression earlier))
  | add (left right : ArenaExpression earlier)

def arenaEvaluate {earlier : ℕ} (e : ArenaExpression earlier) : Phase → ℂ :=
  ArenaExpression.rec (motive_1:=fun _ => Phase → ℂ) (motive_2:=fun _ => Phase → ℂ)
    (fun c _ => (c : ℂ))
    (fun d j x => (originalLeaf d j x : ℂ))
    (fun level a x => (evaluate (erase (sourceEngineTerm earlier a level)) x : ℂ))
    (fun r _ _ left right => complexMoyal r left right)
    (fun c _ word x => (coefficientValue c x : ℂ)*word x)
    (fun _ _ left right x => left x+right x)
    (fun _ => 1)
    (fun _ _ head tail x => head x*tail x) e

@[simp] theorem arenaEvaluate_row {earlier : ℕ} (c : NormalizedCoefficient)
    (word : List (ArenaExpression earlier)) (x : Phase) :
    arenaEvaluate (.row c word) x=(coefficientValue c x : ℂ)*
      word.foldr (fun atom out => arenaEvaluate atom x*out) 1 := by
  suffices fold : ArenaExpression.rec_1
      (motive_1:=fun _ => Phase → ℂ) (motive_2:=fun _ => Phase → ℂ)
      (fun c _ => (c : ℂ))
      (fun d j x => (originalLeaf d j x : ℂ))
      (fun level a x => (evaluate (erase (sourceEngineTerm earlier a level)) x : ℂ))
      (fun r _ _ left right => complexMoyal r left right)
      (fun c _ word x => (coefficientValue c x : ℂ)*word x)
      (fun _ _ left right x => left x+right x)
      (fun _ => 1)
      (fun _ _ head tail x => head x*tail x) word x=
        word.foldr (fun atom out => arenaEvaluate atom x*out) 1 by
    exact congrArg ((coefficientValue c x : ℂ)*·) fold
  induction word with
  | nil => rfl
  | cons a word ih => change arenaEvaluate a x*_ = _; rw [ih]; rfl


@[simp] theorem arenaEvaluate_literal {k : ℕ} (c : ℝ) : arenaEvaluate (.literal c : ArenaExpression k)=(fun _ => (c : ℂ)) := rfl
@[simp] theorem arenaEvaluate_source {k : ℕ} (d : Fin 3) (j : Fin 14) : arenaEvaluate (.source d j : ArenaExpression k)=(fun x => (originalLeaf d j x : ℂ)) := rfl
@[simp] theorem arenaEvaluate_clock {k : ℕ} (l : Fin (k+1)) (a : Fin 4) : arenaEvaluate (.clock l a : ArenaExpression k)=(fun x => (evaluate (erase (sourceEngineTerm k a l)) x : ℂ)) := rfl
@[simp] theorem arenaEvaluate_moyal {k : ℕ} (r : ℕ) (e f : ArenaExpression k) : arenaEvaluate (.moyal r e f)=complexMoyal r (arenaEvaluate e) (arenaEvaluate f) := rfl
@[simp] theorem arenaEvaluate_add {k : ℕ} (e f : ArenaExpression k) : arenaEvaluate (.add e f)=(fun x => arenaEvaluate e x+arenaEvaluate f x) := rfl

theorem arena_clock_readback (earlier : ℕ) (level : Fin (earlier+1)) (a : Fin 4) (x : Phase) :
    arenaEvaluate (.clock level a : ArenaExpression earlier) x=(sourceEngine earlier a level x : ℂ) := by
  simp only [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_erase]

theorem arena_clock_definition_key (earlier order : ℕ) (paid : order+1≤earlier)
    (a : Fin 4) (x : Phase) :
    arenaEvaluate (.clock ⟨order+1,by omega⟩ a : ArenaExpression earlier) x=
      (evaluate (clock_definition_exprs order a) x : ℂ) := by
  rw [arena_clock_readback,clock_definition_exprs_readback]
  have same := sourceEngine_preserves_paid (order+1) earlier paid a (order+1) (Nat.le_refl _)
  change (if h : order+1<earlier+1 then sourceEngine earlier a ⟨order+1,h⟩ else 0)=
    (if h : order+1<order+1+1 then sourceEngine (order+1) a ⟨order+1,h⟩ else 0) at same
  simp only [show order+1<earlier+1 by omega,show order+1<order+1+1 by omega,dif_pos] at same
  exact congrArg (fun f : Symbol => (f x : ℂ)) same

theorem arena_source_moyal (earlier r : ℕ) (d e : Fin 3) (j k : Fin 14) (x : Phase) :
    arenaEvaluate (.moyal r (.source d j) (.source e k) : ArenaExpression earlier) x=
      originalN0Coefficient r d e j k x := by
  simp only [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,originalN0Coefficient]
  exact complexMoyal_real r _ _ x

theorem arena_source_moyal_grouped (earlier r : ℕ) (d e : Fin 3) (j k : Fin 14) (x : Phase)
    (physical : x∈PreparationVacuumMoyalSymmetry.originalPhysicalPhase) :
    arenaEvaluate (.moyal r (.source d j) (.source e k) : ArenaExpression earlier) x=
      originalGroupedN0Coefficient r d e j k x := by
  rw [arena_source_moyal,PreparationVacuumMoyalSymmetry.originalN0Coefficient_grouped r d e j k x physical]

theorem arena_row_ordered (earlier : ℕ) (c : NormalizedCoefficient)
    (word : List (ArenaExpression earlier)) (x : Phase) :
    arenaEvaluate (.row c word) x=(coefficientValue c x : ℂ)*
      word.foldr (fun atom out => arenaEvaluate atom x*out) 1 := by rw [arenaEvaluate_row]

theorem arena_row_empty (earlier : ℕ) (c : NormalizedCoefficient) (x : Phase) :
    arenaEvaluate (.row c [] : ArenaExpression earlier) x=(coefficientValue c x : ℂ) := by
  simp [arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]

theorem arena_row_principal (earlier : ℕ) (slot : Fin 13) (x : Phase) :
    arenaEvaluate (.row (principalCoefficient slot) [] : ArenaExpression earlier) x=(engineSource 0 slot x : ℂ) := by
  rw [arena_row_empty,principalCoefficient_native]

theorem arena_row_inverse (earlier : ℕ) (a b : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.row (inverseCoefficient a b) [] : ArenaExpression earlier) x=((principalForceJacobian x)⁻¹ a b : ℂ) := by
  rw [arena_row_empty,inverseCoefficient_native a b x hx]


private theorem coefficient_eqOn (r : ℕ) {f f' g g' : Symbol}
    (hf : Set.EqOn f f' poleDomain) (hg : Set.EqOn g g' poleDomain)
    (x : Phase) (hx : x∈poleDomain) : coefficient r f g x=coefficient r f' g' x := by
  have fj : ∀ w : Word r,jet r f w x=jet r f' w x := by
    intro w
    have germ : f =ᶠ[𝓝 x] f' := by
      filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact hf hy
    exact congrArg (fun D => D (fun a => slotDirection (w a)))
      ((germ.iteratedFDeriv ℝ r).self_of_nhds)
  have gj : ∀ w : Word r,jet r g w x=jet r g' w x := by
    intro w
    have germ : g =ᶠ[𝓝 x] g' := by
      filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact hg hy
    exact congrArg (fun D => D (fun a => slotDirection (w a)))
      ((germ.iteratedFDeriv ℝ r).self_of_nhds)
  simp only [coefficient,contraction,fj,gj]

private theorem complexMoyal_eqOn (r : ℕ) {f f' g g' : Phase → ℂ}
    (hf : Set.EqOn f f' poleDomain) (hg : Set.EqOn g g' poleDomain)
    (x : Phase) (hx : x∈poleDomain) : complexMoyal r f g x=complexMoyal r f' g' x := by
  have fre : Set.EqOn (fun y => (f y).re) (fun y => (f' y).re) poleDomain := fun y hy => congrArg Complex.re (hf hy)
  have fim : Set.EqOn (fun y => (f y).im) (fun y => (f' y).im) poleDomain := fun y hy => congrArg Complex.im (hf hy)
  have gre : Set.EqOn (fun y => (g y).re) (fun y => (g' y).re) poleDomain := fun y hy => congrArg Complex.re (hg hy)
  have gim : Set.EqOn (fun y => (g y).im) (fun y => (g' y).im) poleDomain := fun y hy => congrArg Complex.im (hg hy)
  simp only [complexMoyal,coefficient_eqOn r fre gre x hx,coefficient_eqOn r fim gim x hx,
    coefficient_eqOn r fre gim x hx,coefficient_eqOn r fim gre x hx]

def arenaProduct {k : ℕ} (e f : ArenaExpression k) : ArenaExpression k :=
  .row (polynomialCoefficient 1) [e,f]

def arenaNegate {k : ℕ} (e : ArenaExpression k) : ArenaExpression k := arenaProduct (.literal (-1)) e

def arenaSum {k : ℕ} {ι : Type} (indices : Finset ι) (e : ι → ArenaExpression k) : ArenaExpression k :=
  indices.toList.foldr (fun i out => .add (e i) out) (.literal 0)

def arenaJordan {k : ℕ} (r : ℕ) (e f : ArenaExpression k) : ArenaExpression k :=
  arenaProduct (.literal (1/2)) (.add (.moyal r e f) (.moyal r f e))

theorem arenaProduct_evaluate {k : ℕ} (e f : ArenaExpression k) (x : Phase) :
    arenaEvaluate (arenaProduct e f) x=arenaEvaluate e x*arenaEvaluate f x := by
  simp [arenaProduct,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,polynomialCoefficient_source,polynomialSymbol]

theorem arenaNegate_evaluate {k : ℕ} (e : ArenaExpression k) (x : Phase) :
    arenaEvaluate (arenaNegate e) x= -arenaEvaluate e x := by
  rw [arenaNegate,arenaProduct_evaluate]
  simp [arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]

theorem arenaSum_evaluate {k : ℕ} {ι : Type} (indices : Finset ι) (e : ι → ArenaExpression k) (x : Phase) :
    arenaEvaluate (arenaSum indices e) x=∑ i∈indices,arenaEvaluate (e i) x := by
  have fold (l : List ι) :
      arenaEvaluate (l.foldr (fun i out => .add (e i) out) (.literal 0)) x=
        (l.map (fun i => arenaEvaluate (e i) x)).sum := by
    induction l with
    | nil => simp [arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]
    | cons i l ih => simp [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,ih]
  rw [arenaSum,fold]
  exact Finset.sum_map_toList _ _

theorem arenaJordan_evaluate {k : ℕ} (r : ℕ) (e f : ArenaExpression k) (a b : Symbol)
    (he : Set.EqOn (arenaEvaluate e) (fun x => (a x : ℂ)) poleDomain)
    (hf : Set.EqOn (arenaEvaluate f) (fun x => (b x : ℂ)) poleDomain)
    (x : Phase) (hx : x∈poleDomain) : arenaEvaluate (arenaJordan r e f) x=(scalarJordan r a b x : ℂ) := by
  rw [arenaJordan,arenaProduct_evaluate]
  simp only [arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]
  rw [complexMoyal_eqOn r he hf x hx,complexMoyal_eqOn r hf he x hx,
    complexMoyal_real,complexMoyal_real,scalarJordan_native]
  simp only [jordan,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

def compilePrimitive (p : Primitive) : ArenaExpression 0 :=
  match p with
  | .literal c => .literal c
  | .principal j => .row (principalCoefficient j) []
  | .leaf d j => .source d j
  | .clock => .row (polynomialCoefficient (MvPolynomial.X 0)) []
  | .inverseClock => .row (inversePoleCoefficient 0) []
  | .inverseJacobian a b => .row (inverseCoefficient a b) []

theorem compilePrimitive_evaluate (p : Primitive) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (compilePrimitive p) x=(primitiveValue p x : ℂ) := by
  cases p with
  | literal c => simp only [compilePrimitive,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,primitiveValue]
  | principal j => exact arena_row_principal 0 j x
  | leaf d j => simp only [compilePrimitive,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,primitiveValue]
  | clock =>
    rw [compilePrimitive,arena_row_empty,polynomialCoefficient_source]
    simp [polynomialSymbol,evalAt,sourceVariables,primitiveValue,PreparationVacuumClockJacobian.actualC,sourceClock]
  | inverseClock => rw [compilePrimitive,arena_row_empty,inverseClockCoefficient_native]; rfl
  | inverseJacobian a b => exact arena_row_inverse 0 a b x hx

def Compiled : ExprSort → Type
  | .symbol => ArenaExpression 0
  | .polynomial => AngularExponent → ArenaExpression 0

-- The supports below are exactly those of the same source-generated polynomial
-- occurrence. Phase-dependent central factors remain inside every Moyal operand.
-- No new radius, majorant, sampled symbol, or leaf realization enters.
def compile {s : ExprSort} (e : Expression s) : Compiled s :=
  Expression.rec (motive:=fun s _ => Compiled s)
    compilePrimitive
    (fun _ _ e f => .add e f)
    (fun _ e => arenaNegate e)
    (fun _ _ e f => arenaProduct e f)
    (fun _ terms => arenaSum Finset.univ terms)
    (fun u _ e => e u)
    (fun e compiled => arenaSum (evaluate e).support
      (fun u => arenaProduct (.literal (angularMoment u)) (compiled u)))
    (fun _ => .literal 0)
    (fun u _ e v => if u=v then e else .literal 0)
    (fun _ _ e f u => .add (e u) (f u))
    (fun _ e u => arenaNegate (e u))
    (fun e f ce cf u => arenaSum (evaluate e).support (fun a =>
      arenaSum (evaluate f).support (fun b => if a+b=u then arenaProduct (ce a) (cf b) else .literal 0)))
    (fun _ terms u => arenaSum Finset.univ (fun i => terms i u))
    (fun r e f ce cf u => arenaSum (evaluate e).support (fun a =>
      arenaSum (evaluate f).support (fun b => if a+b=u then arenaJordan r (ce a) (cf b) else .literal 0))) e

private theorem evaluate_primitive (p : Primitive) : evaluate (.primitive p)=(primitiveValue p) := rfl
private theorem compile_primitive (p : Primitive) : compile (.primitive p)=(compilePrimitive p) := rfl
private theorem evaluate_addS (e f : Expression .symbol) : evaluate (.addS e f)=(evaluate e+evaluate f) := rfl
private theorem compile_addS (e f : Expression .symbol) : compile (.addS e f)=(.add (compile e) (compile f)) := rfl
private theorem evaluate_negS (e : Expression .symbol) : evaluate (.negS e)=(-evaluate e) := rfl
private theorem compile_negS (e : Expression .symbol) : compile (.negS e)=(arenaNegate (compile e)) := rfl
private theorem evaluate_mulS (e f : Expression .symbol) : evaluate (.mulS e f)=(evaluate e*evaluate f) := rfl
private theorem compile_mulS (e f : Expression .symbol) : compile (.mulS e f)=(arenaProduct (compile e) (compile f)) := rfl
private theorem evaluate_sumS {n : ℕ} (terms : Fin n → Expression .symbol) : evaluate (.sumS terms)=(∑ i,evaluate (terms i)) := rfl
private theorem compile_sumS {n : ℕ} (terms : Fin n → Expression .symbol) : compile (.sumS terms)=(arenaSum Finset.univ (fun i => compile (terms i))) := rfl
private theorem evaluate_coefficient (u : AngularExponent) (e : Expression .polynomial) : evaluate (.coefficient u e)=(MvPolynomial.coeff u (evaluate e)) := rfl
private theorem compile_coefficient (u : AngularExponent) (e : Expression .polynomial) : compile (.coefficient u e)=(compile e u) := rfl
private theorem evaluate_average (e : Expression .polynomial) : evaluate (.average e)=(average (evaluate e)) := rfl
private theorem compile_average (e : Expression .polynomial) : compile (.average e)=(arenaSum (evaluate e).support (fun u => arenaProduct (.literal (angularMoment u)) (compile e u))) := rfl
private theorem evaluate_zeroP  : evaluate Expression.zeroP=(0) := rfl
private theorem compile_zeroP  : compile Expression.zeroP=(fun _ => .literal 0) := rfl
private theorem evaluate_monomial (u : AngularExponent) (e : Expression .symbol) : evaluate (.monomial u e)=(MvPolynomial.monomial u (evaluate e)) := rfl
private theorem compile_monomial (u : AngularExponent) (e : Expression .symbol) : compile (.monomial u e)=(fun v => if u=v then compile e else .literal 0) := rfl
private theorem evaluate_addP (e f : Expression .polynomial) : evaluate (.addP e f)=(evaluate e+evaluate f) := rfl
private theorem compile_addP (e f : Expression .polynomial) : compile (.addP e f)=(fun u => .add (compile e u) (compile f u)) := rfl
private theorem evaluate_negP (e : Expression .polynomial) : evaluate (.negP e)=(-evaluate e) := rfl
private theorem compile_negP (e : Expression .polynomial) : compile (.negP e)=(fun u => arenaNegate (compile e u)) := rfl
private theorem evaluate_mulP (e f : Expression .polynomial) : evaluate (.mulP e f)=(evaluate e*evaluate f) := rfl
private theorem compile_mulP (e f : Expression .polynomial) : compile (.mulP e f)=(fun u => arenaSum (evaluate e).support (fun a => arenaSum (evaluate f).support (fun b => if a+b=u then arenaProduct (compile e a) (compile f b) else .literal 0))) := rfl
private theorem evaluate_sumP {n : ℕ} (terms : Fin n → Expression .polynomial) : evaluate (.sumP terms)=(∑ i,evaluate (terms i)) := rfl
private theorem compile_sumP {n : ℕ} (terms : Fin n → Expression .polynomial) : compile (.sumP terms)=(fun u => arenaSum Finset.univ (fun i => compile (terms i) u)) := rfl
private theorem evaluate_weighted (r : ℕ) (e f : Expression .polynomial) : evaluate (.weighted r e f)=(weighted r (evaluate e) (evaluate f)) := rfl
private theorem compile_weighted (r : ℕ) (e f : Expression .polynomial) : compile (.weighted r e f)=(fun u => arenaSum (evaluate e).support (fun a => arenaSum (evaluate f).support (fun b => if a+b=u then arenaJordan r (compile e a) (compile f b) else .literal 0))) := rfl

private theorem coefficient_product_support (P Q : AngularPolynomial) (u : AngularExponent) :
    MvPolynomial.coeff u (P*Q)=∑ a∈P.support,∑ b∈Q.support,
      if a+b=u then MvPolynomial.coeff a P*MvPolynomial.coeff b Q else 0 := by
  conv_lhs => rw [MvPolynomial.as_sum P,MvPolynomial.as_sum Q]
  simp only [Finset.sum_mul,Finset.mul_sum,MvPolynomial.monomial_mul,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  exact Finset.sum_comm

private theorem coefficient_weighted_support (r : ℕ) (P Q : AngularPolynomial) (u : AngularExponent) :
    MvPolynomial.coeff u (weighted r P Q)=∑ a∈P.support,∑ b∈Q.support,
      if a+b=u then scalarJordan r (MvPolynomial.coeff a P) (MvPolynomial.coeff b Q) else 0 := by
  simp only [weighted,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]

def CompilesTo : (s : ExprSort) → Compiled s → Value s → Prop
  | .symbol,e,f => ∀ x∈poleDomain,arenaEvaluate e x=(f x : ℂ)
  | .polynomial,e,P => ∀ u x,x∈poleDomain → arenaEvaluate (e u) x=((MvPolynomial.coeff u P) x : ℂ)

theorem compile_evaluate {s : ExprSort} (e : Expression s) : CompilesTo s (compile e) (evaluate e) := by
  induction e with
  | primitive p => exact compilePrimitive_evaluate p
  | addS e f he hf =>
    intro x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Pi.add_apply,Complex.ofReal_add]
    rw [he x hx,hf x hx]
  | negS e he =>
    intro x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaNegate_evaluate,he x hx]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Pi.neg_apply,Complex.ofReal_neg]
  | mulS e f he hf =>
    intro x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaProduct_evaluate,he x hx,hf x hx]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Pi.mul_apply,Complex.ofReal_mul]
  | sumS terms ih =>
    intro x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,Finset.sum_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ih i x hx
  | coefficient u e he => exact he u
  | average e he =>
    intro x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,average,Finset.sum_apply,Complex.ofReal_sum,Complex.ofReal_mul,arenaProduct_evaluate,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]
    apply Finset.sum_congr rfl
    intro u _
    rw [he u x hx]
  | zeroP => intro u x hx; simp [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]
  | monomial u e he =>
    intro v x hx
    by_cases h : u=v
    · subst v
      simpa only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted,ite_true,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_monomial] using he x hx
    · simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted,h,ite_false,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_monomial,Pi.zero_apply,Complex.ofReal_zero]
  | addP e f he hf =>
    intro u x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_add,Pi.add_apply,Complex.ofReal_add]
    rw [he u x hx,hf u x hx]
  | negP e he =>
    intro u x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaNegate_evaluate,he u x hx]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_neg,Pi.neg_apply,Complex.ofReal_neg]
  | mulP e f he hf =>
    intro u x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,coefficient_product_support,Finset.sum_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [arenaSum_evaluate]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a+b=u
    · simp only [h,ite_true,arenaProduct_evaluate,Pi.mul_apply,Complex.ofReal_mul]
      rw [he a x hx,hf b x hx]
    · simp only [h,ite_false,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,Pi.zero_apply,Complex.ofReal_zero]
  | sumP terms ih =>
    intro u x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,MvPolynomial.coeff_sum,Finset.sum_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ih i u x hx
  | weighted r e f he hf =>
    intro u x hx
    simp only [compile_primitive,compile_addS,compile_negS,compile_mulS,compile_sumS,compile_coefficient,compile_average,compile_zeroP,compile_monomial,compile_addP,compile_negP,compile_mulP,compile_sumP,compile_weighted]
    rw [arenaSum_evaluate]
    simp only [evaluate_primitive,evaluate_addS,evaluate_negS,evaluate_mulS,evaluate_sumS,evaluate_coefficient,evaluate_average,evaluate_zeroP,evaluate_monomial,evaluate_addP,evaluate_negP,evaluate_mulP,evaluate_sumP,evaluate_weighted,coefficient_weighted_support,Finset.sum_apply,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [arenaSum_evaluate]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : a+b=u
    · simp only [h,ite_true]
      exact arenaJordan_evaluate r _ _ _ _ (fun y hy => he a y hy) (fun y hy => hf b y hy) x hx
    · simp only [h,ite_false,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,Pi.zero_apply,Complex.ofReal_zero]

def arena_energy_expr (k : ℕ) : ArenaExpression 0 := compile (energy_expr k)
def arena_clock_definition_exprs (k : ℕ) (a : Fin 4) : ArenaExpression 0 := compile (clock_definition_exprs k a)

theorem arena_energy_readback (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (arena_energy_expr k) x=(sourceEngineEnergy k x : ℂ) := by
  have result := compile_evaluate (energy_expr k) x hx
  simpa only [energy_expr_readback,arena_energy_expr] using result

theorem arena_clock_definition_readback (k : ℕ) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (arena_clock_definition_exprs k a) x=(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ) := by
  have result := compile_evaluate (clock_definition_exprs k a) x hx
  simpa only [clock_definition_exprs_readback,arena_clock_definition_exprs] using result

theorem complexMoyal_zero (f g : Phase → ℂ) (x : Phase) :
    complexMoyal 0 f g x=f x*g x := by
  apply Complex.ext <;> simp [complexMoyal,coefficient_zero]

theorem arena_moyal_zero {k : ℕ} (e f : ArenaExpression k) (x : Phase) :
    arenaEvaluate (.moyal 0 e f) x=arenaEvaluate (arenaProduct e f) x := by
  rw [arenaProduct_evaluate,arenaEvaluate]
  exact complexMoyal_zero _ _ x

private theorem coefficient_const_left (r : ℕ) (c : ℝ) (f : Symbol) (x : Phase) :
    coefficient (r+1) (fun _ => c) f x=0 := by
  simp [coefficient,contraction,jet,iteratedFDeriv_succ_const]

private theorem coefficient_const_right (r : ℕ) (c : ℝ) (f : Symbol) (x : Phase) :
    coefficient (r+1) f (fun _ => c) x=0 := by
  rw [coefficient_swap,coefficient_const_left]
  simp

theorem arena_moyal_constant_left {k : ℕ} (r : ℕ) (c : ℝ) (e : ArenaExpression k) (x : Phase) :
    arenaEvaluate (.moyal (r+1) (.literal c) e) x=0 := by
  simp [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,complexMoyal,coefficient_const_left]

theorem arena_moyal_constant_right {k : ℕ} (r : ℕ) (c : ℝ) (e : ArenaExpression k) (x : Phase) :
    arenaEvaluate (.moyal (r+1) e (.literal c)) x=0 := by
  simp [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,complexMoyal,coefficient_const_right]

theorem complexMoyal_swap (r : ℕ) (f g : Phase → ℂ) (x : Phase) :
    complexMoyal r g f x=(-1 : ℂ)^r*complexMoyal r f g x := by
  conv_lhs =>
    unfold complexMoyal
    rw [coefficient_swap r (fun y => (f y).re) (fun y => (g y).re),
      coefficient_swap r (fun y => (f y).im) (fun y => (g y).im),
      coefficient_swap r (fun y => (f y).im) (fun y => (g y).re),
      coefficient_swap r (fun y => (f y).re) (fun y => (g y).im)]
  unfold complexMoyal
  ring

theorem arena_moyal_swap {k : ℕ} (r : ℕ) (e f : ArenaExpression k) (x : Phase) :
    arenaEvaluate (.moyal r f e) x=(-1 : ℂ)^r*arenaEvaluate (.moyal r e f) x := by
  simp only [arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add]
  exact complexMoyal_swap r _ _ x

theorem arena_moyal_odd_self {k : ℕ} (r : ℕ) (e : ArenaExpression k) (x : Phase) :
    arenaEvaluate (.moyal (2*r+1) e e) x=0 := by
  have swap := arena_moyal_swap (2*r+1) e e x
  have sign : (-1 : ℂ)^(2*r+1)= -1 := by simp [pow_add,pow_mul]
  rw [sign] at swap
  linear_combination (1/2 : ℂ)*swap

-- These are the actual scalar-N0 laws used by Arena.collect and its central-word
-- permutation. They are identities of the same coefficient/word occurrence.
theorem arena_row_permutation {k : ℕ} (c : NormalizedCoefficient)
    {word other : List (ArenaExpression k)} (h : word.Perm other) (x : Phase) :
    arenaEvaluate (.row c word) x=arenaEvaluate (.row c other) x := by
  rw [arenaEvaluate_row,arenaEvaluate_row]
  congr 1
  have result := (h.map (fun atom => arenaEvaluate atom x)).prod_eq
  simpa only [List.prod_eq_foldr,List.foldr_map] using result

theorem arena_collect {k : ℕ} (c d : NormalizedCoefficient) (word : List (ArenaExpression k))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.add (.row c word) (.row d word)) x=arenaEvaluate (.row (addCoefficient c d) word) x := by
  simp only [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,addCoefficient_source c d x hx,Complex.ofReal_add]
  ring

theorem arena_row_multiply {k : ℕ} (c d : NormalizedCoefficient)
    (word other : List (ArenaExpression k)) (x : Phase) :
    arenaEvaluate (.row c word) x*arenaEvaluate (.row d other) x=
      arenaEvaluate (.row (multiplyCoefficient c d) (word++other)) x := by
  have fold (l : List (ArenaExpression k)) :
      l.foldr (fun atom out => arenaEvaluate atom x*out) 1=(l.map (fun atom => arenaEvaluate atom x)).prod := by
    simp only [List.prod_eq_foldr,List.foldr_map]
  simp only [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,multiplyCoefficient_source,Complex.ofReal_mul,fold,List.map_append,List.prod_append]
  ring

theorem arena_coefficient_normalize {k : ℕ} (c : CentralExpression) (word : List (ArenaExpression k))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (.row (normalize c) word) x=(expressionValue c x : ℂ)*
      word.foldr (fun atom out => arenaEvaluate atom x*out) 1 := by
  simp only [arenaEvaluate_row,arenaEvaluate_literal,arenaEvaluate_source,arenaEvaluate_clock,arenaEvaluate_moyal,arenaEvaluate_row,arenaEvaluate_add,normalize_source c x hx]

end LowEnergy.PreparationVacuumDAGSemantic
