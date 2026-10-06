import H0mework.Realization.Perfectification.Quantum.Forms.Ground.Approximate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Generic analytic producer for the form A†A+R. A is the closed first-order
factor, R the bounded self-adjoint remainder. No resolvent, normalized vector,
phase or physical source realization is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace LinearPMap
namespace SaturationMonoid.Quantum.Forms.BoundedRemainder

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def positiveRemainder (R : H →L[ℂ] H) : H →L[ℂ] H :=
  R + algebraMap ℝ (H →L[ℂ] H) ‖R‖

theorem positiveRemainder_nonnegative (R : H →L[ℂ] H) (selfAdjoint : IsSelfAdjoint R) :
    0 ≤ positiveRemainder R := by
  simpa only [positiveRemainder, sub_neg_eq_add] using
    (sub_nonneg.mpr selfAdjoint.neg_algebraMap_norm_le_self)

def squareRoot (R : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (positiveRemainder R)

theorem squareRoot_selfAdjoint (R : H →L[ℂ] H) : IsSelfAdjoint (squareRoot R) :=
  (CFC.sqrt_nonneg (positiveRemainder R)).isSelfAdjoint

theorem squareRoot_square (R : H →L[ℂ] H) (selfAdjoint : IsSelfAdjoint R) :
    squareRoot R * squareRoot R = positiveRemainder R :=
  CFC.sqrt_mul_sqrt_self _ (positiveRemainder_nonnegative R selfAdjoint)

theorem squareRoot_pair (R : H →L[ℂ] H) (selfAdjoint : IsSelfAdjoint R) (x y : H) :
    inner ℂ (squareRoot R x) (squareRoot R y) = inner ℂ x (positiveRemainder R y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (squareRoot_selfAdjoint R).adjoint_eq]
  exact congrArg (inner ℂ x) (congrArg (fun T : H →L[ℂ] H => T y) (squareRoot_square R selfAdjoint))

abbrev Augmented := WithLp 2 (F × H)

def augmented (A : H →ₗ.[ℂ] F) (R : H →L[ℂ] H) : H →ₗ.[ℂ] Augmented (H := H) (F := F) where
  domain := A.domain
  toFun := (WithLp.linearEquiv 2 ℂ (F × H)).symm.toLinearMap.comp
    (A.toFun.prod ((squareRoot R).toLinearMap.comp A.domain.subtype))

omit [CompleteSpace F] in
theorem augmented_apply (A : H →ₗ.[ℂ] F) (R : H →L[ℂ] H) (x : A.domain) :
    augmented A R x = WithLp.toLp 2 (A x, squareRoot R x.val) := rfl

omit [CompleteSpace F] in
theorem augmented_closed (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H) :
    (augmented A R).IsClosed := by
  have graph : ((augmented A R).graph : Set (H × Augmented (H := H) (F := F))) =
      {p | (p.1,p.2.fst) ∈ A.graph ∧ p.2.snd=squareRoot R p.1} := by
    ext p
    constructor
    · intro member
      obtain ⟨x, hx, hy⟩ := (augmented A R).mem_graph_iff.mp member
      change (p.1,p.2.fst) ∈ A.graph ∧ p.2.snd=squareRoot R p.1
      rw [← hx, ← hy]
      exact ⟨A.mem_graph x, rfl⟩
    · rintro ⟨member, hs⟩
      obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp member
      refine (augmented A R).mem_graph_iff.mpr ⟨x, hx, ?_⟩
      apply (WithLp.linearEquiv 2 ℂ (F × H)).injective
      change (A x, squareRoot R x.val) = (p.2.fst,p.2.snd)
      exact Prod.ext hy (hx ▸ hs.symm)
  change IsClosed ((augmented A R).graph : Set (H × Augmented (H := H) (F := F)))
  rw [graph]
  have unpack := (WithLp.prod_continuous_ofLp 2 F H).comp
    (continuous_snd : Continuous (Prod.snd : H × Augmented (H := H) (F := F) → _))
  exact (closed.preimage (continuous_fst.prodMk unpack.fst)).inter
    (isClosed_eq unpack.snd ((squareRoot R).continuous.comp continuous_fst))

def form (A : H →ₗ.[ℂ] F) (R : H →L[ℂ] H) (x y : A.domain) : ℂ :=
  inner ℂ (A x) (A y) + inner ℂ x.val (R y.val)

def shift (R : H →L[ℂ] H) : ℝ := 1+‖R‖

omit [CompleteSpace F] in
theorem augmented_pair (A : H →ₗ.[ℂ] F) (R : H →L[ℂ] H)
    (selfAdjoint : IsSelfAdjoint R) (x y : A.domain) :
    inner ℂ (augmented A R x) (augmented A R y) =
      form A R x y + (‖R‖ : ℂ)*inner ℂ x.val y.val := by
  rw [augmented_apply, augmented_apply, WithLp.prod_inner_apply, squareRoot_pair R selfAdjoint]
  change inner ℂ (A x) (A y) + inner ℂ x.val (R y.val + (‖R‖ : ℂ) • y.val) = _
  rw [inner_add_right, inner_smul_right]
  unfold form
  ring

def resolvent (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H) : H →L[ℂ] H :=
  Graph.resolvent (augmented A R) (augmented_closed A closed R)

theorem resolvent_positive (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H) :
    (resolvent A closed R).IsPositive :=
  Graph.resolvent_positive (augmented A R) (augmented_closed A closed R)

theorem resolvent_injective (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) :
    Function.Injective (resolvent A closed R) :=
  Graph.resolvent_injective (augmented A R) (augmented_closed A closed R) dense

def solution (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H) (x : H) : A.domain :=
  Graph.solution (augmented A R) (augmented_closed A closed R) x

theorem riesz_pair (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H)
    (selfAdjoint : IsSelfAdjoint R) (x : H) (y : A.domain) :
    form A R (solution A closed R x) y +
      (shift R : ℂ)*inner ℂ (resolvent A closed R x) y.val = inner ℂ x y.val := by
  have h := Graph.variational (augmented A R) (augmented_closed A closed R) x y
  rw [inner_sub_left, augmented_pair A R selfAdjoint] at h
  change inner ℂ x y.val-inner ℂ (resolvent A closed R x) y.val =
    form A R (solution A closed R x) y + (‖R‖ : ℂ)*inner ℂ (resolvent A closed R x) y.val at h
  unfold shift
  push_cast
  linear_combination -h

theorem riesz_pair_right (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H)
    (selfAdjoint : IsSelfAdjoint R) (x : H) (y : A.domain) :
    form A R y (solution A closed R x) +
      (shift R : ℂ)*inner ℂ y.val (resolvent A closed R x) = inner ℂ y.val x := by
  have h := congrArg (starRingEnd ℂ) (riesz_pair A closed R selfAdjoint x y)
  simp only [map_add, map_mul, form, inner_conj_symm] at h
  have symmetric : inner ℂ (R y.val) (solution A closed R x).val =
      inner ℂ y.val (R (solution A closed R x).val) :=
    selfAdjoint.isSymmetric y.val (solution A closed R x).val
  rw [symmetric,
    show (starRingEnd ℂ) (shift R : ℂ)=(shift R : ℂ) by simp] at h
  exact h

def operator (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := (Forms.hamiltonian (augmented A R) (augmented_closed A closed R) dense).domain
  toFun := (Forms.hamiltonian (augmented A R) (augmented_closed A closed R) dense).toFun -
    (‖R‖ : ℂ) • (Forms.hamiltonian (augmented A R) (augmented_closed A closed R) dense).domain.subtype

def factorPoint (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H)
    (x : (operator A closed dense R).domain) : A.domain :=
  Forms.derivativePoint (augmented A R) (augmented_closed A closed R) dense x

theorem factorPoint_val (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H)
    (x : (operator A closed dense R).domain) : (factorPoint A closed dense R x).val=x.val :=
  Forms.derivativePoint_val (augmented A R) (augmented_closed A closed R) dense x

theorem operator_form (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) (selfAdjoint : IsSelfAdjoint R)
    (x : (operator A closed dense R).domain) (y : A.domain) :
    inner ℂ (operator A closed dense R x) y.val = form A R (factorPoint A closed dense R x) y := by
  have original := Forms.hamiltonian_form (augmented A R) (augmented_closed A closed R) dense x y
  change inner ℂ (Forms.hamiltonian (augmented A R) (augmented_closed A closed R) dense x) y.val =
    inner ℂ (augmented A R (factorPoint A closed dense R x)) (augmented A R y) at original
  have value : (factorPoint A closed dense R x).val=x.val :=
    Forms.derivativePoint_val (augmented A R) (augmented_closed A closed R) dense x
  change inner ℂ (Forms.hamiltonian (augmented A R) (augmented_closed A closed R) dense x -
    (‖R‖ : ℂ) • x.val) y.val = _
  rw [inner_sub_left, original, augmented_pair A R selfAdjoint, inner_smul_left, value]
  rw [show (starRingEnd ℂ) (‖R‖ : ℂ) = (‖R‖ : ℂ) by simp]
  ring

def resolventPoint (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) (x : H) :
    (operator A closed dense R).domain :=
  Forms.resolventPoint (augmented A R) (augmented_closed A closed R) dense x

theorem operator_resolvent (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) (x : H) :
    operator A closed dense R (resolventPoint A closed dense R x) +
      (shift R : ℂ) • resolvent A closed R x = x := by
  have h := Forms.resolvent_equation (augmented A R) (augmented_closed A closed R) dense x
  change (Forms.hamiltonian (augmented A R) (augmented_closed A closed R) dense
      (Forms.resolventPoint (augmented A R) (augmented_closed A closed R) dense x) -
      (‖R‖ : ℂ) • resolvent A closed R x) + (shift R : ℂ) • resolvent A closed R x = x
  rw [show (shift R : ℂ) = 1+(‖R‖ : ℂ) by simp [shift], add_smul, one_smul]
  convert! h using 1; abel

def energy (A : H →ₗ.[ℂ] F) (closed : A.IsClosed) (R : H →L[ℂ] H) : ℝ :=
  ‖resolvent A closed R‖⁻¹-shift R

theorem normalized_approximate [Nontrivial H] (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ x : (operator A closed dense R).domain, ‖x.val‖=1 ∧
      ‖operator A closed dense R x - (energy A closed R : ℂ) • x.val‖ < epsilon := by
  obtain ⟨x, unit, small⟩ := Approximate.inverse_approximate (resolvent A closed R)
    (resolvent_injective A closed dense R) (resolvent_positive A closed R) epsilon positive
  refine ⟨x, unit, ?_⟩
  change ‖(Inverse.operator (resolvent A closed R) _ x - (‖R‖ : ℂ) • x.val) -
    (energy A closed R : ℂ) • x.val‖ < epsilon
  have same : (Inverse.operator (resolvent A closed R) _ x - (‖R‖ : ℂ) • x.val) -
      (energy A closed R : ℂ) • x.val =
      Inverse.operator (resolvent A closed R) _ x -
        (Approximate.energy (resolvent A closed R) : ℂ) • x.val := by
    simp only [energy, shift, Approximate.energy, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_one, sub_smul, add_smul, one_smul]
    abel
  rwa [same]

theorem form_preparation [Nontrivial H] (A : H →ₗ.[ℂ] F) (closed : A.IsClosed)
    (dense : Dense (A.domain : Set H)) (R : H →L[ℂ] H) (selfAdjoint : IsSelfAdjoint R)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ x : (operator A closed dense R).domain, ‖x.val‖=1 ∧
      ‖operator A closed dense R x - (energy A closed R : ℂ) • x.val‖ < epsilon ∧
      ∀ y : A.domain, inner ℂ (operator A closed dense R x) y.val =
        inner ℂ (A (factorPoint A closed dense R x)) (A y) +
          inner ℂ x.val (R y.val) := by
  obtain ⟨x, unit, near⟩ := normalized_approximate A closed dense R epsilon positive
  refine ⟨x, unit, near, ?_⟩
  intro y
  simpa only [form, factorPoint_val] using operator_form A closed dense R selfAdjoint x y

end SaturationMonoid.Quantum.Forms.BoundedRemainder
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.augmented_closed
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.riesz_pair
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.riesz_pair_right
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.operator_form
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.operator_resolvent
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.normalized_approximate
#print axioms SaturationMonoid.Quantum.Forms.BoundedRemainder.form_preparation
