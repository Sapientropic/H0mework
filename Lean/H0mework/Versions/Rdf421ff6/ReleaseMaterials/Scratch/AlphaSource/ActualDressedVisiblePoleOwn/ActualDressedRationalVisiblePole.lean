import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualDressedVisiblePole
open Polynomial
open scoped Polynomial

def readFraction (N D : ℂ[X]) : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D
def visibleRoots (R : RatFunc ℂ) : Multiset ℂ := R.denom.roots
def poleOrder (R : RatFunc ℂ) (a : ℂ) : ℕ := R.denom.rootMultiplicity a
def rootPower (R : RatFunc ℂ) (a : ℂ) : ℂ[X] := (X-C a)^poleOrder R a
def rootRemainder (R : RatFunc ℂ) (a : ℂ) : ℂ[X] := R.denom /ₘ rootPower R a

theorem reduced_denominator_dvd (N D : ℂ[X]) : (readFraction N D).denom ∣ D :=
  RatFunc.denom_div_dvd N D

theorem reduced_cross_identity (N D : ℂ[X]) (nonzero : D ≠ 0) :
    (readFraction N D).num * D = N * (readFraction N D).denom :=
  (RatFunc.num_mul_eq_mul_denom_iff nonzero).mpr rfl

theorem reduced_denominator_at_regular (N D : ℂ[X]) (a : ℂ) (regular : D.eval a ≠ 0) :
    (readFraction N D).denom.eval a ≠ 0 := by
  obtain ⟨Q, hQ⟩ := reduced_denominator_dvd N D
  intro zero
  apply regular
  rw [hQ, eval_mul, zero, zero_mul]

theorem reduced_read_at_regular (N D : ℂ[X]) (a : ℂ) (regular : D.eval a ≠ 0) :
    (readFraction N D).num.eval a / (readFraction N D).denom.eval a = N.eval a / D.eval a := by
  have nonzero : D ≠ 0 := by
    intro zero
    apply regular
    rw [zero, eval_zero]
  have cross := congrArg (Polynomial.eval a) (reduced_cross_identity N D nonzero)
  simp only [eval_mul] at cross
  exact (div_eq_div_iff (reduced_denominator_at_regular N D a regular) regular).mpr cross

theorem visible_root_iff (R : RatFunc ℂ) (a : ℂ) :
    a ∈ visibleRoots R ↔ R.denom.eval a = 0 := by
  exact mem_roots (RatFunc.denom_ne_zero R)

theorem visible_numerator_nonzero (R : RatFunc ℂ) (a : ℂ) (root : a ∈ visibleRoots R) :
    R.num.eval a ≠ 0 := by
  have zero := (visible_root_iff R a).mp root
  obtain ⟨u, v, bezout⟩ := RatFunc.isCoprime_num_denom R
  intro numZero
  have impossible := congrArg (Polynomial.eval a) bezout
  simp only [eval_add, eval_mul, eval_one, numZero, zero, mul_zero, zero_add] at impossible
  exact zero_ne_one impossible

theorem visible_pole_order_positive (R : RatFunc ℂ) (a : ℂ) (root : a ∈ visibleRoots R) :
    0 < poleOrder R a :=
  (rootMultiplicity_pos (RatFunc.denom_ne_zero R)).mpr ((visible_root_iff R a).mp root)

theorem visible_roots_count (R : RatFunc ℂ) (a : ℂ) :
    (visibleRoots R).count a = poleOrder R a := count_roots R.denom

theorem denominator_root_factor (R : RatFunc ℂ) (a : ℂ) :
    rootPower R a * rootRemainder R a = R.denom :=
  pow_mul_divByMonic_rootMultiplicity_eq R.denom a

theorem root_remainder_nonzero (R : RatFunc ℂ) (a : ℂ) :
    (rootRemainder R a).eval a ≠ 0 :=
  eval_divByMonic_pow_rootMultiplicity_ne_zero a (RatFunc.denom_ne_zero R)

def leadingPoleCoefficient (R : RatFunc ℂ) (a : ℂ) : ℂ := R.num.eval a / (rootRemainder R a).eval a
theorem leading_pole_coefficient_nonzero (R : RatFunc ℂ) (a : ℂ) (root : a ∈ visibleRoots R) :
    leadingPoleCoefficient R a ≠ 0 :=
  div_ne_zero (visible_numerator_nonzero R a root) (root_remainder_nonzero R a)

private theorem coprime_linear_of_eval_ne_zero (Q : ℂ[X]) (a : ℂ) (nonzero : Q.eval a ≠ 0) :
    IsCoprime Q (X-C a) := by
  have division := modByMonic_add_div Q (X-C a)
  rw [modByMonic_X_sub_C_eq_C_eval] at division
  have balance : Q-(X-C a)*(Q /ₘ (X-C a))=C (Q.eval a) := by linear_combination -division
  refine ⟨C ((Q.eval a)⁻¹), -C ((Q.eval a)⁻¹) * (Q /ₘ (X-C a)), ?_⟩
  calc
    _ = C ((Q.eval a)⁻¹) * (Q-(X-C a)*(Q /ₘ (X-C a))) := by ring
    _ = C ((Q.eval a)⁻¹) * C (Q.eval a) := congrArg (fun P : ℂ[X] => C ((Q.eval a)⁻¹)*P) balance
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ nonzero, C_1]

def bezoutLeft (Q P : ℂ[X]) : ℂ[X] :=
  Ring.inverse (EuclideanDomain.gcd Q P) * EuclideanDomain.gcdA Q P
def bezoutRight (Q P : ℂ[X]) : ℂ[X] :=
  Ring.inverse (EuclideanDomain.gcd Q P) * EuclideanDomain.gcdB Q P

theorem source_bezout (Q P : ℂ[X]) (coprime : IsCoprime Q P) :
    Q*bezoutLeft Q P+P*bezoutRight Q P=1 := by
  classical
  calc
    _ = Ring.inverse (EuclideanDomain.gcd Q P) *
        (Q*EuclideanDomain.gcdA Q P+P*EuclideanDomain.gcdB Q P) := by
      unfold bezoutLeft bezoutRight
      ring
    _ = Ring.inverse (EuclideanDomain.gcd Q P) * EuclideanDomain.gcd Q P :=
      congrArg (fun g : ℂ[X] => Ring.inverse (EuclideanDomain.gcd Q P)*g)
        (EuclideanDomain.gcd_eq_gcd_ab Q P).symm
    _ = 1 := Ring.inverse_mul_cancel _ (EuclideanDomain.gcd_isUnit_iff.mpr coprime)

theorem root_remainder_coprime (R : RatFunc ℂ) (a : ℂ) :
    IsCoprime (rootRemainder R a) (rootPower R a) :=
  (coprime_linear_of_eval_ne_zero _ a (root_remainder_nonzero R a)).pow_right

def principalNumerator (R : RatFunc ℂ) (a : ℂ) : ℂ[X] :=
  (R.num*bezoutLeft (rootRemainder R a) (rootPower R a)) %ₘ rootPower R a
def analyticNumerator (R : RatFunc ℂ) (a : ℂ) : ℂ[X] :=
  R.num*bezoutRight (rootRemainder R a) (rootPower R a)+
    ((R.num*bezoutLeft (rootRemainder R a) (rootPower R a)) /ₘ rootPower R a)*rootRemainder R a
def principalCoefficient (R : RatFunc ℂ) (a : ℂ) (k : ℕ) : ℂ :=
  ((principalNumerator R a).comp (X+C a)).coeff k
def poleResidue (R : RatFunc ℂ) (a : ℂ) : ℂ := principalCoefficient R a (poleOrder R a-1)

theorem principal_polynomial_identity (R : RatFunc ℂ) (a : ℂ) :
    R.num=principalNumerator R a*rootRemainder R a+rootPower R a*analyticNumerator R a := by
  have bezout := source_bezout _ _ (root_remainder_coprime R a)
  have division := modByMonic_add_div (R.num*bezoutLeft (rootRemainder R a) (rootPower R a)) (rootPower R a)
  unfold principalNumerator analyticNumerator
  linear_combination -R.num*bezout -rootRemainder R a*division

theorem principal_degree (R : RatFunc ℂ) (a : ℂ) :
    (principalNumerator R a).degree < (poleOrder R a : WithBot ℕ) := by
  have monic : (rootPower R a).Monic := (monic_X_sub_C a).pow _
  have bound := degree_modByMonic_lt (R.num*bezoutLeft (rootRemainder R a) (rootPower R a)) monic
  simpa only [principalNumerator, rootPower, degree_pow, degree_X_sub_C, nsmul_eq_mul, mul_one] using bound

theorem principal_value_at_root (R : RatFunc ℂ) (a : ℂ) (root : a ∈ visibleRoots R) :
    (principalNumerator R a).eval a=leadingPoleCoefficient R a := by
  have identity := congrArg (Polynomial.eval a) (principal_polynomial_identity R a)
  have positive := visible_pole_order_positive R a root
  simp only [eval_add, eval_mul, rootPower, eval_pow, eval_sub, eval_X, eval_C, sub_self,
    zero_pow positive.ne', zero_mul, add_zero] at identity
  exact (eq_div_iff (root_remainder_nonzero R a)).mpr identity.symm

theorem principal_leading_nonzero (R : RatFunc ℂ) (a : ℂ) (root : a ∈ visibleRoots R) :
    principalCoefficient R a 0 ≠ 0 := by
  have value : principalCoefficient R a 0=(principalNumerator R a).eval a := by
    simp [principalCoefficient, coeff_zero_eq_eval_zero, eval_comp]
  rw [value, principal_value_at_root R a root]
  exact leading_pole_coefficient_nonzero R a root

theorem principal_analytic_remainder (R : RatFunc ℂ) (a : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (analyticNumerator R a).eval z/(rootRemainder R a).eval z) a :=
  ((AnalyticOnNhd.eval_polynomial (analyticNumerator R a)) a (Set.mem_univ a)).div
    ((AnalyticOnNhd.eval_polynomial (rootRemainder R a)) a (Set.mem_univ a))
    (root_remainder_nonzero R a)

theorem complete_principal_part (R : RatFunc ℂ) (a z : ℂ) (away : z ≠ a)
    (regular : (rootRemainder R a).eval z ≠ 0) :
    R.num.eval z / R.denom.eval z =
      (principalNumerator R a).eval z / (z-a)^poleOrder R a+
        (analyticNumerator R a).eval z / (rootRemainder R a).eval z := by
  have factor := congrArg (Polynomial.eval z) (denominator_root_factor R a)
  have numerator := congrArg (Polynomial.eval z) (principal_polynomial_identity R a)
  simp only [eval_mul, rootPower, eval_pow, eval_sub, eval_X, eval_C] at factor
  simp only [eval_mul, eval_add, rootPower, eval_pow, eval_sub, eval_X, eval_C] at numerator
  rw [← factor, numerator]
  field_simp [regular, pow_ne_zero (poleOrder R a) (sub_ne_zero.mpr away)]

theorem principal_negative_powers (R : RatFunc ℂ) (a z : ℂ) (root : a ∈ visibleRoots R) :
    (principalNumerator R a).eval z/(z-a)^poleOrder R a =
      ∑ k ∈ Finset.range (poleOrder R a), principalCoefficient R a k*(z-a)^k/(z-a)^poleOrder R a := by
  have nonzero : principalNumerator R a ≠ 0 := by
    intro zero
    have value := principal_value_at_root R a root
    have leading := leading_pole_coefficient_nonzero R a root
    rw [zero, eval_zero] at value
    exact leading value.symm
  have bound : (taylor a (principalNumerator R a)).natDegree < poleOrder R a := by
    rw [natDegree_taylor]
    exact (natDegree_lt_iff_degree_lt nonzero).mpr (principal_degree R a)
  have expansion := (taylor a (principalNumerator R a)).eval_eq_sum_range' bound (z-a)
  rw [taylor_eval_sub] at expansion
  rw [expansion, Finset.sum_div]
  rfl

theorem reduced_analytic_at (R : RatFunc ℂ) (a : ℂ) (regular : R.denom.eval a ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => R.num.eval z/R.denom.eval z) a :=
  ((AnalyticOnNhd.eval_polynomial R.num) a (Set.mem_univ a)).div
    ((AnalyticOnNhd.eval_polynomial R.denom) a (Set.mem_univ a)) regular

theorem pole_order_limit (R : RatFunc ℂ) (a : ℂ) :
    Filter.Tendsto (fun z : ℂ => (z-a)^poleOrder R a*(R.num.eval z/R.denom.eval z))
      (nhdsWithin a ({a}ᶜ)) (nhds (leadingPoleCoefficient R a)) := by
  have remainder : AnalyticAt ℂ (fun z : ℂ => (rootRemainder R a).eval z) a :=
    (AnalyticOnNhd.eval_polynomial (rootRemainder R a)) a (Set.mem_univ a)
  have numerator : AnalyticAt ℂ (fun z : ℂ => R.num.eval z) a :=
    (AnalyticOnNhd.eval_polynomial R.num) a (Set.mem_univ a)
  have continuous := numerator.continuousAt.div remainder.continuousAt (root_remainder_nonzero R a)
  have near : ∀ᶠ z in nhds a, (rootRemainder R a).eval z ≠ 0 :=
    remainder.continuousAt.eventually_ne (root_remainder_nonzero R a)
  apply Filter.Tendsto.congr' _ (continuous.tendsto.mono_left inf_le_left)
  filter_upwards [near.filter_mono inf_le_left, self_mem_nhdsWithin] with z regular away
  have nonzero : z-a ≠ 0 := sub_ne_zero.mpr (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using away)
  have factor := congrArg (Polynomial.eval z) (denominator_root_factor R a)
  simp only [eval_mul, rootPower, eval_pow, eval_sub, eval_X, eval_C] at factor
  simp only [Pi.div_apply]
  rw [← factor]
  field_simp [regular, pow_ne_zero (poleOrder R a) nonzero]

inductive ReadDisposition (N D : ℂ[X]) : Type
  | singular (denominator_zero : D = 0)
  | zeroRead (denominator_nonzero : D ≠ 0) (numerator_zero : N = 0)
  | nonzeroRead (denominator_nonzero : D ≠ 0) (numerator_nonzero : N ≠ 0)

def sourceReadDisposition (N D : ℂ[X]) : ReadDisposition N D := by
  classical
  exact if hd : D = 0 then .singular hd else if hn : N = 0 then .zeroRead hd hn else .nonzeroRead hd hn

def sourcePoleRoots (N D : ℂ[X]) : Option (Multiset ℂ) := by
  classical
  exact if D = 0 then none else some (visibleRoots (readFraction N D))

theorem singular_no_pole_packet (N D : ℂ[X]) (singular : D = 0) : sourcePoleRoots N D = none := by
  simp only [sourcePoleRoots, if_pos singular]

theorem regular_pole_packet (N D : ℂ[X]) (regular : D ≠ 0) :
    sourcePoleRoots N D = some (visibleRoots (readFraction N D)) := by
  simp only [sourcePoleRoots, if_neg regular]

theorem zero_read_no_visible_roots (D : ℂ[X]) : visibleRoots (readFraction 0 D) = 0 := by
  simp [visibleRoots, readFraction]

section Matrix
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem adjugate_green_identity (P H G : Matrix ι ι ℂ) (d : ℂ)
    (clear : d • P = H) (inverse : P*G=1) : H.det • G = d • H.adjugate := by
  have closed : H*G=d • 1 := by rw [← clear, Matrix.smul_mul, inverse]
  have paid := congrArg (fun A : Matrix ι ι ℂ => H.adjugate*A) closed
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one] at paid
  exact paid

theorem adjugate_full_read (P H G : Matrix ι ι ℂ) (d : ℂ) (fd fs : ι → ℂ)
    (clear : d • P = H) (inverse : P*G=1) :
    H.det * dotProduct fd (G*ᵥfs) = d*dotProduct fd (H.adjugate*ᵥfs) := by
  have paid := congrArg (fun A : Matrix ι ι ℂ => dotProduct fd (A*ᵥfs))
    (adjugate_green_identity P H G d clear inverse)
  simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using paid

end Matrix

end LowEnergy.ActualDressedVisiblePole

#print axioms LowEnergy.ActualDressedVisiblePole.visible_numerator_nonzero
#print axioms LowEnergy.ActualDressedVisiblePole.complete_principal_part
#print axioms LowEnergy.ActualDressedVisiblePole.principal_negative_powers
#print axioms LowEnergy.ActualDressedVisiblePole.pole_order_limit
