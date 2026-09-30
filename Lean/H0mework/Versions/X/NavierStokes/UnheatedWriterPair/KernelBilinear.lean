import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.Flux

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairKernelBilinear

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeHigherTimeJets NativeUnheatedPairInverseFlux

noncomputable section

variable (kernel : IntegerWavevector → IntegerWavevector → ℝ) (wave : IntegerWavevector)
  (output input : Coordinate) (budget : ℝ) (bounded : ∀ first, ‖kernel first (wave-first)‖ ≤ budget)

def value (left right : ComplexVorticityHilbertState) : ℂ :=
  -∑' first, kernel first (wave-first) • (left first input * right (wave-first) output)

include bounded

theorem budget_nonnegative : 0 ≤ budget := (norm_nonneg _).trans (bounded 0)

theorem summable_pair (left right : ComplexVorticityHilbertState) :
    Summable (fun first => kernel first (wave-first) • (left first input * right (wave-first) output)) := by
  apply Summable.of_norm
  apply ((mixed_pair_summable left right wave output input).norm.mul_left budget).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro first
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (bounded first) (norm_nonneg _)

theorem norm_bound (left right : ComplexVorticityHilbertState) :
    ‖value kernel wave output input left right‖ ≤ (3 * budget) * ‖left‖ * ‖right‖ := by
  rw [value, norm_neg]
  apply (norm_tsum_le_tsum_norm (summable_pair kernel wave output input budget bounded left right).norm).trans
  have bound := mul_le_mul_of_nonneg_left (absolute_pair_bound left right wave output input)
    (budget_nonnegative kernel wave budget bounded)
  apply le_trans _ (bound.trans_eq (by ring))
  rw [← tsum_mul_left]
  apply (summable_pair kernel wave output input budget bounded left right).norm.tsum_le_tsum _
    ((mixed_pair_summable left right wave output input).norm.mul_left budget)
  intro first
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (bounded first) (norm_nonneg _)

theorem add_left (left other right : ComplexVorticityHilbertState) :
    value kernel wave output input (left+other) right =
      value kernel wave output input left right + value kernel wave output input other right := by
  simp only [value, lp.coeFn_add, Pi.add_apply, add_mul, smul_add]
  rw [(summable_pair kernel wave output input budget bounded left right).tsum_add
    (summable_pair kernel wave output input budget bounded other right), neg_add]

theorem add_right (left right other : ComplexVorticityHilbertState) :
    value kernel wave output input left (right+other) =
      value kernel wave output input left right + value kernel wave output input left other := by
  simp only [value, lp.coeFn_add, Pi.add_apply, mul_add, smul_add]
  rw [(summable_pair kernel wave output input budget bounded left right).tsum_add
    (summable_pair kernel wave output input budget bounded left other), neg_add]

theorem smul_left (scalar : ℝ) (left right : ComplexVorticityHilbertState) :
    value kernel wave output input (scalar • left) right = scalar • value kernel wave output input left right := by
  simp only [value, lp.coeFn_smul, Pi.smul_apply, smul_mul_assoc, smul_neg]
  simp_rw [smul_comm _ scalar]
  rw [Summable.tsum_const_smul scalar (summable_pair kernel wave output input budget bounded left right)]

theorem smul_right (scalar : ℝ) (left right : ComplexVorticityHilbertState) :
    value kernel wave output input left (scalar • right) = scalar • value kernel wave output input left right := by
  simp only [value, lp.coeFn_smul, Pi.smul_apply, mul_smul_comm, smul_neg]
  simp_rw [smul_comm _ scalar]
  rw [Summable.tsum_const_smul scalar (summable_pair kernel wave output input budget bounded left right)]

def linear : ComplexVorticityHilbertState →ₗ[ℝ] ComplexVorticityHilbertState →ₗ[ℝ] ℂ where
  toFun left :=
    { toFun := value kernel wave output input left
      map_add' := add_right kernel wave output input budget bounded left
      map_smul' scalar right := smul_right kernel wave output input budget bounded scalar left right }
  map_add' left other := by
    ext right
    exact add_left kernel wave output input budget bounded left other right
  map_smul' scalar left := by
    ext right
    exact smul_left kernel wave output input budget bounded scalar left right

def bilinear : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState →L[ℝ] ℂ :=
  (linear kernel wave output input budget bounded).mkContinuous₂ (3 * budget)
    (norm_bound kernel wave output input budget bounded)

@[simp] theorem bilinear_apply (left right : ComplexVorticityHilbertState) :
    bilinear kernel wave output input budget bounded left right = value kernel wave output input left right := rfl

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairKernelBilinear
