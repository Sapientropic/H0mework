import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.SourceDeterminantPerturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceQuantumCoefficientErrorOwn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open GaussComposite.ActualDressedUniformMaterialCoefficients GaussComposite.ActualDressedEMTensorClock
open GaussComposite.ActualDressedVisiblePole GaussComposite.ActualEMResponseSplit
open GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualEMCarrierOwn
open scoped BigOperators Matrix

private theorem bilinear_error {ι : Type*} [Fintype ι] (d : ℂ) (fd fs : ι→ℂ) (A B : Matrix ι ι ℂ)
    (E : ℝ) (error : ∀ i j,‖A i j-B i j‖ ≤ E) :
    ‖d*dotProduct fd (A*ᵥfs)-d*dotProduct fd (B*ᵥfs)‖ ≤ ∑ i,∑ j,‖d‖*‖fd i‖*E*‖fs j‖ := by
  have difference : d*dotProduct fd (A*ᵥfs)-d*dotProduct fd (B*ᵥfs)=
      ∑ i,∑ j,d*fd i*(A i j-B i j)*fs j := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [difference]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (error i j) (by positivity)) (norm_nonneg _)

def sourceEMNumeratorWindow (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (mu nu : Fin 4) : ℂ :=
  sourceStaticCommonDenominator event eps sigma n * dotProduct (fun i=>emInsertion i mu)
    ((sourceStaticClearedWindow event eps sigma n bits).adjugate*ᵥfun j=>emInsertion j nu)

def sourceEMNumeratorError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (mu nu : Fin 4) : ℝ :=
  ∑ i,∑ j,‖sourceStaticCommonDenominator event eps sigma n‖*‖emInsertion i mu‖*
    sourceClearedDeterminantError event eps sigma n bits 288*‖emInsertion j nu‖

attribute [local irreducible] commonClearedPencil commonEMTensorNumerator sourceStaticClearedWindow
  sourceStaticCommonDenominator emInsertion sourceEMNumeratorWindow sourceEMNumeratorError

theorem actual_source_EM16_numerator_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) (mu nu : Fin 4) :
    ‖MvPolynomial.eval (irValues eps sigma 0) (commonEMTensorNumerator event n mu nu)-
      sourceEMNumeratorWindow event eps sigma n bits mu nu‖ ≤ sourceEMNumeratorError event eps sigma n bits mu nu := by
  rw [common_em_tensor_numerator_eval]
  unfold sourceEMNumeratorWindow sourceEMNumeratorError sourceStaticCommonDenominator
  exact bilinear_error _ _ _ _ _ _ (actual_source_adjugate_entry_error event eps sigma n positive small bits)

def sourceCommonDeterminantMargin (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) : ℝ :=
  ‖(sourceStaticClearedWindow event eps sigma n bits).det‖-sourceClearedDeterminantError event eps sigma n bits 289

theorem actual_source_denominator_lower (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) :
    sourceCommonDeterminantMargin event eps sigma n bits ≤ ‖MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n)‖ := by
  have error:=actual_source_symbolic_denominator_error event eps sigma n positive small bits
  have lower:=norm_sub_norm_le (sourceStaticClearedWindow event eps sigma n bits).det
    (MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n))
  rw [norm_sub_rev] at lower
  unfold sourceCommonDeterminantMargin
  linarith

end LowEnergy.ActualSourceQuantumCoefficientErrorOwn
