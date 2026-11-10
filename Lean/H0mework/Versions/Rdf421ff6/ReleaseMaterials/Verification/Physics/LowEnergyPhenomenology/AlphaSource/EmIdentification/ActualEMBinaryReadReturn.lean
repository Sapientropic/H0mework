import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNumeratorError
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMStaticCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceQuantumCoefficientErrorOwn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open GaussComposite.ActualDressedEMTensorClock GaussComposite.ActualDressedVisiblePole
open GaussComposite.ActualDressedCorrectedGreen GaussComposite.ActualDressedUniformMaterialCoefficients
open GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualEMCarrierOwn
open scoped BigOperators Matrix

private theorem inverse_price (D : ℂ) (m : ℝ) (positive : 0 < m) (lower : m ≤ ‖D‖) :
    D≠0 ∧ ‖D⁻¹‖ ≤ 1/m := by
  have nonzero : D≠0 := by intro zero; rw [zero,norm_zero] at lower; linarith
  refine ⟨nonzero,?_⟩
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le positive lower

private theorem quotient_error (N D n d : ℂ) (EN ED m : ℝ) (positive : 0 < m)
    (lower : m ≤ ‖D‖) (lowerWindow : m ≤ ‖d‖)
    (errorN : ‖N-n‖ ≤ EN) (errorD : ‖D-d‖ ≤ ED) :
    ‖N/D-n/d‖ ≤ (EN+‖n‖*ED/m)/m := by
  have inv:=inverse_price D m positive lower
  have wind:=inverse_price d m positive lowerWindow
  have difference : N/D-n/d=(N-n)*D⁻¹+n*(d-D)*D⁻¹*d⁻¹ := by
    field_simp [inv.1,wind.1]
    ring
  have ep : 0 ≤ EN := (norm_nonneg _).trans errorN
  have ed : 0 ≤ ED := (norm_nonneg _).trans errorD
  rw [difference]
  calc
    _ ≤ ‖N-n‖*‖D⁻¹‖+‖n‖*‖d-D‖*‖D⁻¹‖*‖d⁻¹‖ := by simpa only [norm_mul] using norm_add_le ((N-n)*D⁻¹) (n*(d-D)*D⁻¹*d⁻¹)
    _ ≤ EN*(1/m)+‖n‖*ED*(1/m)*(1/m) := by
      have err : ‖d-D‖ ≤ ED := by rw [norm_sub_rev]; exact errorD
      exact add_le_add (mul_le_mul errorN inv.2 (norm_nonneg _) ep)
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left err (norm_nonneg n)) inv.2
          (norm_nonneg _) (mul_nonneg (norm_nonneg n) ed)) wind.2
          (norm_nonneg _) (by positivity))
    _ = _ := by field_simp

def sourceEMBinaryRead (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (mu nu : Fin 4) : ℂ :=
  sourceEMNumeratorWindow event eps sigma n bits mu nu/(sourceStaticClearedWindow event eps sigma n bits).det

def sourceEMBinaryReadError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (mu nu : Fin 4) : ℝ :=
  (sourceEMNumeratorError event eps sigma n bits mu nu+
    ‖sourceEMNumeratorWindow event eps sigma n bits mu nu‖*sourceClearedDeterminantError event eps sigma n bits 289/
      sourceCommonDeterminantMargin event eps sigma n bits)/sourceCommonDeterminantMargin event eps sigma n bits

attribute [local irreducible] commonClearedPencil commonDeterminant commonEMTensorNumerator correctedEMTensor correctedDet
  sourceStaticClearedWindow sourceEMNumeratorWindow sourceEMNumeratorError sourceEMBinaryRead sourceEMBinaryReadError

private theorem source_window_lower (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) :
    sourceCommonDeterminantMargin event eps sigma n bits ≤ ‖(sourceStaticClearedWindow event eps sigma n bits).det‖ := by
  have nonnegative : 0 ≤ sourceClearedDeterminantError event eps sigma n bits 289 :=
    (norm_nonneg _).trans (actual_source_symbolic_denominator_error event eps sigma n positive small bits)
  unfold sourceCommonDeterminantMargin
  linarith

theorem actual_source_binary_regular_inverse (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ)
    (paid : 0 < sourceCommonDeterminantMargin event eps sigma n bits) :
    correctedDet event eps 0 sigma n≠0 ∧
      ‖(MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n))⁻¹‖ ≤
        1/sourceCommonDeterminantMargin event eps sigma n bits := by
  have inv:=inverse_price _ _ paid (actual_source_denominator_lower event eps sigma n positive small bits)
  exact ⟨actual_common_chart_original event eps sigma 0 n positive inv.1,inv.2⟩

theorem actual_source_EM16_binary_read_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ)
    (paid : 0 < sourceCommonDeterminantMargin event eps sigma n bits) (mu nu : Fin 4) :
    ‖correctedEMTensor event eps 0 sigma n mu nu-sourceEMBinaryRead event eps sigma n bits mu nu‖ ≤
      sourceEMBinaryReadError event eps sigma n bits mu nu := by
  have regular:=(actual_source_binary_regular_inverse event eps sigma n positive small bits paid).1
  have clear:=congrFun (congrFun (actual_corrected_em_tensor_clear event eps sigma 0 n positive regular) mu) nu
  have lower:=actual_source_denominator_lower event eps sigma n positive small bits
  have nonzero:=(inverse_price _ _ paid lower).1
  have read : correctedEMTensor event eps 0 sigma n mu nu=
      MvPolynomial.eval (irValues eps sigma 0) (commonEMTensorNumerator event n mu nu)/
        MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n) := by
    apply (eq_div_iff nonzero).mpr
    simpa only [Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,mul_comm] using clear
  rw [read]
  unfold sourceEMBinaryRead sourceEMBinaryReadError
  exact quotient_error _ _ _ _ _ _ _ paid lower (source_window_lower event eps sigma n positive small bits)
    (actual_source_EM16_numerator_error event eps sigma n positive small bits mu nu)
    (actual_source_symbolic_denominator_error event eps sigma n positive small bits)

def sourceFullGreenNumeratorWindow (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (i j : Fin 289) : ℂ :=
  sourceStaticCommonDenominator event eps sigma n*(sourceStaticClearedWindow event eps sigma n bits).adjugate i j

def sourceFullGreenNumeratorError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) : ℝ :=
  ‖sourceStaticCommonDenominator event eps sigma n‖*sourceClearedDeterminantError event eps sigma n bits 288

def sourceFullGreenBinaryRead (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (i j : Fin 289) : ℂ :=
  sourceFullGreenNumeratorWindow event eps sigma n bits i j/(sourceStaticClearedWindow event eps sigma n bits).det

def sourceFullGreenBinaryError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (i j : Fin 289) : ℝ :=
  (sourceFullGreenNumeratorError event eps sigma n bits+
    ‖sourceFullGreenNumeratorWindow event eps sigma n bits i j‖*sourceClearedDeterminantError event eps sigma n bits 289/
      sourceCommonDeterminantMargin event eps sigma n bits)/sourceCommonDeterminantMargin event eps sigma n bits

attribute [local irreducible] correctedGreen sourceFullGreenNumeratorWindow sourceFullGreenNumeratorError
  sourceFullGreenBinaryRead sourceFullGreenBinaryError

theorem actual_source_full289_green_binary_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ)
    (paid : 0 < sourceCommonDeterminantMargin event eps sigma n bits) (i j : Fin 289) :
    ‖correctedGreen event eps 0 sigma n i j-sourceFullGreenBinaryRead event eps sigma n bits i j‖ ≤
      sourceFullGreenBinaryError event eps sigma n bits i j := by
  have regular:=(actual_source_binary_regular_inverse event eps sigma n positive small bits paid).1
  have clear:=congrFun (congrFun (actual_common_green_adjugate event eps sigma 0 n positive regular) i) j
  have lower:=actual_source_denominator_lower event eps sigma n positive small bits
  have nonzero:=(inverse_price _ _ paid lower).1
  have read : correctedGreen event eps 0 sigma n i j=
      (sourceStaticCommonDenominator event eps sigma n*
        ((GaussComposite.ActualDressedUniformMaterialCoefficients.commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0))).adjugate i j)/
        MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n) := by
    apply (eq_div_iff nonzero).mpr
    unfold sourceStaticCommonDenominator
    simpa only [Matrix.smul_apply,smul_eq_mul,mul_comm] using clear
  have numerator : ‖sourceStaticCommonDenominator event eps sigma n*
        ((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma 0))).adjugate i j-
      sourceFullGreenNumeratorWindow event eps sigma n bits i j‖ ≤ sourceFullGreenNumeratorError event eps sigma n bits := by
    unfold sourceFullGreenNumeratorWindow sourceFullGreenNumeratorError
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (actual_source_adjugate_entry_error event eps sigma n positive small bits i j) (norm_nonneg _)
  rw [read]
  unfold sourceFullGreenBinaryRead sourceFullGreenBinaryError
  exact quotient_error _ _ _ _ _ _ _ paid lower (source_window_lower event eps sigma n positive small bits) numerator
    (actual_source_symbolic_denominator_error event eps sigma n positive small bits)

/-- The source window and its proven error decide the chart; no external price or lower bound is supplied. -/
inductive SourceEMBinaryReturn (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) : Type
  | unresolved (source_margin : sourceCommonDeterminantMargin event eps sigma n bits ≤ 0)
  | enclosed (source_margin : 0 < sourceCommonDeterminantMargin event eps sigma n bits)
      (original_regular : correctedDet event eps 0 sigma n≠0)
      (inverse_price : ‖(MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n))⁻¹‖ ≤
        1/sourceCommonDeterminantMargin event eps sigma n bits)
      (all289 : ∀ i j,‖correctedGreen event eps 0 sigma n i j-sourceFullGreenBinaryRead event eps sigma n bits i j‖ ≤
        sourceFullGreenBinaryError event eps sigma n bits i j)
      (all16 : ∀ mu nu,‖correctedEMTensor event eps 0 sigma n mu nu-sourceEMBinaryRead event eps sigma n bits mu nu‖ ≤
        sourceEMBinaryReadError event eps sigma n bits mu nu)

def sourceEMBinaryReturn (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) : SourceEMBinaryReturn event eps sigma n bits := by
  classical
  by_cases paid : 0 < sourceCommonDeterminantMargin event eps sigma n bits
  · have regular:=actual_source_binary_regular_inverse event eps sigma n positive small bits paid
    exact .enclosed paid regular.1 regular.2 (actual_source_full289_green_binary_error event eps sigma n positive small bits paid) (actual_source_EM16_binary_read_error event eps sigma n positive small bits paid)
  · exact .unresolved (le_of_not_gt paid)

end LowEnergy.ActualSourceQuantumCoefficientErrorOwn
