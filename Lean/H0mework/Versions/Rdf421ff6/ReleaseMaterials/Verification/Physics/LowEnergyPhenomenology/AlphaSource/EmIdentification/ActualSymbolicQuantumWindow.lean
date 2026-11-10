import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMBinaryReadReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceQuantumCoefficientErrorOwn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet
open GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualDressedSylvester
open GaussComposite.ActualDressedFrequencyHalf GaussComposite.ActualDressedUniformMaterialCoefficients
open GaussComposite.ActualDressedEMTensorClock ActualMixedNoetherTimePriceOwn
open scoped BigOperators Matrix

private theorem static_pi_source (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) :
    frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps 0 n)
      (dampedFourierClock (sourceFrequency eps 0) sigma)=dressedStaticPolarization event ((eps^2 : ℝ) • n) (sigma : ℂ) := by
  have clock : dampedFourierClock (sourceFrequency eps 0) sigma=(sigma : ℂ) := by
    simp [dampedFourierClock,sourceFrequency]
  rw [clock]
  funext i j
  unfold frequencyHalfPolarization
  exact dressed_static_polarization_actual event ((eps^2 : ℝ) • n)
    (frequencyRay eps 0 n) (by simp [frequencyRay,physicalFrequencyMomentum]) (sigma : ℂ) positive i j

def sourceSymbolicQuantumWindow (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  sourceStaticCommonDenominator event eps sigma n • originalQuantumBinaryWindow event ((eps^2 : ℝ) • n) (sigma : ℂ) bits

def sourceSymbolicQuantumError (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (i j : Fin 289) : ℝ :=
  ‖sourceStaticCommonDenominator event eps sigma n‖*
    ((896*sourceCompleteCubicNoetherPrice event ((eps^2 : ℝ) • n) (fieldUnit i) (fieldUnit j)/sigma^4)*(1/2 : ℝ)^bits)

attribute [local irreducible] dressedStaticPolarization frequencyHalfPolarization commonNumerator commonDenominator
  sourceStaticCommonDenominator sourceSymbolicQuantumWindow originalQuantumBinaryWindow

theorem actual_source_symbolicN_binary_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) (i j : Fin 289) :
    ‖(commonNumerator event n).map (MvPolynomial.eval (irValues eps sigma 0)) i j-
      sourceSymbolicQuantumWindow event eps sigma n bits i j‖ ≤ sourceSymbolicQuantumError event eps sigma n bits i j := by
  have clear:=actual_common_ir_pi_clear event n eps sigma 0 positive
  rw [static_pi_source event eps sigma n positive] at clear
  rw [←clear]
  unfold sourceSymbolicQuantumWindow sourceSymbolicQuantumError sourceStaticCommonDenominator
  simp only [Matrix.smul_apply,smul_eq_mul,←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (actualFullQuantum_binary_source_error event ((eps^2 : ℝ) • n)
    (sigma : ℂ) positive small bits i j) (norm_nonneg _)

theorem actual_static_polynomial_denominator_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) :
    ‖(staticEMDeterminant event sigma n).eval (eps : ℂ)-(sourceStaticClearedWindow event eps sigma n bits).det‖ ≤
      sourceClearedDeterminantError event eps sigma n bits 289 := by
  rw [staticEMDeterminant,static_scale_eval]
  exact actual_source_symbolic_denominator_error event eps sigma n positive small bits

theorem actual_static_polynomial_EM16_numerator_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ) (mu nu : Fin 4) :
    ‖(staticEMNumerator event sigma n mu nu).eval (eps : ℂ)-sourceEMNumeratorWindow event eps sigma n bits mu nu‖ ≤
      sourceEMNumeratorError event eps sigma n bits mu nu := by
  change ‖(staticScaleSlice sigma (commonEMTensorNumerator event n mu nu)).eval (eps : ℂ)-_‖ ≤ _
  rw [static_scale_eval]
  exact actual_source_EM16_numerator_error event eps sigma n positive small bits mu nu

-- The light tensor is the unchanged original complete-photon Green read.
def sourceFullLightBinaryRead (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum) (bits : ℕ)
    (mu nu : Fin 4) : ℂ :=
  sourceEMBinaryRead event eps sigma n bits mu nu-GaussComposite.ActualEMCarrierOwn.emPropagator eps 0 n mu nu

attribute [local irreducible] GaussComposite.ActualEMCarrierOwn.emPropagator sourceFullLightBinaryRead
  sourceEMBinaryRead GaussComposite.ActualDressedEMTensorClock.correctedEMTensor

theorem actual_source_full_light_binary_error (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ)
    (paid : 0 < sourceCommonDeterminantMargin event eps sigma n bits) (mu nu : Fin 4) :
    ‖(correctedEMTensor event eps 0 sigma n mu nu-GaussComposite.ActualEMCarrierOwn.emPropagator eps 0 n mu nu)-
      sourceFullLightBinaryRead event eps sigma n bits mu nu‖ ≤ sourceEMBinaryReadError event eps sigma n bits mu nu := by
  unfold sourceFullLightBinaryRead
  rw [sub_sub_sub_cancel_right]
  exact actual_source_EM16_binary_read_error event eps sigma n positive small bits paid mu nu

theorem actual_source_full_light_binary_complex_enclosure (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0 < sigma) (small : sigma ≤ 2) (bits : ℕ)
    (paid : 0 < sourceCommonDeterminantMargin event eps sigma n bits) (mu nu : Fin 4) :
    |(correctedEMTensor event eps 0 sigma n mu nu-GaussComposite.ActualEMCarrierOwn.emPropagator eps 0 n mu nu).re-
      (sourceFullLightBinaryRead event eps sigma n bits mu nu).re| ≤ sourceEMBinaryReadError event eps sigma n bits mu nu ∧
    |(correctedEMTensor event eps 0 sigma n mu nu-GaussComposite.ActualEMCarrierOwn.emPropagator eps 0 n mu nu).im-
      (sourceFullLightBinaryRead event eps sigma n bits mu nu).im| ≤ sourceEMBinaryReadError event eps sigma n bits mu nu := by
  have paidError:=actual_source_full_light_binary_error event eps sigma n positive small bits paid mu nu
  constructor
  · exact (Complex.abs_re_le_norm _).trans paidError
  · exact (Complex.abs_im_le_norm _).trans paidError

end LowEnergy.ActualSourceQuantumCoefficientErrorOwn
