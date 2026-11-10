import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhysicalRayPencil
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCorrectedGreen
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumCurrentSignalOperator
open ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedPhysicalRayNumerator
open scoped Matrix
attribute [local irreducible] physicalRayDenominator physicalRayNumerator physicalRayClearedPencil
  frequencyResponsePencil

def correctedDet (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  (physicalRayClearedPencil event e s sigma n).det

def correctedAdjugateNumerator (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  physicalRayDenominator event e s sigma n • (physicalRayClearedPencil event e s sigma n).adjugate

def correctedGreen (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  physicalRayDenominator event e s sigma n • (physicalRayClearedPencil event e s sigma n)⁻¹

attribute [local irreducible] correctedDet correctedAdjugateNumerator correctedGreen

theorem corrected_green_adjugate (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    correctedGreen event e s sigma n=
      (correctedDet event e s sigma n)⁻¹ • correctedAdjugateNumerator event e s sigma n := by
  unfold correctedGreen correctedDet correctedAdjugateNumerator
  rw [Matrix.inv_def,Ring.inverse_eq_inv']
  simp only [smul_smul,mul_comm]

theorem corrected_adjugate_generated (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    physicalRayClearedPencil event e s sigma n*correctedAdjugateNumerator event e s sigma n=
        (physicalRayDenominator event e s sigma n*correctedDet event e s sigma n) • 1 ∧
    correctedAdjugateNumerator event e s sigma n*physicalRayClearedPencil event e s sigma n=
        (physicalRayDenominator event e s sigma n*correctedDet event e s sigma n) • 1 := by
  unfold correctedAdjugateNumerator correctedDet
  constructor
  · rw [Matrix.mul_smul,Matrix.mul_adjugate,smul_smul]
  · rw [Matrix.smul_mul,Matrix.adjugate_mul,smul_smul]

private theorem cleared_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P H : Matrix ι ι ℂ) (d : ℂ) (nonzero : d≠0) (clear : d • P=H) (regular : H.det≠0) :
    P*(d • H⁻¹)=1 ∧ (d • H⁻¹)*P=1 := by
  have unit : IsUnit H.det := isUnit_iff_ne_zero.mpr regular
  have recovered : P=d⁻¹ • H := by rw [←clear,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  rw [recovered]
  constructor
  · rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
    exact Matrix.mul_nonsing_inv H unit
  · rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
    exact Matrix.nonsing_inv_mul H unit

/-- The canonical same-event Green inverts the complete actual response on its source determinant region. -/
theorem actual_corrected_green_inverse (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (regular : correctedDet event e s sigma n≠0) :
    frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)*correctedGreen event e s sigma n=1 ∧
    correctedGreen event e s sigma n*frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)=1 := by
  unfold correctedGreen
  exact cleared_inverse _ _ _ (physical_ray_denominator_nonzero event e s sigma n positive)
    (actual_physical_ray_pencil_clear event e s sigma n positive)
    (by simpa only [correctedDet] using regular)

def correctedResponse (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (forcing : SignalAmplitude) : SignalAmplitude := correctedGreen event e s sigma n*ᵥforcing
attribute [local irreducible] correctedResponse

theorem actual_corrected_response_equation (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (regular : correctedDet event e s sigma n≠0) (forcing : SignalAmplitude) :
    frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
      (dampedFourierClock (sourceFrequency e s) sigma)*ᵥcorrectedResponse event e s sigma n forcing=forcing := by
  unfold correctedResponse
  rw [Matrix.mulVec_mulVec,(actual_corrected_green_inverse event e s sigma n positive regular).1,
    Matrix.one_mulVec]

theorem actual_corrected_full_solution (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (regular : correctedDet event e s sigma n≠0) (forcing a : SignalAmplitude) :
    frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
      (dampedFourierClock (sourceFrequency e s) sigma)*ᵥa=forcing ↔
        a=correctedResponse event e s sigma n forcing := by
  constructor
  · intro equation
    have restored:=congrArg (fun v=>correctedGreen event e s sigma n*ᵥv) equation
    rw [Matrix.mulVec_mulVec,(actual_corrected_green_inverse event e s sigma n positive regular).2,
      Matrix.one_mulVec] at restored
    simpa only [correctedResponse] using restored
  · rintro rfl
    exact actual_corrected_response_equation event e s sigma n positive regular forcing

theorem actual_corrected_response_cleared (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (regular : correctedDet event e s sigma n≠0) (forcing : SignalAmplitude) :
    physicalRayClearedPencil event e s sigma n*ᵥcorrectedResponse event e s sigma n forcing=
      physicalRayDenominator event e s sigma n • forcing :=
  (actual_physical_ray_equation_iff event e s sigma n positive forcing _).mp
    (actual_corrected_response_equation event e s sigma n positive regular forcing)

end LowEnergy.GaussComposite.ActualDressedCorrectedGreen
