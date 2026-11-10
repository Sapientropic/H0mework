import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTwoClockNumerator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalRayNumerator
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedFrequencyHalf ActualEMAction
open PreparationVacuumOriginalGreenFeedback
open scoped Matrix BigOperators Topology
attribute [local irreducible] dressedKinematicPoint dampedFourierClock frequencyResponsePencil
  frequencyHalfPolarization emOriginalJacobi twoClockDenominator twoClockNumerator

def physicalRayDenominator (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  twoClockDenominator (dressedKinematicPoint event ((e^2:ℝ) • n))
    (dampedFourierClock (sourceFrequency e s) sigma) (sigma:ℂ)

def physicalRayNumerator (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  twoClockNumerator event ((e^2:ℝ) • n) (dampedFourierClock (sourceFrequency e s) sigma) (sigma:ℂ)

/-- The complete actual corrected matrix, without invoking an old-action Green chart. -/
def physicalRayClearedPencil (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  physicalRayDenominator event e s sigma n • emOriginalJacobi (frequencyRay e s n)-
    (sigma:ℂ) • physicalRayNumerator event e s sigma n

attribute [local irreducible] physicalRayDenominator physicalRayNumerator physicalRayClearedPencil

theorem physical_ray_denominator_nonzero (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) : physicalRayDenominator event e s sigma n≠0 := by
  have damped : 0<(dampedFourierClock (sourceFrequency e s) sigma).re := by
    simpa only [dampedFourierClock,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] using positive
  unfold physicalRayDenominator
  exact two_clock_denominator_nonzero (dressedKinematicPoint event ((e^2:ℝ) • n))
    (dampedFourierClock (sourceFrequency e s) sigma) (sigma:ℂ) damped positive

private theorem physical_ray_half_clear (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    physicalRayDenominator event e s sigma n •
      frequencyHalfPolarization event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)=physicalRayNumerator event e s sigma n := by
  have frequency : sourceFrequency e s=s*e^2 := by unfold sourceFrequency;ring
  simpa only [frequency,frequencyRay,physicalRayDenominator,physicalRayNumerator] using
    actual_two_clock_clear event ((e^2:ℝ) • n) (sourceFrequency e s) sigma ((e^2:ℝ) • n) positive

/-- Both clocks, all 289 fields and the same physical momentum enter one source-generated numerator. -/
theorem actual_physical_ray_pencil_clear (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    physicalRayDenominator event e s sigma n •
      frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)=physicalRayClearedPencil event e s sigma n := by
  rw [damped_source_sheet_response event e s sigma n positive,physicalRayClearedPencil,smul_sub]
  have clear:=physical_ray_half_clear event e s sigma n positive
  congr 1
  rw [smul_comm,clear]

/-- Clearing changes no actual full solution or its nine source constraint rows. -/
theorem actual_physical_ray_equation_iff (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (forcing a : Fin 289→ℂ) :
    frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
      (dampedFourierClock (sourceFrequency e s) sigma)*ᵥa=forcing ↔
      physicalRayClearedPencil event e s sigma n*ᵥa=
        physicalRayDenominator event e s sigma n • forcing := by
  rw [←actual_physical_ray_pencil_clear event e s sigma n positive,Matrix.smul_mulVec]
  exact (smul_right_injective _ (physical_ray_denominator_nonzero event e s sigma n positive)).eq_iff.symm

end LowEnergy.GaussComposite.ActualDressedPhysicalRayNumerator
