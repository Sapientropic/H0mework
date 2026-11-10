import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroDampingReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroDamping
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualCompositeFieldCurrent ActualEMResponseSplit ActualEMCurrentSplit
open scoped Matrix BigOperators

private theorem principal_at_source_chart (N D : ℂ[X]) (sigma : ℝ) (positive : 0<sigma)
    (chart : D.eval (sigma : ℂ)≠0) (order : 0<poleOrder (readFraction N D) 0) :
    let R := readFraction N D
    R.num.eval (sigma : ℂ)/R.denom.eval (sigma : ℂ)=
      (∑ k ∈ Finset.range (poleOrder R 0), principalCoefficient R 0 k*(sigma : ℂ)^k/(sigma : ℂ)^poleOrder R 0)+
        (analyticNumerator R 0).eval (sigma : ℂ)/(rootRemainder R 0).eval (sigma : ℂ) := by
  dsimp only
  let R := readFraction N D
  have reduced := reduced_denominator_at_regular N D (sigma : ℂ) chart
  have remainder : (rootRemainder R 0).eval (sigma : ℂ)≠0 := by
    intro zero
    have factor := congrArg (Polynomial.eval (sigma : ℂ)) (denominator_root_factor R 0)
    simp only [eval_mul, zero, mul_zero] at factor
    exact reduced factor.symm
  have away : (sigma : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt positive)
  have root : 0∈visibleRoots R := (visible_root_iff R 0).mpr
    ((rootMultiplicity_pos (RatFunc.denom_ne_zero R)).mp order)
  have complete := complete_principal_part R 0 (sigma : ℂ) away remainder
  rw [principal_negative_powers R 0 (sigma : ℂ) root] at complete
  simpa only [sub_zero] using complete

/-- No damping principal term is removed by an EM projection or by a scalar detector. -/
theorem actual_damping_em_principal (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (chart : (dampingDeterminant event eps n).eval (sigma : ℂ)≠0)
    (mu nu : Fin 4) (order : 0<poleOrder (dampingEMFraction event eps n mu nu) 0) :
    let R := dampingEMFraction event eps n mu nu
    correctedEMTensor event eps 0 sigma n mu nu=
      (∑ k ∈ Finset.range (poleOrder R 0), principalCoefficient R 0 k*(sigma : ℂ)^k/(sigma : ℂ)^poleOrder R 0)+
        (analyticNumerator R 0).eval (sigma : ℂ)/(rootRemainder R 0).eval (sigma : ℂ) := by
  exact (actual_damping_em_fraction event eps sigma n positive chart mu nu).trans
    (principal_at_source_chart _ _ sigma positive chart order)

theorem actual_damping_probe_principal (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (positive : 0<sigma) (chart : (dampingDeterminant event eps n).eval (sigma : ℂ)≠0)
    (order : 0<poleOrder (dampingProbeFraction event eps n pd ps dL dR sL sR) 0) :
    let R := dampingProbeFraction event eps n pd ps dL dR sL sR
    correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR=
      (∑ k ∈ Finset.range (poleOrder R 0), principalCoefficient R 0 k*(sigma : ℂ)^k/(sigma : ℂ)^poleOrder R 0)+
        (analyticNumerator R 0).eval (sigma : ℂ)/(rootRemainder R 0).eval (sigma : ℂ) := by
  exact (actual_damping_probe_fraction event eps sigma n pd ps dL dR sL sR positive chart).trans
    (principal_at_source_chart _ _ sigma positive chart order)

/-- The canonical damping fraction observes the unchanged complete four-piece electron read. -/
theorem actual_damping_probe_four_parts (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (positive : 0<sigma) (chart : (dampingDeterminant event eps n).eval (sigma : ℂ)≠0) :
    let R := dampingProbeFraction event eps n pd ps dL dR sL sR
    let G := correctedGreen event eps 0 sigma n
    let fd := ActualCompositeFieldCurrent.compositeCurrent pd dL dR
    let fs := ActualCompositeFieldCurrent.compositeCurrent ps sL sR
    R.num.eval (sigma : ℂ)/R.denom.eval (sigma : ℂ)=
      dotProduct (emCoordinateCurrent fd) (correctedEMTensor event eps 0 sigma n*ᵥemCoordinateCurrent fs)+
      emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
      emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs) :=
  (actual_damping_probe_fraction event eps sigma n pd ps dL dR sL sR positive chart).symm.trans
    (actual_probe_tensor_four_parts event eps sigma 0 n pd ps dL dR sL sR)

end LowEnergy.GaussComposite.ActualDressedZeroDamping
