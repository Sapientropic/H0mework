import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.TwinFullRaw

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance pairedRawComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


def actualOriginalFourierRWholeRaw (h : ℝ) : ℝ → ℂ :=
  burnolTateReciprocalRaw (actualTateFourierRWholeRaw observation nontrivial half h)

theorem actual_original_F_R_full_source_raw (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (fourierL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h)) : ℝ → ℂ) =ᵐ[volume]
      actualOriginalFourierRWholeRaw observation nontrivial half h := by
  rw [actual_original_F_R_source]
  have source := actual_tate_fourier_R_full_source_raw observation nontrivial half h nonnegative bounded
  have actualRaw : MemLp (actualTateFourierRWholeRaw observation nontrivial half h) 2 volume :=
    (Lp.memLp (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualTateFourierSourceMaterial observation nontrivial half h))).ae_eq source
  exact (burnolTateReciprocalL2_coeFn _).trans
    (burnolTateReciprocalRaw_ae_congr (Lp.memLp _) actualRaw source)

def actualOriginalPairedRWholeRaw (h x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (actualOriginalRWholeRaw observation nontrivial half h x +
    actualOriginalFourierRWholeRaw observation nontrivial half h x)
def actualOriginalSiblingRWholeRaw (h x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (actualOriginalRWholeRaw observation nontrivial half h x -
    actualOriginalFourierRWholeRaw observation nontrivial half h x)

/-- The two original R directions are dependent faces of the same generated whole raw material. -/
theorem actual_original_pair_sibling_full_source_raw (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h : ℝ → ℂ) =ᵐ[volume]
      actualOriginalPairedRWholeRaw observation nontrivial half h ∧
    (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h : ℝ → ℂ) =ᵐ[volume]
      actualOriginalSiblingRWholeRaw observation nontrivial half h := by
  let acted := OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (actualSourceMaterial observation nontrivial half h)
  have original := actual_original_R_full_source_raw observation nontrivial half h nonnegative bounded
  have fourier := actual_original_F_R_full_source_raw observation nontrivial half h nonnegative bounded
  have sumRead := Lp.coeFn_add acted (fourierL2 acted)
  have differenceRead := Lp.coeFn_sub acted (fourierL2 acted)
  constructor
  · filter_upwards [original, fourier, sumRead, Lp.coeFn_smul (1 / 2 : ℂ) (acted+fourierL2 acted)]
      with x originalAt fourierAt added scaled
    change ((1 / 2 : ℂ) • (acted+fourierL2 acted) : BurnolL2) x = _
    rw [scaled]
    change (1 / 2 : ℂ) * (acted+fourierL2 acted : BurnolL2) x = _
    rw [added]
    change (1 / 2 : ℂ) * (acted x + fourierL2 acted x) = _
    rw [originalAt, fourierAt]
    rfl
  · filter_upwards [original, fourier, differenceRead, Lp.coeFn_smul (1 / 2 : ℂ) (acted-fourierL2 acted)]
      with x originalAt fourierAt difference scaled
    change ((1 / 2 : ℂ) • (acted-fourierL2 acted) : BurnolL2) x = _
    rw [scaled]
    change (1 / 2 : ℂ) * (acted-fourierL2 acted : BurnolL2) x = _
    rw [difference]
    change (1 / 2 : ℂ) * (acted x - fourierL2 acted x) = _
    rw [originalAt, fourierAt]
    rfl


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
