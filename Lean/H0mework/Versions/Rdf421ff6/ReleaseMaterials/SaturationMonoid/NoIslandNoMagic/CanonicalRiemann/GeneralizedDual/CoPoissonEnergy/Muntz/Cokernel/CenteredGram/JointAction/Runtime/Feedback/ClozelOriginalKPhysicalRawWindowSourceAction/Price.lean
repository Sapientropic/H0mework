import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalRawWindowSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance priceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "radius" t => ((1/4:ℝ)*Real.exp t)
open OriginalKWholePaSourceRankAction OriginalKQBSourceWindowAction OriginalKExpandedCompleteWindowSourceAction
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- A source programme from the original whole R profile and both inverse quarter corrections, before any cotest. -/
def actualPhysicalRawSourceProgramme (value : BurnolL2) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  burnolEvenRaw raw x -
    (1/2:ℂ) * ((symmetricInterval (1/4:ℝ)).indicator (burnolFirstCorrectionRaw value raw) x +
      (symmetricInterval (1/4:ℝ)).indicator (burnolFirstCorrectionRaw value raw) (-x) +
      burnolRadiusTruncatedFourierRaw (1/4:ℝ) (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2) x +
      burnolRadiusTruncatedFourierRaw (1/4:ℝ) (burnolAmbientMeanZeroSecondCorrection value : BurnolQuarterIntervalL2) (-x))

theorem actual_original_raw_source_programme (h x : ℝ) :
    OriginalKPhysicalWindowSourceAction.actualPhysicalPairedRaw observation nontrivial half h x =
      actualPhysicalRawSourceProgramme (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
        (OriginalKPhysicalWindowSourceAction.actualOriginalPairedRWholeRaw observation nontrivial half h) x ∧
    OriginalKPhysicalWindowSourceAction.actualPhysicalSiblingRaw observation nontrivial half h x =
      actualPhysicalRawSourceProgramme (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)
        (OriginalKPhysicalWindowSourceAction.actualOriginalSiblingRWholeRaw observation nontrivial half h) x := by
  constructor
  · unfold OriginalKPhysicalWindowSourceAction.actualPhysicalPairedRaw
      burnolEvenProjectionRaw actualPhysicalRawSourceProgramme burnolEvenRaw burnolRawCorrectionRaw
    ring
  · unfold OriginalKPhysicalWindowSourceAction.actualPhysicalSiblingRaw
      burnolEvenProjectionRaw actualPhysicalRawSourceProgramme burnolEvenRaw burnolRawCorrectionRaw
    ring

def actualPairPhysicalRawWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  ∫ x : ℝ, star (actualPhysicalRawSourceProgramme (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
    (OriginalKPhysicalWindowSourceAction.actualOriginalPairedRWholeRaw observation nontrivial half h) x) *
    actualExpandedQuarterWeight source t x ∂volume.restrict (symmetricInterval (radius t))
def actualSiblingPhysicalRawWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  ∫ x : ℝ, star (actualPhysicalRawSourceProgramme (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)
    (OriginalKPhysicalWindowSourceAction.actualOriginalSiblingRWholeRaw observation nontrivial half h) x) *
    actualExpandedQuarterWeight source t x ∂volume.restrict (symmetricInterval (radius t))

/-- The exact R raw and both correction feet pay the full physical weighted field read through the source-qualified vector. -/
theorem actual_physical_raw_weighted_source_fees (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (source : BurnolQuarterIntervalL2) (t : ℝ) :
    inner ℂ (actualPhysicalPairRawWindow observation nontrivial half h nonnegative bounded t) (actualExpandedQuarterWeight source t) =
      actualPairPhysicalRawWeightedFee observation nontrivial half h source t ∧
    inner ℂ (actualPhysicalSiblingRawWindow observation nontrivial half h nonnegative bounded t) (actualExpandedQuarterWeight source t) =
      actualSiblingPhysicalRawWeightedFee observation nontrivial half h source t := by
  constructor
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp ((actual_physical_source_raw_qualified observation nontrivial half h nonnegative bounded).1.restrict
      (symmetricInterval (radius t)))] with x raw
    change (actualPhysicalPairRawWindow observation nontrivial half h nonnegative bounded t) x =
      OriginalKPhysicalWindowSourceAction.actualPhysicalPairedRaw observation nontrivial half h x at raw
    rw [raw, (actual_original_raw_source_programme observation nontrivial half h x).1]
    simp only [RCLike.inner_apply,starRingEnd_apply]
    ring
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp ((actual_physical_source_raw_qualified observation nontrivial half h nonnegative bounded).2.restrict
      (symmetricInterval (radius t)))] with x raw
    change (actualPhysicalSiblingRawWindow observation nontrivial half h nonnegative bounded t) x =
      OriginalKPhysicalWindowSourceAction.actualPhysicalSiblingRaw observation nontrivial half h x at raw
    rw [raw, (actual_original_raw_source_programme observation nontrivial half h x).2]
    simp only [RCLike.inner_apply,starRingEnd_apply]
    ring

def actualPairRawSourceWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  actualPairPhysicalRawWeightedFee observation nontrivial half h source t -
    inner ℂ (paSourceWindowProgramme (actualFullPairPaSource observation nontrivial half h) t) (actualExpandedQuarterWeight source t) -
    star (actualWholePaSourceCoefficient observation nontrivial half h/2) *
      inner ℂ (actualUnitPairWindowProgramme observation nontrivial half t) (actualExpandedQuarterWeight source t)
def actualSiblingRawSourceWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  actualSiblingPhysicalRawWeightedFee observation nontrivial half h source t -
    inner ℂ (paSourceWindowProgramme (actualFullSiblingPaSource observation nontrivial half h) t) (actualExpandedQuarterWeight source t) -
    star (actualWholePaSourceCoefficient observation nontrivial half h/2) *
      inner ℂ (actualUnitSiblingWindowProgramme observation nontrivial half t) (actualExpandedQuarterWeight source t)

theorem actual_raw_source_weighted_complete_fees (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (source : BurnolQuarterIntervalL2) (t : ℝ) :
    actualPairWindowSourceCotest observation nontrivial half h source t = actualPairRawSourceWeightedFee observation nontrivial half h source t ∧
    actualSiblingWindowSourceCotest observation nontrivial half h source t = actualSiblingRawSourceWeightedFee observation nontrivial half h source t := by
  have generated := actual_raw_source_window_weighted_effect observation nontrivial half h nonnegative bounded source t
  have raw := actual_physical_raw_weighted_source_fees observation nontrivial half h nonnegative bounded source t
  constructor
  · rw [generated.1]
    unfold actualPairRawSourceCotest actualPairRawSourceWindow actualPairRawSourceWeightedFee
    rw [inner_sub_left,inner_sub_left,inner_smul_left,raw.1]
    rfl
  · rw [generated.2]
    unfold actualSiblingRawSourceCotest actualSiblingRawSourceWindow actualSiblingRawSourceWeightedFee
    rw [inner_sub_left,inner_sub_left,inner_smul_left,raw.2]
    rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
