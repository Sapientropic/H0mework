import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKFullAdjointSource OriginalKForcingGapAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local instance gapPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance gapQuarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "S" => burnolMeanZeroTruncatedFourier

private theorem inverseFourier_original (coordinate : BurnolCompletedMellinCoordinate) :
    fourierL2.symm (burnolCompletedMellinRieszVector coordinate : BurnolL2)=
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompletedMellinRieszVector coordinate) : BurnolL2) := by
  apply fourierL2.injective
  rw [fourierL2.apply_symm_apply]
  exact (congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2))
    (evenFaceFourier_involutive burnolUnscaledCommonGapRadius
      (burnolCompletedMellinRieszVector coordinate))).symm

/-- Full-L2 Fourier action places the source adjoint in the actual inward conjugate R fibre. -/
theorem inverseFourier_adjoint_source (coordinate : BurnolCompletedMellinCoordinate) :
    fourierL2.symm (sourceAdjointField coordinate)=
      burnolDirectRightResolvent (star coordinate.value/2)
        (fourierL2.symm (burnolCompletedMellinRieszVector coordinate : BurnolL2)) := by
  have right : 1/4<(star coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have actual := FiniteMobiusResolventFlux.fourier_R (star coordinate.value/2) right
    (fourierL2.symm (burnolCompletedMellinRieszVector coordinate : BurnolL2))
  rw [fourierL2.apply_symm_apply] at actual
  change fourierL2 (burnolDirectRightResolvent (star coordinate.value/2)
    (fourierL2.symm (burnolCompletedMellinRieszVector coordinate : BurnolL2)))=
      sourceAdjoint coordinate (burnolCompletedMellinRieszVector coordinate : BurnolL2) at actual
  rw [sourceAdjoint_original] at actual
  exact (congrArg fourierL2.symm actual).symm.trans (fourierL2.symm_apply_apply _)

/-- The original Fourier gap and the paid inward resolvent action generate a zero mean-zero cotest. -/
theorem adjoint_inverseFourier_quarterCotest_zero (coordinate : BurnolCompletedMellinCoordinate) :
    quarterCotest (fourierL2.symm (sourceAdjointField coordinate))=0 := by
  let value := fourierL2.symm (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  let mu := burnolQuarterMeanCoefficient (burnolQuarterRestriction value)
  have qualified : burnolQuarterRestriction value∈intervalConstantLine (1/4 : ℝ) := by
    dsimp only [value]
    rw [inverseFourier_original]
    exact (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompletedMellinRieszVector coordinate)).property.1.1
  have centered := (burnolQuarterMeanZeroProjection_eq_zero_iff (burnolQuarterRestriction value)).mpr qualified
  rw [burnolMeanZeroProjection_eq_sub_constant] at centered
  have gap : burnolQuarterRestriction value=mu • intervalConstant (1/4 : ℝ) := sub_eq_zero.mp centered
  have right : 1/4<(star coordinate.value/2).re := by
    rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have acted := right_resolvent_quarter_constant (star coordinate.value/2) right value mu gap
  apply Subtype.ext
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (fourierL2.symm (sourceAdjointField coordinate)))=0
  rw [inverseFourier_adjoint_source]
  change burnolQuarterMeanZeroProjection (burnolQuarterRestriction
    (burnolDirectRightResolvent (star coordinate.value/2) value))=0
  rw [acted,map_smul]
  have constantZero : burnolQuarterMeanZeroProjection (intervalConstant (1/4 : ℝ))=0 :=
    (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)
  rw [constantZero,smul_zero]

theorem outsideCotest_from_position_source (coordinate : BurnolCompletedMellinCoordinate) :
    outsideCotest (sourceAdjointField coordinate)=-(S).adjoint (quarterCotest (sourceAdjointField coordinate)) := by
  rw [outsideCotest,adjoint_inverseFourier_quarterCotest_zero,zero_sub]

/-- The complete source price has one actual S channel; its other cotest is generated zero by inward R. -/
theorem outside_price_from_position_source (coordinate : BurnolCompletedMellinCoordinate)
    (state : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (outsideCotest (sourceAdjointField coordinate)) state=
      -inner ℂ (quarterCotest (sourceAdjointField coordinate)) (S state) := by
  rw [outsideCotest_from_position_source,inner_neg_left,ContinuousLinearMap.adjoint_inner_left]

/-- The original Q successor consumes the Pa/Q source and the computed one-channel outside price. -/
theorem actual_nextQ_one_channel_source (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let coordinate := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
    let K := (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    inner ℂ K (PA.Q (D.raw observation nontrivial half depth ((ordinal+1)+1)) : BurnolL2)=
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)*
        inner ℂ K (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)+
      inner ℂ (qAdjointSource coordinate) (D.raw observation nontrivial half depth (ordinal+1))-
      inner ℂ (quarterCotest (sourceAdjointField coordinate))
        (S (sourceOutsideColumn coordinate (D.raw observation nontrivial half depth ordinal))) := by
  dsimp only
  have actual := actual_nextQ_complete_source observation nontrivial half depth ordinal
  dsimp only at actual
  rw [outside_price_from_position_source] at actual
  simpa only [sub_eq_add_neg] using actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
