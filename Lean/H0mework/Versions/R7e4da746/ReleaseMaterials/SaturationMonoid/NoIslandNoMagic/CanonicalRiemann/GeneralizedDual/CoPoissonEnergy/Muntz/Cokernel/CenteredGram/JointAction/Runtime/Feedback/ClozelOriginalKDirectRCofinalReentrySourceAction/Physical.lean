import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalReentrySourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace PA
export OriginalKCombCofinalPaAction (Q)
end PA
namespace P
export OriginalKCombPhysicalAction (physicalRemainder)
end P
namespace D
export OriginalKCombFirstFullSourceDynamics (input next_pair)
end D

/-- The outside-P source has no Pa projection before the original R action is read. -/
theorem outside_P_E_zero (value : BurnolL2) : PA.E (P.physicalRemainder value)=0 := by
 change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (burnolEvenAmbientProjection (P.physicalRemainder value))=0
 have physicalZero : burnolEvenAmbientProjection (P.physicalRemainder value)=0 :=
  Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
   (Submodule.starProjection_apply_mem _ _)
 rw [physicalZero,map_zero]

section OriginalZero
variable {owner : GlobalGermOwner}
variable (observation : GeneratedRiemannZeroObservationAt owner)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "coordinate" => burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
local notation "starCoordinate" => OriginalPrimitiveRankBalance.conjugateCoordinate coordinate
local notation "sourceUnit" => fourierL2 (burnolUnitTailResponse starCoordinate 4)
include nontrivial rightHalf

/-- The original zero-conjugation theorem supplies this mathematical parameter's original unit qualification. -/
theorem conjugate_unit_physical :
 burnolUnitTailResponse starCoordinate 4 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 let conjugateObservation := GeneratedRiemannZeroObservationAt.ofMathlibZero owner
  (starRingEnd ℂ observation.coordinate) observation.conjugate_mathlibZero
 have conjugateNontrivial : ¬∃ n:Nat,conjugateObservation.coordinate=-2*(n+1) :=
  observation.conjugate_nontrivial nontrivial
 have conjugateHalf : 1/2<conjugateObservation.coordinate.re := by
  change 1/2<(starRingEnd ℂ observation.coordinate).re
  simpa only [Complex.conj_re] using rightHalf
 exact burnolZeroOwnedUnitTailResponse_physical conjugateObservation conjugateNontrivial conjugateHalf

/-- Actual Fourier preserves the original physical P face of this specific source unit. -/
theorem conjugate_F_unit_physical :
 sourceUnit∈evenBurnolClosedFace burnolUnscaledCommonGapRadius :=
 (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  ⟨burnolUnitTailResponse starCoordinate 4,
   conjugate_unit_physical observation nontrivial rightHalf⟩).property

/-- The specific actual-zero source unit annihilates the complete outside-P channel. -/
theorem source_unit_outside_P_zero (value : BurnolL2) :
 inner ℂ sourceUnit (P.physicalRemainder value)=0 := by
 have member : P.physicalRemainder value∈
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ :=
  Submodule.starProjection_apply_mem _ _
 exact member sourceUnit (conjugate_F_unit_physical observation nontrivial rightHalf)

/-- In this actual-zero channel, the original full-invisible pairing is exactly its actual physical-Q pairing. -/
theorem source_unit_invisible_pair_Q (value : BurnolL2) :
 inner ℂ sourceUnit (PA.invisible value)=inner ℂ sourceUnit (PA.Q value : BurnolL2) := by
 let physical : BurnolPaAmbientCarrier :=
  ⟨sourceUnit,conjugate_F_unit_physical observation nontrivial rightHalf⟩
 have projected := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left physical value
 change inner ℂ sourceUnit (burnolEvenAmbientProjection value : BurnolL2)=
  inner ℂ sourceUnit value at projected
 have split := congrArg
  (fun state : BurnolPaAmbientCarrier => inner ℂ sourceUnit (state : BurnolL2))
  (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
   (burnolEvenAmbientProjection value))
 change inner ℂ sourceUnit ((PA.E value : BurnolPaAmbientCarrier)+(PA.Q value : BurnolPaAmbientCarrier) : BurnolL2)=
  inner ℂ sourceUnit (burnolEvenAmbientProjection value : BurnolL2) at split
 rw [inner_add_right] at split
 unfold PA.invisible
 rw [inner_sub_right,←projected,←split]
 abel

/-- Full-L2 source action proves the outside-P channel's actual Pa return vanishes. -/
theorem outside_P_R_E_zero (value : BurnolL2) :
 PA.E (burnolDirectRightResolvent (observation.coordinate/2) (P.physicalRemainder value))=0 := by
 have actual := full_pa_reentry_action coordinate (P.physicalRemainder value) (outside_P_E_zero value)
 change PA.E (burnolDirectRightResolvent (observation.coordinate/2) (P.physicalRemainder value))=
  inner ℂ sourceUnit (P.physicalRemainder value) •
   (sourceReentryVector coordinate : BurnolPaAmbientCarrier) at actual
 rw [source_unit_outside_P_zero observation nontrivial rightHalf,zero_smul] at actual
 exact actual
end OriginalZero

section ActualOriginalInput
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "coordinate" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "sourceUnit" => fourierL2 (burnolUnitTailResponse
 (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) 4)

/-- The same original current's beta now depends exactly on its generated Q source. -/
theorem actual_beta_Q :
 inner ℂ sourceUnit (PA.invisible (D.raw observation nontrivial half depth ordinal))=
 inner ℂ sourceUnit (PA.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2) :=
 source_unit_invisible_pair_Q observation nontrivial half.down _

/-- The actual next outside-P stock is retained, while this source pairing annihilates its Pa channel. -/
theorem actual_next_outside_pair_zero :
 inner ℂ sourceUnit (D.input observation nontrivial half depth (ordinal+1)).2=0 := by
 rw [D.next_pair]
 exact source_unit_outside_P_zero observation nontrivial half.down _

theorem actual_next_outside_reentry_zero :
 PA.E (P.R observation nontrivial half (D.input observation nontrivial half depth (ordinal+1)).2)=0 := by
 rw [D.next_pair,OriginalKCombCofinalRAction.original_R_direct]
 exact outside_P_R_E_zero observation nontrivial half.down _

/-- The actual full-vector re-entry is computed from Q after the full-L2 outside-P proof. -/
theorem actual_reentry_Q_generated :
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))=
 inner ℂ sourceUnit (PA.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2) •
  (sourceReentryVector coordinate : BurnolPaAmbientCarrier) := by
 rw [actual_reentry_generated]
 change inner ℂ sourceUnit (PA.invisible (D.raw observation nontrivial half depth ordinal)) •
  (sourceReentryVector coordinate : BurnolPaAmbientCarrier)=_
 rw [actual_beta_Q]

theorem actual_Pa_successor_Q_reentry :
 PA.actualPa observation nontrivial half depth (ordinal+1)=
 V.generatedCorrection observation nontrivial half depth ordinal+
 Prior.sourceCoefficient observation nontrivial half depth ordinal •
  PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 inner ℂ sourceUnit (PA.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2) •
  (sourceReentryVector coordinate : BurnolPaAmbientCarrier) := by
 rw [V.actual_Pa_successor_from_source,actual_reentry_Q_generated]

/-- Every original Mobius coordinate consumes the same generated physical-Q return vector. -/
theorem actual_Mobius_successor_Q_reentry :
 burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth (ordinal+1))=
 burnolTateReciprocalL2
  (OriginalPaPhysicalGreen.sourceVolterraWindow coordinate
   (burnolTateReciprocalL2
    (burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth ordinal))))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal •
  burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
 inner ℂ sourceUnit (PA.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2) •
  burnolMobiusSourceL2 (sourceReentryVector coordinate : BurnolPaAmbientCarrier) := by
 rw [V.actual_Mobius_source_successor_Volterra,actual_reentry_Q_generated,map_smul]
end ActualOriginalInput

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalReentrySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
