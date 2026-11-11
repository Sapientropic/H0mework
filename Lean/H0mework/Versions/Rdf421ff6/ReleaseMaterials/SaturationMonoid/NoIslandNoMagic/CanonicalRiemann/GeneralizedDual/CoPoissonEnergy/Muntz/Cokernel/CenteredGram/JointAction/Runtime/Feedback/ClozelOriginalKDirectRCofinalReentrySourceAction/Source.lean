import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Window

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalReentrySourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local instance ambientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance fullPaComplete : CompleteSpace ↥(burnolCompactCoPoissonClosedRange.toSubmodule) := by
 apply IsComplete.completeSpace_coe
 exact burnolCompactCoPoissonClosedRange.isClosed.isComplete
namespace PA
export OriginalKCombCofinalPaAction (actualPa actualPa_mem E invisible invisible_mem wholePa_normal_read)
end PA
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace D
export OriginalKCombFirstFullSourceDynamics (raw)
end D
namespace V
export OriginalKDirectRCofinalMobiusSourceAction
 (generatedCorrection actual_Pa_successor_from_source actual_Mobius_source_successor_Volterra)
end V
namespace Prior
export OriginalKDirectRCofinalDivision (sourceCoefficient)
export OriginalKDirectRCofinalPaUpdate (sourceWholeUnit)
end Prior

/-- Riesz is applied to the existing complete source coefficient after the actual Fourier action. -/
def sourceReentryVector (coordinate : BurnolCompletedMellinCoordinate) :
 ↥(burnolCompactCoPoissonClosedRange.toSubmodule) :=
 (InnerProductSpace.toDual ℂ ↥(burnolCompactCoPoissonClosedRange.toSubmodule)).symm
  (((burnolPaResolventSourceCoefficient (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)).comp
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).toContinuousLinearEquiv.toContinuousLinearMap).comp
   burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL)

/-- The full input is paired with the actual conjugate-parameter Fourier unit. -/
def sourceReentryAction (coordinate : BurnolCompletedMellinCoordinate) :
 BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
 (innerSL ℂ (fourierL2 (burnolUnitTailResponse
   (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) 4))).smulRight
  (sourceReentryVector coordinate : BurnolPaAmbientCarrier)

theorem full_pa_reentry_test (coordinate : BurnolCompletedMellinCoordinate)
 (i : BurnolL2) (invisible : PA.E i=0)
 (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
 inner ℂ g (PA.E (burnolDirectRightResolvent (coordinate.value/2) i)) =
 star (burnolPaResolventSourceCoefficient (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius g)) *
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) 4)) i := by
 let starCoordinate := OriginalPrimitiveRankBalance.conjugateCoordinate coordinate
 let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
 have FgPa : F g∈burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inside
 let corrected := burnolPaSourceCorrection starCoordinate ⟨F g,FgPa⟩
 let coefficient := burnolPaResolventSourceCoefficient starCoordinate (F g)
 have correctedPa := burnolPaSourceCorrection_mem starCoordinate ⟨F g,FgPa⟩
 have FcorrectedPa : F corrected∈burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange correctedPa
 have killed : inner ℂ ((F corrected : BurnolPaAmbientCarrier) : BurnolL2) i=0 := by
  have actual := PA.wholePa_normal_read i (F corrected) FcorrectedPa
  rw [invisible,inner_zero_right] at actual
  exact actual.symm
 have split : burnolDirectRightResolvent (starCoordinate.value/2) (F g : BurnolL2) =
  (corrected : BurnolL2)+coefficient • burnolUnitTailResponse starCoordinate 4 := by
  change burnolDirectRightResolvent (starCoordinate.value/2) (F g : BurnolL2) =
   (burnolDirectRightResolvent (starCoordinate.value/2) (F g : BurnolL2)-
    coefficient • burnolUnitTailResponse starCoordinate 4)+coefficient • burnolUnitTailResponse starCoordinate 4
  abel
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 have starRight : 1/4<(starCoordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [starCoordinate.rightHalf]
 have starParameter : star (coordinate.value/2)=starCoordinate.value/2 := by
  simp [starCoordinate,OriginalPrimitiveRankBalance.conjugateCoordinate]
 have invol : fourierL2 (F g : BurnolL2)=(g : BurnolL2) :=
  congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2))
   (evenFaceFourier_involutive burnolUnscaledCommonGapRadius g)
 have adjoint := FiniteMobiusResolventFlux.fourier_R (starCoordinate.value/2) starRight (F g : BurnolL2)
 rw [invol] at adjoint
 have generated : FiniteMobiusResolventFlux.Rplus (star (coordinate.value/2)) (g : BurnolL2) =
  fourierL2 (corrected : BurnolL2)+coefficient • fourierL2 (burnolUnitTailResponse starCoordinate 4) := by
  rw [starParameter,←adjoint,split,map_add,map_smul]
 change inner ℂ (fourierL2 (corrected : BurnolL2)) i=0 at killed
 rw [PA.wholePa_normal_read _ g inside,
  OriginalKCompactAdjointRSource.actual_original_R_adjoint _ right,generated,
  inner_add_left,inner_smul_left,killed,zero_add]
 rfl

theorem sourceReentryVector_read (coordinate : BurnolCompletedMellinCoordinate)
 (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
 inner ℂ g (sourceReentryVector coordinate : BurnolPaAmbientCarrier) =
 star (burnolPaResolventSourceCoefficient (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)
  (evenFaceFourierEquiv burnolUnscaledCommonGapRadius g)) := by
 have actual := InnerProductSpace.toDual_symm_apply (𝕜:=ℂ)
  (x:= (⟨g,inside⟩ : ↥(burnolCompactCoPoissonClosedRange.toSubmodule)))
  (y:= (((burnolPaResolventSourceCoefficient (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate)).comp
    (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).toContinuousLinearEquiv.toContinuousLinearMap).comp
   burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL))
 change inner ℂ (sourceReentryVector coordinate)
  (⟨g,inside⟩ : ↥(burnolCompactCoPoissonClosedRange.toSubmodule)) = _ at actual
 have symmetric := inner_conj_symm (𝕜:=ℂ) (⟨g,inside⟩ : ↥(burnolCompactCoPoissonClosedRange.toSubmodule))
  (sourceReentryVector coordinate)
 rw [actual] at symmetric
 exact symmetric.symm

/-- All Pa tests separate the complete re-entry vector, for every full-L2 invisible input. -/
theorem full_pa_reentry_action (coordinate : BurnolCompletedMellinCoordinate)
 (i : BurnolL2) (invisible : PA.E i=0) :
 PA.E (burnolDirectRightResolvent (coordinate.value/2) i)=sourceReentryAction coordinate i := by
 have normal (g : BurnolPaAmbientCarrier) (inside : g∈burnolCompactCoPoissonClosedRange) :
  inner ℂ g (PA.E (burnolDirectRightResolvent (coordinate.value/2) i))=
  inner ℂ g (sourceReentryAction coordinate i) := by
  rw [full_pa_reentry_test coordinate i invisible g inside]
  change _ = inner ℂ g ((inner ℂ (fourierL2 (burnolUnitTailResponse
   (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) 4)) i) •
   (sourceReentryVector coordinate : BurnolPaAmbientCarrier))
  rw [inner_smul_right,sourceReentryVector_read coordinate g inside]
  exact mul_comm _ _
 have belongs : PA.E (burnolDirectRightResolvent (coordinate.value/2) i)-sourceReentryAction coordinate i∈
  burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem
   (Submodule.starProjection_apply_mem _ _)
   (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ (sourceReentryVector coordinate).property)
 have zero : inner ℂ (PA.E (burnolDirectRightResolvent (coordinate.value/2) i)-sourceReentryAction coordinate i)
  (PA.E (burnolDirectRightResolvent (coordinate.value/2) i)-sourceReentryAction coordinate i)=0 := by
  rw [inner_sub_right,normal _ belongs,sub_self]
 exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

theorem full_invisible_reentry (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
 PA.E (burnolDirectRightResolvent (coordinate.value/2) (PA.invisible value))=
 sourceReentryAction coordinate (PA.invisible value) := by
 apply full_pa_reentry_action
 exact PA.invisible_mem value

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem actual_reentry_generated :
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))=
 sourceReentryAction (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (PA.invisible (D.raw observation nontrivial half depth ordinal)) := by
 rw [OriginalKCombCofinalRAction.original_R_direct]
 exact full_invisible_reentry
  (burnolDivisionZeroCompletedMellinCoordinate observation half.down) _

/-- The actual generated Pa successor now computes the entire invisible re-entry. -/
theorem actual_Pa_successor_source_reentry :
 PA.actualPa observation nontrivial half depth (ordinal+1) =
 V.generatedCorrection observation nontrivial half depth ordinal +
 Prior.sourceCoefficient observation nontrivial half depth ordinal •
  PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2) +
 sourceReentryAction (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (PA.invisible (D.raw observation nontrivial half depth ordinal)) := by
 rw [V.actual_Pa_successor_from_source,actual_reentry_generated]

/-- The same full vector action enters every coordinate of the original Mobius successor. -/
theorem actual_Mobius_successor_source_reentry :
 burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth (ordinal+1)) =
 burnolTateReciprocalL2
  (OriginalPaPhysicalGreen.sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
   (burnolTateReciprocalL2
    (burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth ordinal)))) +
 Prior.sourceCoefficient observation nontrivial half depth ordinal •
  burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)) +
 burnolMobiusSourceL2
  (sourceReentryAction (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
   (PA.invisible (D.raw observation nontrivial half depth ordinal))) := by
 rw [V.actual_Mobius_source_successor_Volterra,actual_reentry_generated]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalReentrySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
