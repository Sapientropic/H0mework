import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaCoefficientActionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Synthesis.Action

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaNativePortSource
open Complex BurnolPhysicalState OriginalPaPhysicalGreen
open SourceOperationEffects
open scoped InnerProductSpace
abbrev Pa := burnolCompactCoPoissonClosedRange.toSubmodule
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance : CompleteSpace ↥Pa :=
  IsComplete.completeSpace_coe burnolCompactCoPoissonClosedRange.isClosed.isComplete

def sourceMap : ↥Pa →L[ℂ] BurnolL2 :=
  (burnolTateReciprocalL2.comp burnolMobiusSourceL2).comp Pa.subtypeL

def correction (c : BurnolCompletedMellinCoordinate) : ↥Pa →L[ℂ] ↥Pa :=
  (burnolPaSourceCorrection c).codRestrict Pa (burnolPaSourceCorrection_mem c)

def loop (c : BurnolCompletedMellinCoordinate) (n : Nat) (input : ↥Pa) : ↥Pa :=
  ((fun p : ↥Pa => correction c p)^[n]) input

def port (c : BurnolCompletedMellinCoordinate) (n : Nat) (input : ↥Pa) : ℂ :=
  burnolPaResolventSourceCoefficient c (loop c n input : BurnolPaAmbientCarrier)

theorem actual_source_step (c : BurnolCompletedMellinCoordinate) (input : ↥Pa) :
    sourceMap (correction c input) = sourceVolterraWindow c (sourceMap input) :=
  (sourceVolterraWindow_original_pa c input.val input.property).symm

theorem actual_source_loop (c : BurnolCompletedMellinCoordinate) (n : Nat) (input : ↥Pa) :
    sourceMap (loop c n input) = ((fun α : BurnolL2 => sourceVolterraWindow c α)^[n]) (sourceMap input) := by
  induction n with
  | zero => rfl
  | succ n previous =>
    simp only [loop, Function.iterate_succ_apply'] at *
    rw [actual_source_step]
    exact congrArg (sourceVolterraWindow c) previous

/-- The whole original R output retains its own coefficient and true unit at every generated rung. -/
theorem actual_original_R (c : BurnolCompletedMellinCoordinate) (n : Nat) (input : ↥Pa) :
    burnolDirectRightResolventCLM c ((loop c n input : BurnolPaAmbientCarrier) : BurnolL2) =
      ((loop c (n+1) input : BurnolPaAmbientCarrier) : BurnolL2) +
        port c n input • burnolUnitTailResponse c 4 := by
  have next : loop c (n+1) input = correction c (loop c n input) := by
    unfold loop
    exact Function.iterate_succ_apply' _ _ _
  rw [next]
  unfold port
  change burnolDirectRightResolvent (c.value/2) _ =
    (burnolDirectRightResolvent (c.value/2) _ -
      burnolPaResolventSourceCoefficient c (loop c n input : BurnolPaAmbientCarrier) •
        burnolUnitTailResponse c 4) + _
  exact (sub_add_cancel _ _).symm

theorem actual_port_source (c : BurnolCompletedMellinCoordinate) (n : Nat) (input : ↥Pa) :
    port c n input = 2 * burnolMellinTailEvaluator c.value c.rightHalf
      (((fun α : BurnolL2 => sourceVolterraWindow c α)^[n]) (sourceMap input)) := by
  change 2 * burnolMellinTailEvaluator c.value c.rightHalf (sourceMap (loop c n input)) = _
  rw [actual_source_loop]

theorem sourceMap_injective : Function.Injective sourceMap := by
  intro left right same
  apply Subtype.ext
  exact original_pa_tate_source_injective left.val right.val left.property right.property same

theorem sourceMap_zero_iff (input : ↥Pa) : sourceMap input = 0 ↔ input = 0 := by
  constructor
  · intro zero
    apply sourceMap_injective
    simpa only [map_zero] using zero
  · rintro rfl
    exact map_zero _

theorem zero_port_control (c : BurnolCompletedMellinCoordinate) (n : Nat) : port c n 0 = 0 := by
  have zero : loop c n 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n previous =>
      change ((fun p : ↥Pa => correction c p)^[n+1]) 0 = 0
      rw [Function.iterate_succ_apply']
      change correction c (loop c n 0) = 0
      rw [previous, map_zero]
  unfold port
  rw [zero]
  change burnolPaResolventSourceCoefficient c (0 : BurnolPaAmbientCarrier) = 0
  exact map_zero _

end OriginalKCrossParameterRAdjointSource.PaNativePortSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
