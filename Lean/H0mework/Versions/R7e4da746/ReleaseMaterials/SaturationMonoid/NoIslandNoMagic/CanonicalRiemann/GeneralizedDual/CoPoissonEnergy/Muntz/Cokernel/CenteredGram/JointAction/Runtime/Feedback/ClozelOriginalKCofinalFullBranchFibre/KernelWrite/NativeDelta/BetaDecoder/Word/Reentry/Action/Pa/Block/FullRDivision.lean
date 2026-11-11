import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.FullRCode

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRDivision
open Complex RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace D
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
 (completeRSourceRead completeRSourceAction complete_R_source_action_read)
end D
namespace S
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResidualRNativeSuccessor
 (sourcePaInput sourcePaLift source_Pa_lift_read source_Pa_qualified)
end S
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open BurnolPhysicalState

local instance baseGroups (initial : Nat) : ∀ t, AddCommGroup (BaseValue initial t) :=
 DR.L.groups (PairValue C.Value) initial
local instance originGroups (initial : Nat) : ∀ t, AddCommGroup (DR.L.Value (BaseValue initial) 2 t) :=
 DR.L.groups (BaseValue initial) 2
local instance codeGroups (initial : Nat) : ∀ t, AddCommGroup (CodeValue initial t) :=
 DR.L.groups (BaseValue initial) 3
local instance valueGroups (initial : Nat) : ∀ t, AddCommGroup (FullRCode.Value initial t) :=
 DR.L.groups (BaseValue initial) 5
local instance valueAddZeroClass (initial : Nat) (t : Unit) : AddZeroClass (FullRCode.Value initial t) :=
 (valueGroups initial t).toAddCommMonoid.toAddMonoid.toAddZeroClass
local instance valueAddZero (initial : Nat) (t : Unit) : AddZero (FullRCode.Value initial t) :=
 (valueAddZeroClass initial t).toAddZero
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (initial : Nat) (body : Expr (CodeValue initial) C.Var ())
variable (environment : Env (FullRCode.Value initial) C.Var) (total : FullRCode.Value initial ())
variable (actual : Trace environment (FullRCode.code observation nontrivial half initial body) (.const total))
variable (receipts : FullRCode.TwoAt observation nontrivial half initial body environment total actual)

def input := D.completeRSourceRead initial 2 0 ((FullRCode.input initial body).eval environment).1.1
def paRead := D.completeRSourceRead initial 2 0 receipts.paValue.1.1
def paSource : BurnolPaAmbientCarrier :=
 OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField (input initial body environment))

theorem pa_action :
 paRead observation nontrivial half initial body environment total actual receipts =
 OriginalKFullSourceRAction.variableAction observation nontrivial half
  (S.sourcePaInput (input initial body environment)) := by
 unfold paRead
 rw [receipts.pa_action]
 change D.completeRSourceRead initial 2 0
  (D.completeRSourceAction observation nontrivial half initial 2 0
   (S.sourcePaLift initial 2 0 ((FullRCode.input initial body).eval environment).1.1)) = _
 rw [D.complete_R_source_action_read, S.source_Pa_lift_read]
 rfl

theorem pa_qualified : paSource initial body environment ∈ burnolCompactCoPoissonClosedRange :=
 S.source_Pa_qualified _

theorem pa_physical :
 (paRead observation nontrivial half initial body environment total actual receipts).1.1 ∈
 evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 rw [pa_action]
 change OriginalKCombPhysicalAction.R observation nontrivial half
  (paSource initial body environment : BurnolL2) ∈ _
 rw [OriginalKCombCofinalRAction.original_R_direct]
 exact burnolPaResolvent_physical observation nontrivial
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf _
  (pa_qualified initial body environment)

theorem pa_positionGap :
 (paRead observation nontrivial half initial body environment total actual receipts).1.1 ∈
 locallyConstantFace burnolUnscaledCommonGapRadius :=
 (pa_physical observation nontrivial half initial body environment total actual receipts).1.1

def paPhysical : BurnolPaAmbientCarrier :=
 ⟨(paRead observation nontrivial half initial body environment total actual receipts).1.1,
  pa_physical observation nontrivial half initial body environment total actual receipts⟩

theorem pa_response :
 paPhysical observation nontrivial half initial body environment total actual receipts =
 burnolPaResolventPhysicalResponse observation nontrivial
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
  (paSource initial body environment) (pa_qualified initial body environment) := by
 apply Subtype.ext
 change (paRead observation nontrivial half initial body environment total actual receipts).1.1 = _
 rw [pa_action]
 change OriginalKCombPhysicalAction.R observation nontrivial half
  (paSource initial body environment : BurnolL2) = _
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rfl

theorem pa_unit_rank :
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (paPhysical observation nontrivial half initial body environment total actual receipts) =
 burnolPaResolventSourceCoefficient
  (burnolDivisionZeroCompletedMellinCoordinate observation
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)
  (paSource initial body environment) •
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolZeroOwnedUnitTailState observation nontrivial
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf) := by
 rw [pa_response]
 exact burnolPaResolventPhysicalResponse_Q _ _ _ _ _

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.FullRDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
