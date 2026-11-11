import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.CompletedSourceRCalculation

import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.CompletedSourceRCalculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative (native)
end WN
namespace AS
export OriginalKDirectRCofinalMaterial.AS (nativeAfterAdmission)
end AS
namespace W
export OriginalKReturnJordanSourceWriteback (actualValue)
end W

namespace MathSource
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
 (frame residualMaterial residualRegistered residualTarget residual_frame_next residual_first_receipt
  endpointState endpointInput endpointCount endpoint_source_state compiled actual_next)
end MathSource
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base runtime actual_answer actual_query actual_next next nextBorn presentation)
end Shared
namespace Clock
export SourceRegisteredClaimClock (sourceRemainder sourceBudget remainder_generated suffixHistory source_suffix_factorizes suffix_no_restart)
end Clock

local instance originalGroups (grade:Nat) : ∀target,AddCommGroup
 (OriginalKDirectRCofinalMaterial.L.Value (PairValue Original.Value) grade target) :=
 OriginalKDirectRCofinalMaterial.L.groups (PairValue Original.Value) grade

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

theorem same_native_actor : WN.native observation nontrivial half depth ordinal=
 AS.nativeAfterAdmission (OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half)
  (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal) := rfl

theorem input_source : (inputCode observation nontrivial half).eval
 (environment observation nontrivial half depth)=
 OriginalKDefectAction.actionFields (Q.prefixProgramme observation nontrivial half m) :=
 congrArg OriginalKDefectAction.actionFields (prefix_source observation nontrivial half depth)

theorem pa_source : (paReceipt observation nontrivial half depth ordinal).value=
 OriginalKFullSourceRAction.variableAction observation nontrivial half
  (OriginalKSourceResidualRNativeSuccessor.sourcePaInput
   (OriginalKDefectAction.actionFields (Q.prefixProgramme observation nontrivial half m))) := by
 have paid:=completed_trace_value (environment observation nontrivial half depth)
  (paReceipt observation nontrivial half depth ordinal).trace
 change _= (OriginalKFullSourceRAction.variableAction observation nontrivial half)
  (OriginalKSourceResidualRNativeSuccessor.sourcePaInput
   ((inputCode observation nontrivial half).eval (environment observation nontrivial half depth))) at paid
 exact paid.trans (congrArg
  (fun v=>OriginalKFullSourceRAction.variableAction observation nontrivial half
   (OriginalKSourceResidualRNativeSuccessor.sourcePaInput v))
  (input_source observation nontrivial half depth))

theorem nonPa_source : (nonPaReceipt observation nontrivial half depth ordinal).value=
 OriginalKFullSourceRAction.variableAction observation nontrivial half
  (OriginalKSourceResidualRNativeSuccessor.sourceNonPaInput
   (OriginalKDefectAction.actionFields (Q.prefixProgramme observation nontrivial half m))) := by
 have paid:=completed_trace_value (environment observation nontrivial half depth)
  (nonPaReceipt observation nontrivial half depth ordinal).trace
 change _= (OriginalKFullSourceRAction.variableAction observation nontrivial half)
  (OriginalKSourceResidualRNativeSuccessor.sourceNonPaInput
   ((inputCode observation nontrivial half).eval (environment observation nontrivial half depth))) at paid
 exact paid.trans (congrArg
  (fun v=>OriginalKFullSourceRAction.variableAction observation nontrivial half
   (OriginalKSourceResidualRNativeSuccessor.sourceNonPaInput v))
  (input_source observation nontrivial half depth))

theorem full_R_source : value observation nontrivial half depth ordinal=
 OriginalKFullSourceRAction.variableAction observation nontrivial half
  (OriginalKDefectAction.actionFields (Q.prefixProgramme observation nontrivial half m)) := by
 rw [two_child_sum,pa_source,nonPa_source,←map_add,
  OriginalKSourceResidualRNativeSuccessor.source_Pa_nonPa_sum]

theorem physical_R_source : (value observation nontrivial half depth ordinal).1.1=
 burnolDirectRightResolventCLM c (Q.prefixProgramme observation nontrivial half m) := by
 rw [full_R_source]
 rfl

variable (t:ℝ) (N:Nat)
theorem same_original_child : (prefixCode observation nontrivial half).eval
 (environment observation nontrivial half depth)=
 (Original.currentPrefixReceipt observation nontrivial half depth ordinal t N).value :=
 (prefix_source observation nontrivial half depth).trans
  (Q.actual_original_prefix observation nontrivial half depth ordinal t N).symm

include t N in
theorem same_original_next : (value observation nontrivial half depth ordinal).1.1=
 W.actualValue observation nontrivial half depth 1 :=
 (physical_R_source observation nontrivial half depth ordinal).trans
  (PaCoefficientSourceGramConsumer.actual_original_R observation nontrivial half depth ordinal t N)

/-- The input is read from the installed occurrence face, before it is registered. -/
def installedRaw : OF.Raw (Value:=Value) (Var:=Var) (sort:=Slot.branches) :=
 (sourceFace observation nontrivial half depth ordinal).rootRead.2.1

def installedReader := fun
 (_:(installed observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
   (installedVisit observation nontrivial half depth ordinal).current) =>
 installedRaw observation nontrivial half depth ordinal

theorem installed_raw_source : installedRaw observation nontrivial half depth ordinal=
 raw observation nontrivial half depth := rfl

abbrev sourceU7 := (Shared.base
 (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal).2.1.1).U7
abbrev sourceCalculus := (Shared.base
 (OriginalKDirectRCofinalMaterial.D.packet observation nontrivial half depth ordinal).2.1.1).calculus

abbrev sourceFrame := MathSource.frame
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev sourceEndpoint := MathSource.endpointState
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev sourceRegistered := MathSource.residualRegistered
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev registeredMaterial := MathSource.residualMaterial
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
 ((sourceEndpoint observation nontrivial half depth ordinal).root.emitted
  (sourceEndpoint observation nontrivial half depth ordinal).visit.current)
abbrev firstRegisteredTarget := MathSource.residualTarget
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)

theorem registered_source_raw : (registeredMaterial observation nontrivial half depth ordinal).raw=
 (installedRaw observation nontrivial half depth ordinal).expression := rfl

theorem actual_equation_registered :
 (sourceRegistered observation nontrivial half depth ordinal).input.expression=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
  (registeredMaterial observation nontrivial half depth ordinal) := rfl

private theorem firstDestinationAt {Network:WorldRelationNetwork} {Voc:Vocabulary}
 (sourceRoot:SourceNativeLivingRootClosure Network Voc)
 (sourceVisit:SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
 (sourceU7:U7ProducerCalculus Network) (sourceCalculus:U7ObstructionEvolutionCalculus Network sourceU7)
 (read:sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceVisit.current →
  OF.Raw (Value:=Value) (Var:=Var) (sort:=Slot.branches)) :
 type_of% (MathSource.residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus read).firstDestination_heq :=
 (MathSource.residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus read).firstDestination_heq

abbrev registered_first_destination := firstDestinationAt
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev registered_first_next := MathSource.residual_frame_next
 (installed observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)

section Settlement
variable {S:Type} {U X:S→Type} [∀s,AddCommGroup (U s)] {s:S}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
private def stop := {frame with depth:=frame.depth+Clock.sourceRemainder frame}
private theorem stop_zero : remaining (stop frame).event.state.1=0 := by
 change Clock.sourceRemainder (stop frame)=0
 rw [Clock.remainder_generated]
 change Clock.sourceBudget frame-(frame.depth+Clock.sourceRemainder frame+1)=0
 have generated:=Clock.remainder_generated frame
 omega
private def settlement := RootGeneratedDebtActivationJointSource.localSettlement
 (stop frame).event (stop_zero frame)
private theorem stop_action : (stop frame).action=.inl (settlement frame) := by
 cases selected:(stop frame).action with
 | inl chosen =>
  have unique:chosen=settlement frame := by
   rcases chosen with ⟨first,⟨firstEq⟩⟩
   rcases settlement frame with ⟨second,⟨secondEq⟩⟩
   have same:first=second := Expr.const.inj (firstEq.symm.trans secondEq)
   cases same
   rfl
  exact congrArg Sum.inl unique
 | inr paid =>
  have strict:=(RootGeneratedDebtActivationJointSource.law (stop frame).registered).step_budget_lt paid.2
  change remaining paid.1.1<remaining (stop frame).event.state.1 at strict
  rw [stop_zero] at strict
  omega
private theorem stop_next (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=U) (PhysicalVar:=X) (sort:=s)) :
 Shared.next (stop frame) cfg=Shared.nextBorn (stop frame) cfg := by
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 rw [stop_action]

private theorem stop_from_suffix : (stop frame).event.state=
 (SourceRegisteredClaimClock.R.runtimeCurrent frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
  (Clock.suffixHistory frame).target).2.state := by
 have history:(Clock.suffixHistory frame).target=
   SourceRegisteredClaimClock.C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
    (frame.depth+Clock.sourceRemainder frame+1) := by
  change (SourceRegisteredClaimClock.C.runtime frame.old.root.toAuthoritativeRoot frame.registered frame.packetAt
   (frame.depth+1)).advance (Clock.sourceRemainder frame)=_
  rw [SourceRegisteredClaimClock.runtime_advance]
  congr 1
  omega
 rw [history]
 exact SourceRegisteredClaimClock.current_event (stop frame)
end Settlement

abbrev settledSourceFrame := stop (sourceFrame observation nontrivial half depth ordinal)
abbrev sourceSuffix := Clock.suffixHistory (sourceFrame observation nontrivial half depth ordinal)
abbrev sourceSuffixFactorization := Clock.source_suffix_factorizes (sourceFrame observation nontrivial half depth ordinal)
abbrev sourceSuffixStop := stop_from_suffix (sourceFrame observation nontrivial half depth ordinal)
abbrev sourceStopSettlement := settlement (sourceFrame observation nontrivial half depth ordinal)
abbrev sourceStopAction := stop_action (sourceFrame observation nontrivial half depth ordinal)
abbrev sourceConfiguration := SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
 (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=Slot.branches)

def registeredTick := (Shared.runtime
 (settledSourceFrame observation nontrivial half depth ordinal) sourceConfiguration).tickAt 0
abbrev actualRegisteredAnswer := Shared.actual_answer
 (settledSourceFrame observation nontrivial half depth ordinal) sourceConfiguration 0
abbrev actualRegisteredQuery := Shared.actual_query
 (settledSourceFrame observation nontrivial half depth ordinal) sourceConfiguration 0

theorem actual_registered_next : (registeredTick observation nontrivial half depth ordinal).next.node=
 .active (Shared.presentation
  (Shared.nextBorn (settledSourceFrame observation nontrivial half depth ordinal) sourceConfiguration)
  sourceConfiguration) := by
 have actual:=Shared.actual_next (settledSourceFrame observation nontrivial half depth ordinal) sourceConfiguration 0
 change (registeredTick observation nontrivial half depth ordinal).next.node=
  .active (Shared.presentation
   (Shared.next (settledSourceFrame observation nontrivial half depth ordinal) sourceConfiguration)
   sourceConfiguration) at actual
 rw [stop_next] at actual
 exact actual

def actual_completed_original_R :=
 PProd.mk (registeredTick observation nontrivial half depth ordinal)
 (PProd.mk ((sourceFace observation nontrivial half depth ordinal).rootRead)
 (PProd.mk (sourceRegistered observation nontrivial half depth ordinal)
 (PProd.mk (actual_equation_registered observation nontrivial half depth ordinal)
 (PProd.mk (registered_source_raw observation nontrivial half depth ordinal)
 (PProd.mk (firstRegisteredTarget observation nontrivial half depth ordinal)
 (PProd.mk (registered_first_destination observation nontrivial half depth ordinal)
 (PProd.mk (registered_first_next observation nontrivial half depth ordinal)
 (PProd.mk (sourceSuffix observation nontrivial half depth ordinal)
 (PProd.mk (sourceSuffixFactorization observation nontrivial half depth ordinal)
 (PProd.mk (sourceSuffixStop observation nontrivial half depth ordinal)
 (PProd.mk (sourceStopSettlement observation nontrivial half depth ordinal)
 (PProd.mk (sourceStopAction observation nontrivial half depth ordinal)
 (PProd.mk (actualRegisteredQuery observation nontrivial half depth ordinal)
 (PProd.mk (actualRegisteredAnswer observation nontrivial half depth ordinal)
 (PProd.mk (actual_registered_next observation nontrivial half depth ordinal)
 (PProd.mk (same_native_actor observation nontrivial half depth ordinal)
 (PProd.mk (same_original_child observation nontrivial half depth ordinal t N)
 (PProd.mk (same_original_next observation nontrivial half depth ordinal t N)
 (PProd.mk (Original.original_word observation nontrivial half depth ordinal)
 (PProd.mk (Original.current_word_source observation nontrivial half depth ordinal t N)
 (PProd.mk (Original.original_address observation nontrivial half depth)
 (PProd.mk (Original.original_position observation nontrivial half depth ordinal)
 (Original.originalWholeNext observation nontrivial half depth ordinal)))))))))))))))))))))))

end CountedPaInitial.CompletedSourceRCalculation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
