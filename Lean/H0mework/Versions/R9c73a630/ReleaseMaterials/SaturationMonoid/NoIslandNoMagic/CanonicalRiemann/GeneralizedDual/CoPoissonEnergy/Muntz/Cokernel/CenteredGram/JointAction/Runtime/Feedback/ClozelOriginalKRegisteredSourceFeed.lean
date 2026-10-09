import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalFeedback
import H0mework.Versions.C62.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Consumer
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombRegisteredSourceFeed
open Complex MeasureTheory Set
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open scoped InnerProductSpace
noncomputable section
namespace P
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction
  (value R initial raw code result result_value result_trace sourceState paid_R_state
   RReceipt RReceipt_action RReceipt_target complete_raw physicalProjection physicalRemainder splitPair
   lowProgramme configuration selected actual_physical_next)
end P
namespace C
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombReceiptFeedback (Value Var Frame constantEnvironment)
end C
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch originalProgramme)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base baseRoot root visit actualVisit actualOccurrence datum frames runtime next nextBorn query actual_query)
end S
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active epoch mathNext)
end E
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt)
end Complete
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (programme lowResult actual_query born_complete_inventory)
end I
namespace Receipt
export SourceGeneratedInquiryReceiptAction
  (actionReader actionResultAt actualMaterial actual_raw actual_updated_environment afterEnvironment
   registered first_action whole_first literal_next)
end Receipt
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured
  (state lowInitial lowProgramme lowRuntime compiles whole_first target_next actual_initial
   runtime_source_gate receiver_current receiver_inventory receiver_pair_inventory actual_query)
end CF
namespace N
export SourceOperationInquiry.Context.Native.Frame (read actual fullword_read model_next observer)
end N
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree
  (action law nextState targetOf common_raw_state inputNext)
end OF

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat) (half : OriginalKCombCalculation.Half observation)

def lowProgramme : A.Programme (PhysicalValue := C.Value) (PhysicalVar := C.Var) (sort := ()) :=
  { P.lowProgramme observation nontrivial half with
    datum := fun current => { (P.lowProgramme observation nontrivial half).datum current with
      calculationReader := some (fun {_current} _occurrence => P.raw observation nontrivial half current) } }

def configuration : A.Programme (PhysicalValue := C.Value) (PhysicalVar := C.Var) (sort := ()) :=
  I.programme (lowProgramme observation nontrivial half)

theorem action_raw (current : C.Frame) :
    Receipt.actionReader current (configuration observation nontrivial half) (S.actualOccurrence current) =
      P.raw observation nontrivial half (A.epoch current) := rfl

theorem material_raw (current : C.Frame) :
    (Receipt.actualMaterial current (configuration observation nontrivial half)).raw =
      P.code observation nontrivial half := rfl

theorem material_environment (current : C.Frame) :
    (Receipt.actualMaterial current (configuration observation nontrivial half)).environment =
      (fun _ _ => ((A.epoch current).activeEnvironment () (), (0 : BurnolL2))) := rfl

theorem action_value (current : C.Frame) :
    (Receipt.actionResultAt current (configuration observation nontrivial half)
      (S.actualOccurrence current)).2.2.1 =
      (P.physicalProjection ((P.R observation nontrivial half) ((A.epoch current).activeEnvironment () ())),
       P.physicalRemainder ((P.R observation nontrivial half) ((A.epoch current).activeEnvironment () ()))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot current (configuration observation nontrivial half)).toAuthoritativeRoot
    (Receipt.actionReader current (configuration observation nontrivial half))
    (S.actualOccurrence current)).trans rfl

theorem material_trace (current : C.Frame) :
    (Receipt.actualMaterial current (configuration observation nontrivial half)).state.2.length = 3 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (S.baseRoot current (configuration observation nontrivial half)).toAuthoritativeRoot
    (Receipt.actionReader current (configuration observation nontrivial half))
    (S.actualOccurrence current)).trans rfl

def sourceState (current : C.Frame) (count : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
    (S.baseRoot current (configuration observation nontrivial half)).toAuthoritativeRoot
    (S.visit current (configuration observation nontrivial half)).current
    (fun _ => Receipt.actionReader current (configuration observation nontrivial half)
      (S.actualOccurrence current)) count

theorem sourceState_source (current : C.Frame) (count : Nat) :
    sourceState observation nontrivial half current count =
      P.sourceState observation nontrivial half current count :=
  OF.common_raw_state
    (S.baseRoot current (configuration observation nontrivial half)).toAuthoritativeRoot
    (S.visit current (configuration observation nontrivial half)).current
    (S.base current).root.toAuthoritativeRoot (S.actualVisit current).current
    (P.raw observation nontrivial half (A.epoch current)) count

theorem paid_R_state (current : C.Frame) : (sourceState observation nontrivial half current 2).1 =
    .linear (s := ()) (t := ()) P.splitPair.toLinearMap.toAddMonoidHom
      (.const (s := ()) ((P.R observation nontrivial half) ((A.epoch current).activeEnvironment () ()),
        (0 : BurnolL2))) :=
  (congrArg Sigma.fst (sourceState_source observation nontrivial half current 2)).trans
    (P.paid_R_state observation nontrivial half current)

theorem low_value (current : C.Frame) :
    (I.lowResult (A.epoch current) (lowProgramme observation nontrivial half) (S.actualOccurrence current)).2.2.1 =
      (P.physicalProjection ((P.R observation nontrivial half) ((A.epoch current).activeEnvironment () ())),
       P.physicalRemainder ((P.R observation nontrivial half) ((A.epoch current).activeEnvironment () ()))) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (S.baseRoot (A.epoch current) (lowProgramme observation nontrivial half)).toAuthoritativeRoot
    (S.datum (A.epoch current) (lowProgramme observation nontrivial half)).reader
    (S.actualOccurrence current)).trans rfl

theorem receiver_environment_source (current : C.Frame) : E.At (Value := PairValue C.Value) (Var := C.Var) (sort := ())
    (CF.lowInitial current (configuration observation nontrivial half))
    (fun _ _ => ((A.epoch current).activeEnvironment () (), (0 : BurnolL2))) := by
  intro _ occurrence
  rfl

private theorem born_unsettled (current : C.Frame)
    (cfg : A.Programme (PhysicalValue := C.Value) (PhysicalVar := C.Var) (sort := ()))
    (settled : SourceOperationExecutionDebt.Settlement (S.nextBorn current cfg).event.state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law
    (S.nextBorn current cfg).registered.input.environment
    (S.nextBorn current cfg).registered.input.expression).settlement_budget_zero settled
  have budget := SourceRegisteredClaimClock.remainder_generated (S.nextBorn current cfg)
  have growth := current.request_budget
  change remaining (S.nextBorn current cfg).event.state.1 = 0 at zero
  change remaining (S.nextBorn current cfg).event.state.1 = remaining current.request.input.expression - (0 + 1) at budget
  omega

theorem born_next_paid (current : C.Frame)
    (cfg : A.Programme (PhysicalValue := C.Value) (PhysicalVar := C.Var) (sort := ())) :
    S.next (S.nextBorn current cfg) (configuration observation nontrivial half) = (S.nextBorn current cfg).mathNext := by
  unfold S.next
  cases actual : (S.nextBorn current cfg).action with
  | inl settled => exact False.elim (born_unsettled current cfg settled)
  | inr paid => rfl

attribute [local irreducible] P.code

abbrev priorReceipt := Complete.receipt (P.configuration observation nontrivial half)
  (P.initial observation nontrivial depth half) 0
abbrev born := S.nextBorn (P.selected observation nontrivial depth half)
  (P.configuration observation nontrivial half)
abbrev recoveredBorn := N.read (P.initial observation nontrivial depth half)
  (P.configuration observation nontrivial half)
  ((S.runtime (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half)).stateAt
    ((priorReceipt observation nontrivial depth half).1 + 1))
abbrev projected := P.physicalProjection ((P.R observation nontrivial half) (P.value observation nontrivial depth half))

theorem frames_born : S.frames (P.initial observation nontrivial depth half)
    (P.configuration observation nontrivial half) ((priorReceipt observation nontrivial depth half).1 + 1) =
      born observation nontrivial depth half := by
  let generated := priorReceipt observation nontrivial depth half
  have same : S.frames (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half)
      ((0 + generated.1) + 1) = born observation nontrivial depth half := by
    change S.next (S.frames (P.initial observation nontrivial depth half)
      (P.configuration observation nontrivial half) (0 + generated.1))
        (P.configuration observation nontrivial half) = _
    unfold S.next
    rw [generated.2.2.2]
  simpa only [Nat.zero_add] using same

theorem recovered_born : recoveredBorn observation nontrivial depth half = born observation nontrivial depth half :=
  (N.actual (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half)
    ((priorReceipt observation nontrivial depth half).1 + 1)).trans (frames_born observation nontrivial depth half)

theorem full_model_born :
    N.observer (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half)
      (SourceOperationInquiry.Context.readCompletion
        (S.runtime (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half))
        (SourceOperationInquiry.Context.completionAction
          (S.runtime (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half))
          (SourceOperationInquiry.Context.completionPoint
            (S.runtime (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half))
            ((S.runtime (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half)).stateAt
              (priorReceipt observation nontrivial depth half).1)))) =
      Finsupp.single (born observation nontrivial depth half) 1 :=
  (N.model_next (P.initial observation nontrivial depth half) (P.configuration observation nontrivial half)
    (priorReceipt observation nontrivial depth half).1).trans
      (congrArg (fun frame : C.Frame => Finsupp.single frame (1 : ℤ)) (frames_born observation nontrivial depth half))

theorem born_environment : E.At (Value := C.Value) (Var := C.Var) (sort := ())
    (recoveredBorn observation nontrivial depth half)
    (C.constantEnvironment (projected observation nontrivial depth half)) := by
  rw [recovered_born]
  exact P.actual_physical_next observation nontrivial depth half

theorem born_epoch_environment : (A.epoch (recoveredBorn observation nontrivial depth half)).activeEnvironment =
    C.constantEnvironment (projected observation nontrivial depth half) :=
  E.epoch (born_environment observation nontrivial depth half)

theorem next_action_source : Receipt.actionReader (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half) (S.actualOccurrence (recoveredBorn observation nontrivial depth half)) =
      (⟨fun _ _ => (projected observation nontrivial depth half, (0 : BurnolL2)),
        P.code observation nontrivial half⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
          (Value := PairValue C.Value) (Var := C.Var) (sort := ())) := by
  rw [action_raw]
  unfold _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.raw
  rw [born_epoch_environment]
  rfl

theorem next_low_source : I.lowResult (A.epoch (recoveredBorn observation nontrivial depth half))
    (lowProgramme observation nontrivial half) (S.actualOccurrence (recoveredBorn observation nontrivial depth half)) |>.2.2.1 =
      (P.physicalProjection ((P.R observation nontrivial half) (projected observation nontrivial depth half)),
       P.physicalRemainder ((P.R observation nontrivial half) (projected observation nontrivial depth half))) := by
  rw [low_value, born_epoch_environment]
  rfl

theorem next_registered_value :
    (Receipt.actionResultAt (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)
      (S.actualOccurrence (recoveredBorn observation nontrivial depth half))).2.2.1 =
      (P.physicalProjection ((P.R observation nontrivial half) (projected observation nontrivial depth half)),
       P.physicalRemainder ((P.R observation nontrivial half) (projected observation nontrivial depth half))) := by
  rw [action_value, born_epoch_environment]
  rfl

theorem next_paid_R_state : (sourceState observation nontrivial half (recoveredBorn observation nontrivial depth half) 2).1 =
    .linear (s := ()) (t := ()) P.splitPair.toLinearMap.toAddMonoidHom
      (.const (s := ()) ((P.R observation nontrivial half) (projected observation nontrivial depth half), (0 : BurnolL2))) := by
  rw [paid_R_state, born_epoch_environment]
  rfl

theorem next_paid_trace :
    (Receipt.actualMaterial (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)).state.2.length = 3 :=
  material_trace observation nontrivial half (recoveredBorn observation nontrivial depth half)

theorem next_complete_raw :
    (Receipt.actionResultAt (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)
      (S.actualOccurrence (recoveredBorn observation nontrivial depth half))).2.2.1.1 +
    (Receipt.actionResultAt (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)
      (S.actualOccurrence (recoveredBorn observation nontrivial depth half))).2.2.1.2 =
      (P.R observation nontrivial half) (projected observation nontrivial depth half) := by
  rw [next_registered_value]
  change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection _ +
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmoduleᗮ.starProjection _ = _
  exact Submodule.starProjection_add_starProjection_orthogonal _

theorem after_born_environment : Receipt.afterEnvironment (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half) =
      (fun _ _ => (projected observation nontrivial depth half, (0 : BurnolL2))) := by
  rw [recovered_born]
  unfold SourceGeneratedInquiryReceiptAction.afterEnvironment
  rw [born_next_paid, action_raw]
  unfold _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction.raw
  have env := E.epoch (E.mathNext (P.actual_physical_next observation nontrivial depth half))
  rw [env]
  rfl

theorem registered_environment :
    (Receipt.registered (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)).input.environment =
      (fun _ _ => (projected observation nontrivial depth half, (0 : BurnolL2))) :=
  (Receipt.actual_updated_environment (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half)).trans (after_born_environment observation nontrivial depth half)

theorem receiver_environment : E.At (Value := PairValue C.Value) (Var := C.Var) (sort := ())
    (CF.lowInitial (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half))
    (fun _ _ => (projected observation nontrivial depth half, (0 : BurnolL2))) := by
  intro current occurrence
  have source := @receiver_environment_source observation nontrivial half
    (recoveredBorn observation nontrivial depth half) current occurrence
  rw [born_epoch_environment] at source
  exact source

theorem receiver_registered :
    (CF.lowInitial (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)).registered =
      Receipt.registered (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half) := rfl

theorem stock_query : type_of% (I.actual_query (recoveredBorn observation nontrivial depth half)
    (lowProgramme observation nontrivial half)) :=
  I.actual_query (recoveredBorn observation nontrivial depth half) (lowProgramme observation nontrivial half)

theorem configured_compiles : type_of% (CF.compiles (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half)) :=
  CF.compiles (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)

theorem configured_whole : type_of% (CF.whole_first (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half)
    (SourceGeneratedInquiryReceiptAction.sourceEvent (recoveredBorn observation nontrivial depth half)
      (configuration observation nontrivial half))) :=
  CF.whole_first (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)
    (SourceGeneratedInquiryReceiptAction.sourceEvent (recoveredBorn observation nontrivial depth half)
      (configuration observation nontrivial half))

theorem configured_next : type_of% (CF.target_next (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half)
    (SourceGeneratedInquiryReceiptAction.sourceEvent (recoveredBorn observation nontrivial depth half)
      (configuration observation nontrivial half))) :=
  CF.target_next (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)
    (SourceGeneratedInquiryReceiptAction.sourceEvent (recoveredBorn observation nontrivial depth half)
      (configuration observation nontrivial half))

theorem configured_runtime : type_of% (CF.runtime_source_gate (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half)) :=
  CF.runtime_source_gate (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half)

theorem configured_query : type_of% (CF.actual_query (recoveredBorn observation nontrivial depth half)
    (configuration observation nontrivial half) 0) :=
  CF.actual_query (recoveredBorn observation nontrivial depth half) (configuration observation nontrivial half) 0

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombRegisteredSourceFeed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
