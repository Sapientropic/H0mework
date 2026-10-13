import H0mework.Versions.Rfde5c14d.Realization.Operations.Inquiry.Context.Faces.Reverse.Coefficients.Family
import H0mework.Versions.Rfde5c14d.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Installation.Runtime

/-! The existing mother engine reads source-generated coefficient syntax.
The complete original reverse packet and expanded calculation receipts stay
installed; its actual normal recovers its own original reverse fibre. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Reverse.Coefficients
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationScalarInventoryLift
open SourceOperationLogic SourceOperationLogic.FibreLift SourceGeneratedScalarDifferentialResidual
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base root query resultFace actualOccurrence next state)
end S
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
def component : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => PacketAt
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence
  project := fun _ {_current} occurrence _ => packetAt
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence

def programme : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
    (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) where
  LowVar := PhysicalVar
  datum frame := {
    component := some (component frame)
    reader := fun {_current} occurrence => ((component frame).project PUnit.unit occurrence PUnit.unit).2.raw }

def installation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (S.base frame).root.source.base (component (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerRoot frame programme).source.base
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme))

def face : SourceNativeRootSemanticFaceAt (S.root frame programme)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit frame programme) where
  projection := (installation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_word : (S.query frame programme).raw = (face frame).rootRead.2.raw := rfl

private theorem next_raw_current
    (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
      (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    (SourceOperationInquiry.Context.Installation.nextRawAt frame
      (frame.currentState.root.emitted frame.currentState.visit.current)).environment =
      (S.next frame configuration).rawRead.environment := by
  rw [SourceOperationInquiry.Context.Installation.next_raw_source]
  unfold S.next RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.next
    RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.nextFrom
  cases frame.action <;> rfl


abbrev commonRoot := (S.base frame).root.toAuthoritativeRoot
abbrev commonReader := fun (_ : (commonRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current) =>
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame programme).reader (S.actualOccurrence frame)
abbrev chargedState (count : Nat) := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current (commonReader frame) count

theorem charged_state (count : Nat) : chargedState frame count =
    RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state (commonRoot frame)
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
      (commonReader frame) count :=
  SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.CofaceTransport.state_preserved
    (commonRoot frame) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
    (commonReader frame) (component (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)) count

theorem charged_whole (count : Nat) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.whole
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
      (commonReader frame) (chargedState frame count))
      (RootGeneratedDebtActivationJointSource.OwnerFree.whole (commonRoot frame)
        (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
        (commonReader frame) (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state
          (commonRoot frame) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
          (commonReader frame) count)) :=
  SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.CofaceTransport.whole_preserved
    (commonRoot frame) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
    (commonReader frame) (component (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))
    _ _ (heq_of_eq (charged_state frame count))

abbrev receipts := (face frame).rootRead.2

theorem charged_receipt_state (count : Nat) : chargedState frame count =
    state (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (S.actualOccurrence frame) count :=
  charged_state frame count

theorem charged_receipt_whole (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq (RootGeneratedDebtActivationJointSource.OwnerFree.whole
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
      (commonReader frame) (chargedState frame count.1)) ((receipts frame).whole count) :=
  charged_whole frame count.1

def chargedPayment (count : Fin (remaining (receipts frame).raw.expression)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
    (commonReader frame) count

def chargedContinuation (count : Fin (remaining (receipts frame).raw.expression)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activeContinuation
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
    (commonReader frame) count

def chargedStage (count : Fin (remaining (receipts frame).raw.expression + 1)) :=
  SourceGeneratedRuntimeMaterialStageAt.generate
    (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
      (commonReader frame) count.1)

theorem charged_history_stage (count : Fin (remaining (receipts frame).raw.expression + 1)) :
    HEq (chargedStage frame count)
      ((RootGeneratedDebtActivationJointSource.OwnerFree.Calculation.frontier
        (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot frame programme).toAuthoritativeRoot
        (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit frame).current
        (commonReader frame)).history.stageAt count) := HEq.rfl

variable (initial : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation (rawSource raw_actual environment_actual)
end O
abbrev actualRuntime := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.runtime initial programme
abbrev actualFrame (count : Nat) := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.frames initial programme count
abbrev actualSource := O.rawSource initial programme
abbrev actualOccurrence (count : Nat) := S.actualOccurrence (actualFrame initial count)

private def boundaryOf (raw : SourceOperationInquiry.Context.Raw
    (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (next : Env PhysicalValue PhysicalVar) : Formal ℤ PhysicalValue PhysicalVar sort :=
  Finsupp.single raw.expression 1 - Finsupp.single (.const (raw.expression.eval next)) 1

private theorem actual_next_env (count : Nat) : SourceOperationInquiry.Context.readEnv
    (actualRuntime initial) (actualSource initial) ((actualRuntime initial).stateAt count).tick.nextState =
      (actualFrame initial (count + 1)).rawRead.environment :=
  O.environment_actual initial programme (count + 1)

theorem actual_next_word (count : Nat) :
    SourceOperationInquiry.Context.Faces.Reverse.nextWord (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count) =
      F.nextWord (actualFrame initial count) (actualOccurrence initial count) := by
  have runtimeWord := SourceOperationInquiry.Context.Faces.Reverse.source_boundary
    (actualRuntime initial) (actualSource initial) ((actualRuntime initial).stateAt count)
  change _ = boundaryOf
    (SourceOperationInquiry.Context.raw (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count))
    (SourceOperationInquiry.Context.readEnv (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count).tick.nextState) at runtimeWord
  have rawEq := O.raw_actual initial programme count
  have nextEq := actual_next_env initial count
  have body := congrArg₂ boundaryOf rawEq nextEq
  have localWord := (SourceOperationInquiry.Context.Faces.Reverse.Family.nextTrace (actualFrame initial count) (actualOccurrence initial count)).relation_boundary (R := ℤ)
  change _ = boundaryOf (actualFrame initial count).rawRead
    (F.nextEnv (actualFrame initial count) (actualOccurrence initial count)) at localWord
  have localNext := next_raw_current (actualFrame initial count) programme
  have localBody := congrArg (boundaryOf (actualFrame initial count).rawRead) localNext
  exact runtimeWord.trans (body.trans (localBody.symm.trans localWord.symm))

theorem actual_old_word (count : Nat) :
    SourceOperationInquiry.Context.Faces.Reverse.oldWord (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count) =
      SourceOperationInquiry.Context.Faces.Reverse.Family.oldWord (actualFrame initial count) (actualOccurrence initial count) := by
  have rawEq := O.raw_actual initial programme count
  have runtimeWord := SourceOperationInquiry.Context.relation_boundary
    (actualRuntime initial) (actualSource initial) ((actualRuntime initial).stateAt count)
  have localWord := (F.material (actualFrame initial count) (actualOccurrence initial count)).oldTrace.relation_boundary (R := ℤ)
  change _ = boundaryOf (SourceOperationInquiry.Context.raw (actualRuntime initial) (actualSource initial)
    ((actualRuntime initial).stateAt count))
    (SourceOperationInquiry.Context.raw (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count)).environment at runtimeWord
  change SourceOperationInquiry.Context.Faces.Reverse.Family.oldWord (actualFrame initial count) (actualOccurrence initial count) =
    boundaryOf (actualFrame initial count).rawRead (actualFrame initial count).rawRead.environment at localWord
  exact runtimeWord.trans ((congrArg (fun raw => boundaryOf raw raw.environment) rawEq).trans localWord.symm)

theorem actual_target_word (count : Nat) :
    (SourceOperationInquiry.Context.Faces.Reverse.target (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count)).val =
      (SourceOperationInquiry.Context.Faces.Reverse.Family.target (actualFrame initial count) (actualOccurrence initial count)).val :=
  congrArg₂ (· + ·) (actual_old_word initial count) (actual_next_word initial count)

private def rawOf (old increment : Env PhysicalValue PhysicalVar)
    (word : Formal ℤ PhysicalValue PhysicalVar sort) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  ⟨pairEnvironment old increment, liftExpr (W.expression word)⟩

private theorem expanded_pair_eval
    {process : SourceNativeInquiryEngineProcess.{u}}
    (runtime : SourceNativeInquiryRuntime process)
    (source : SourceOperationInquiry.Context.RawSource
      (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)
    (state : runtime.State) (word : Formal ℤ PhysicalValue PhysicalVar sort) :
    (rawOf (SourceOperationInquiry.Context.readEnv runtime source state)
      (SourceOperationInquiry.Context.increment runtime source state) word).expression.eval
      (rawOf (SourceOperationInquiry.Context.readEnv runtime source state)
        (SourceOperationInquiry.Context.increment runtime source state) word).environment =
        SourceOperationInquiry.Context.Faces.pairInventory runtime source state word := by
  change (liftExpr (W.expression word)).eval
    (pairEnvironment (SourceOperationInquiry.Context.readEnv runtime source state)
      (SourceOperationInquiry.Context.increment runtime source state)) = _
  rw [eval_liftExpr, W.expression_eval, W.expression_effect]
  rfl

private theorem actual_delta (count : Nat) : SourceOperationInquiry.Context.increment
    (actualRuntime initial) (actualSource initial) ((actualRuntime initial).stateAt count) =
      F.delta (actualFrame initial count) (actualOccurrence initial count) := by
  have atCurrent := O.environment_actual initial programme count
  have atNext := actual_next_env initial count
  have actualDelta := congrArg₂ (· - ·) atNext atCurrent
  have localNext := next_raw_current (actualFrame initial count) programme
  exact actualDelta.trans (congrArg (fun environment => environment - (actualFrame initial count).rawRead.environment) localNext).symm

private theorem actual_pair_raw (count : Nat) :
    rawOf (SourceOperationInquiry.Context.readEnv (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count)) (SourceOperationInquiry.Context.increment
      (actualRuntime initial) (actualSource initial) ((actualRuntime initial).stateAt count))
      (SourceOperationInquiry.Context.Faces.Reverse.nextWord (actualRuntime initial) (actualSource initial)
        ((actualRuntime initial).stateAt count)) =
      pairRaw (actualFrame initial count) (actualOccurrence initial count) := by
  exact (congrArg₂ (fun old increment => rawOf old increment
    (SourceOperationInquiry.Context.Faces.Reverse.nextWord (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count)))
    (O.environment_actual initial programme count) (actual_delta initial count)).trans
      (congrArg (rawOf (F.oldEnv (actualFrame initial count) (actualOccurrence initial count))
        (F.delta (actualFrame initial count) (actualOccurrence initial count))) (actual_next_word initial count))

private theorem epoch_pair_raw
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    pairRaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence =
      pairRaw frame occurrence := by
  have rawEq : (F.material (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence).raw =
      (F.material frame occurrence).raw := rfl
  have nextEq : (F.material (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence).nextRaw =
      (F.material frame occurrence).nextRaw := by
    unfold F.material SourceOperationInquiry.Context.Installation.materialAt
    dsimp only
    rcases occurrence with ⟨support, event⟩
    cases event
    unfold SourceOperationInquiry.Context.Installation.nextRawAt
    dsimp only [SourceOperationInquiry.Context.Faces.Execution.Activation.epoch]
    cases RootGeneratedDebtActivationJointSource.mathAction current.2 <;> rfl
  unfold pairRaw F.nextWord SourceOperationInquiry.Context.Faces.Reverse.Family.nextTrace
    SourceOperationInquiry.Context.Faces.Reverse.Family.expression F.delta F.nextEnv F.oldEnv
  rw [rawEq, nextEq]

private theorem reader_generated (count : Nat) :
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum (actualFrame initial count) programme).reader
      (S.actualOccurrence (actualFrame initial count)) =
        pairRaw (actualFrame initial count) (actualOccurrence initial count) := by
  have emitted : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum
      (actualFrame initial count) programme).reader (S.actualOccurrence (actualFrame initial count)) =
      pairRaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch (actualFrame initial count))
        (actualOccurrence initial count) := rfl
  exact emitted.trans (epoch_pair_raw (actualFrame initial count) (actualOccurrence initial count))

theorem normal_recovered (count : Nat) :
    (S.resultFace (actualFrame initial count) programme).rootRead.2.2.1 =
      SourceOperationInquiry.Context.Faces.recover (actualRuntime initial) (actualSource initial)
        ((actualRuntime initial).stateAt count)
        (SourceOperationInquiry.Context.Faces.Reverse.reverse (actualRuntime initial) (actualSource initial)
          ((actualRuntime initial).stateAt count)) := by
  have value := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot (actualFrame initial count) programme).toAuthoritativeRoot
    ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum (actualFrame initial count) programme).reader)
    (S.actualOccurrence (actualFrame initial count))
  have evalEq := congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) => raw.expression.eval raw.environment)
      (actual_pair_raw initial count)
  have readerEq := congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) => raw.expression.eval raw.environment)
      (reader_generated initial count)
  exact value.trans (readerEq.trans (evalEq.symm.trans
    ((expanded_pair_eval (actualRuntime initial) (actualSource initial)
      ((actualRuntime initial).stateAt count)
      (SourceOperationInquiry.Context.Faces.Reverse.nextWord (actualRuntime initial) (actualSource initial)
        ((actualRuntime initial).stateAt count))).trans
      (SourceOperationInquiry.Context.Faces.Reverse.reverse_recover (actualRuntime initial) (actualSource initial)
        ((actualRuntime initial).stateAt count)).symm)))

theorem normal_cost (count : Nat) :
    (S.resultFace (actualFrame initial count) programme).rootRead.2.1.2.length =
      SaturationMonoid.SourceOperationExecution.Coefficients.cost
        (F.nextWord (actualFrame initial count) (actualOccurrence initial count)) := by
  have charged := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot (actualFrame initial count) programme).toAuthoritativeRoot
    ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum (actualFrame initial count) programme).reader)
    (S.actualOccurrence (actualFrame initial count))
  have rawCost := congrArg (fun raw : O.Raw
    (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) => remaining raw.expression)
    (reader_generated initial count)
  exact charged.trans (rawCost.trans
    (SaturationMonoid.SourceOperationExecution.Coefficients.lifted_remaining
      (F.nextWord (actualFrame initial count) (actualOccurrence initial count))))

theorem actual_answer_next (count : Nat) :
    type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initial programme count) ∧
    type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initial programme count) :=
  ⟨SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initial programme count,
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initial programme count⟩

end SourceOperationInquiry.Context.Faces.Reverse.Coefficients
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
