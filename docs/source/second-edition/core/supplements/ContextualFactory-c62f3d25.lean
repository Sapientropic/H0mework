import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Source
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Difference.Forward
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Installation
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Writer
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Source
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Faces
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Tree
import SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Forecast.Source
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s:S}
attribute [local instance] groups
variable (binding : ∀ t,X t → Expr W X t)

def baseFactory : Lower.SourceFamily.Factory W X s :=
 {Lower.SourceFamily.Foresight.factory (s:=s) binding with
  datum := fun n seed sourceFrame =>
    let original := (Profile.FiniteSource.Indexed.Installation.configuration binding n seed).datum sourceFrame
    { original with
      calculationReader :=
        Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
          sourceFrame original }
  nextInventory := fun n seed => (Installed.configuration binding n seed).nextInventory
  nextPairInventory := fun n seed => (Installed.configuration binding n seed).nextPairInventory}

variable (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
def priorSourceTree := Paid.Ledger.sourceTreeAt n data
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query data.1
  (Lower.SourceFamily.cfg (baseFactory (s:=s) binding) n data.2)).raw.expression
def phaseEvent : Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n := .generator
 (Reader.residualExpression binding n data.2
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (actualIndex n data.1))
def phaseSourceTree := SourceHistoryCommon.seed (priorSourceTree binding n data)
 (RootedAccountedUnfolding.zero (phaseEvent binding n data))
def readerSourceTree := SourceHistoryCommon.seed (phaseSourceTree binding n data)
 (Profile.FiniteSource.Indexed.ReaderResidual.sourceTree binding n data)
def sourceTree := SourceHistoryCommon.seed (readerSourceTree binding n data) (Forecast.tree binding n data)

theorem prior_source_preserved (event)
 (present : event ∈ (priorSourceTree binding n data).trace) :
 event ∈ (sourceTree binding n data).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event
  ((SourceHistoryCommon.parallel_left _ _ _).1 event
   ((SourceHistoryCommon.parallel_left _ _ _).1 event present))

theorem phase_source_present : phaseEvent binding n data ∈ (sourceTree binding n data).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 _
  ((SourceHistoryCommon.parallel_left _ _ _).1 _
   ((SourceHistoryCommon.parallel_right _ _ _).1 _ List.mem_cons_self))

theorem reader_source_present : Profile.FiniteSource.Indexed.ReaderResidual.event binding n data ∈ (sourceTree binding n data).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 _
  ((SourceHistoryCommon.parallel_right _ _ _).1 _
   (Profile.FiniteSource.Indexed.ReaderResidual.source_event_present binding n data))

theorem forecast_source_present : Forecast.event binding n data ∈ (sourceTree binding n data).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 _ (Forecast.source_event_present binding n data)

theorem forecast_relation_present (event) (present : event ∈ (Forecast.tree binding n data).trace) :
 event ∈ (sourceTree binding n data).trace :=
 (SourceHistoryCommon.parallel_right _ _ _).1 event present

def generated := Paid.Ledger.run (Paid.Ledger.writeEvent binding n data) (sourceTree binding n data)
def nativeWritten := (Reader.pairWritten binding n data.2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (actualIndex n data.1)).map T.liftEvent
def completeGenerated := Psi.append binding n data.2 data.1
 (SourceHistoryCommon.seed (nativeWritten binding n data) (generated binding n data))
def selectedProfile := Profile.FiniteSource.Indexed.Writer.generated binding n data.2
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1) (actualIndex n data.1)
-- Each selected receipt pays its literal writer; higher native material keeps its original unit.
def selectedGenerated := T.preserve (selectedProfile binding n data) (completeGenerated binding n data)

-- The calculation reader is an actual source action.  Carry the paid
-- relation exposure of that same word into the next pair inventory before
-- adding the forward-difference generator, so downstream boundary consumers
-- see the same occurrence.
def actionWord : Lower.SourceFamily.Foresight.Paid.Word (W:=W) (X:=X) n s :=
 Finsupp.single
  (SourceGeneratedInquiryReceiptAction.actionReader data.1
    (Lower.SourceFamily.cfg (baseFactory (s:=s) binding) n data.2)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence data.1)).expression
  (1:ℤ)
def actionWritten := SourceOperationPaidRelations.exposure
  (Lower.SourceFamily.Foresight.Paid.paidTrace binding n data s (actionWord binding n data))

theorem original_generated_preserved (event) (present:event∈(completeGenerated binding n data).trace):
 event∈(selectedGenerated binding n data).trace :=by
 unfold selectedGenerated T.preserve
 cases selectedProfile binding n data with
 | none=>exact present
 | some chosen=>exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem selected_profile_preserved (chosen) (actual:selectedProfile binding n data=some chosen)
 (event) (present:event∈chosen.trace):event∈(selectedGenerated binding n data).trace:=by
 unfold selectedGenerated T.preserve
 rw [actual]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

def extraPair := some
 (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.pairUpdate binding n data
   (SourceHistoryCommon.seed
    (T.preserve
     ((Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1)
     (selectedGenerated binding n data))
    (actionWritten binding n data)))

def actualFee := (sourceTree binding n data).fold (fun source costs =>
 (Paid.paidTrace binding n data s (Paid.Ledger.eventWord n source)).length+costs.sum)
def sourceFee := (sourceTree binding n data).fold (fun source costs =>
 remaining (Paid.expression (W:=W) (X:=X) n s (Paid.Ledger.eventWord n source))+costs.sum)
theorem fee_source : actualFee binding n data=sourceFee binding n data := by
 unfold actualFee sourceFee
 congr 1
 funext source costs
 exact congrArg (fun fee=>fee+costs.sum) (Paid.complete_fee binding n data s (Paid.Ledger.eventWord n source))

def factory : Lower.SourceFamily.Factory W X s :=
 {baseFactory (s:=s) binding with extraPair:=fun k seed frame=>extraPair binding k ⟨frame,seed⟩}

theorem factory_calculation_reader :
 ((Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2).datum data.1).calculationReader =
 Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
  data.1 ((Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2).datum data.1) := rfl

theorem factory_action_environment (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s))
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current)) :
 (SourceGeneratedInquiryReceiptAction.actionReader frame (Lower.SourceFamily.cfg (factory (s:=s) binding) n seed) supplied).environment=
 ((SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.datum frame
   (Lower.SourceFamily.cfg (factory (s:=s) binding) n seed)).reader supplied).environment := by
 unfold SourceGeneratedInquiryReceiptAction.actionReader
 have h := factory_calculation_reader binding n
   (⟨SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame,seed⟩ : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
 rw [h]
 unfold Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
 cases hp : (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame).pairInventory with
 | none => rfl
 | some tree => rfl

theorem factory_extra_pair_root :
 ((extraPair binding n data).get (by rfl)).root =
 Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.event binding n data := by
 unfold extraPair
 change (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.pairUpdate binding n data _).root = _
 simpa using (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.pairUpdate_root binding n data _)

abbrev factory_receiver := Lower.SourceFamily.receiver (factory (s:=s) binding) n data
abbrev factory_nextSeed := Lower.SourceFamily.nextSeed (factory (s:=s) binding) n data

theorem factory_receiver_pair :
 (factory_receiver binding n data).pairInventory =
 some (Lower.SourceFamily.pair (factory (s:=s) binding) n data) := rfl

theorem factory_next_calculation_reader :
 ((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (factory_nextSeed binding n data)).datum
  (factory_receiver binding n data)).calculationReader =
 Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
  (factory_receiver binding n data)
  ((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (factory_nextSeed binding n data)).datum
    (factory_receiver binding n data)) := rfl

theorem factory_next_calculation_some :
 Option.isSome ((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (factory_nextSeed binding n data)).datum
  (factory_receiver binding n data)).calculationReader := by
 rw [factory_next_calculation_reader]
 unfold Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
 rw [factory_receiver_pair]
 rfl

theorem factory_next_reader_raw :
 ((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (factory_nextSeed binding n data)).datum
   (factory_receiver binding n data)).calculationReader =
 some (fun {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
   (factory_receiver binding n data).registered}
   (supplied : SourceOperationInquiry.Context.Installation.Occurrence
   (factory_receiver binding n data) (current := current)) =>
   (⟨(((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (factory_nextSeed binding n data)).datum
      (factory_receiver binding n data)).reader supplied).environment,
    Expr.add (((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (factory_nextSeed binding n data)).datum
      (factory_receiver binding n data)).reader supplied).expression
    (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.eventExpression
      (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.event
        binding n data))⟩ : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
     (Value := PairValue (Lower.Value W (n+1))) (Var := X) (sort := s))) := by
 rw [factory_next_calculation_reader]
 unfold Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
 rw [factory_receiver_pair]
 rfl

theorem factory_raw (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
  (Lower.SourceFamily.cfg (factory (s:=s) binding) n seed)).raw=
 Reader.raw binding n seed (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame) :=by
 apply (congrArg (fun germ=>germ.raw)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame
   (Lower.SourceFamily.cfg (factory (s:=s) binding) n seed))).trans
 exact Profile.FiniteSource.Indexed.Installation.original_reader binding n seed
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame)

theorem factory_action_charge (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) :
  2 ≤ remaining (SourceGeneratedInquiryReceiptAction.actionReader data.1
    (Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence data.1)).expression := by
  unfold SourceGeneratedInquiryReceiptAction.actionReader
  have h := factory_calculation_reader binding n
    (⟨SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1, data.2⟩ :
      Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
  rw [h]
  unfold Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.calculationReader
  cases hp : (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1).pairInventory with
  | none =>
    simp_all [Option.getD]
    change 2 ≤ remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query data.1
      (Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2)).raw.expression
    have actual := congrArg (fun raw => remaining raw.expression)
      (factory_raw binding n data.2 data.1)
    rw [actual]
    change 2 ≤ remaining (Lower.SourceFamily.Foresight.Contextual.Reader.expression binding n data.2
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1)
      (Lower.SourceFamily.Foresight.Contextual.actualIndex n data.1))
    have charged := Lower.SourceFamily.Foresight.Contextual.Reader.source_fee binding n data.2
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1)
      (Lower.SourceFamily.Foresight.Contextual.actualIndex n data.1)
    omega
  | some tree =>
    simp_all [Option.getD]
    change 2 ≤ remaining (Expr.add
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query data.1
        (Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2)).raw.expression
      (Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.Incoming.eventExpression tree.root))
    simp only [SourceOperationExecution.remaining]
    have actual := congrArg (fun raw => remaining raw.expression)
      (factory_raw binding n data.2 data.1)
    rw [actual]
    change 2 ≤ remaining (Lower.SourceFamily.Foresight.Contextual.Reader.expression binding n data.2
        (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1)
        (Lower.SourceFamily.Foresight.Contextual.actualIndex n data.1)) + _ + 1
    have charged := Lower.SourceFamily.Foresight.Contextual.Reader.source_fee binding n data.2
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch data.1)
      (Lower.SourceFamily.Foresight.Contextual.actualIndex n data.1)
    omega

theorem factory_environment (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
  (Lower.SourceFamily.cfg (factory (s:=s) binding) n seed)).raw.environment=
 Future.Replay.Source.pairEnvironment (Future.Replay.Binding.at binding n)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame) :=
 (congrArg (fun raw=>raw.environment) (factory_raw binding n seed frame)).trans
  (Reader.raw_environment binding n seed
   (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame))

theorem factory_fee (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
  (Lower.SourceFamily.cfg (factory (s:=s) binding) n seed)).raw.expression :=
 Eq.mp (congrArg (fun raw=>2≤remaining raw.expression) (factory_raw binding n seed frame).symm)
  (le_trans (by decide : 2≤3)
   (Reader.source_fee binding n seed
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) (actualIndex n frame)))

end Lower.SourceFamily.Foresight.Contextual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
