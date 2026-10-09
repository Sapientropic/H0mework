import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Effect
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Effect
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query datum actualOccurrence actualVisit)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E
namespace C
export Lower.SourceFamily.Foresight.Contextual (factory factory_environment actualIndex)
end C
namespace P
export Lower.SourceFamily.Foresight.Paid
  (sourceEnv sourceScalar sourcePair result paidTrace generated_new_kernel environment_stock_independent Word)
end P
namespace U
export Lower.SourceFamily.Foresight.Update (decoder increment actual_environment)
end U
namespace G
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated (face)
end G
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

def packetDecoder (source : Lower.SourceFamily.Factory W X s) : Env (Lower.Value W (n+1)) X :=
  (Lower.SourceFamily.receiver source n data).environment
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.originalOccurrence
      (Lower.SourceFamily.receiver source n data).registered (Lower.SourceFamily.receiver source n data).packetAt
      (Q.actualOccurrence (Lower.SourceFamily.receiver source n data)))

theorem packet_decoder_read (source : Lower.SourceFamily.Factory W X s) : packetDecoder n data source =
    ((Q.datum data.1 (Lower.SourceFamily.cfg source n data.2)).reader
      (Q.actualOccurrence data.1.mathNext)).environment := rfl

def actualEnvironment :=
  (Q.query (Lower.SourceFamily.step (C.factory (s:=s) binding) n data).1
    (Lower.SourceFamily.cfg (C.factory (s:=s) binding) (n+1)
      (Lower.SourceFamily.step (C.factory (s:=s) binding) n data).2)).raw.environment
def actualDecoder := packetDecoder n data (C.factory (s:=s) binding)
def actualIncrement := SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1))
  (actualDecoder binding n data)-actualDecoder binding n data

theorem decoder_same_source : actualDecoder binding n data =
    U.decoder binding n data.2 data.1
      (Lower.SourceFamily.scalar (C.factory (s:=s) binding) n data)
      (Lower.SourceFamily.pair (C.factory (s:=s) binding) n data) := by
  rw [actualDecoder, packet_decoder_read]
  exact Lower.SourceFamily.Foresight.Contextual.Reader.raw_environment binding n data.2 (E.epoch data.1)
    ⟨(Q.actualVisit data.1.mathNext).current,Q.actualOccurrence data.1.mathNext⟩

theorem actual_environment : actualEnvironment binding n data =
    pairEnvironment (actualDecoder binding n data) (actualIncrement binding n data) :=
  C.factory_environment binding (n+1) (Lower.SourceFamily.nextSeed (C.factory (s:=s) binding) n data)
    (Lower.SourceFamily.receiver (C.factory (s:=s) binding) n data)

theorem source_environment : P.sourceEnv binding n data = actualEnvironment binding n data := by
  have stock := P.environment_stock_independent binding n data.2 data.1
    (P.sourceScalar binding n data) (Lower.SourceFamily.scalar (C.factory (s:=s) binding) n data)
    (P.sourcePair binding n data) (Lower.SourceFamily.pair (C.factory (s:=s) binding) n data)
  have updated := U.actual_environment binding n data.2 data.1
    (Lower.SourceFamily.scalar (C.factory (s:=s) binding) n data)
    (Lower.SourceFamily.pair (C.factory (s:=s) binding) n data)
  apply stock.trans (updated.trans _)
  have same := congrArg (fun base : Env (Lower.Value W (n+1)) X =>
    pairEnvironment base (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding (n+1)) base-base))
    (decoder_same_source binding n data).symm
  exact same.trans (actual_environment binding n data).symm

theorem actual_word (t : S) (word : Formal ℤ (Lower.Value W (n+1)) X t) :
    evaluation (R:=ℤ) (actualEnvironment binding n data) (liftMap word) =
      updateInventory (R:=ℤ) (actualDecoder binding n data) (actualIncrement binding n data) word := by
  rw [actual_environment]
  exact LinearMap.congr_fun (evaluation_liftMap (R:=ℤ) (s:=t)
    (actualDecoder binding n data) (actualIncrement binding n data)) word

theorem actual_paid_value (t : S) (word : P.Word (W:=W) (X:=X) n t) :
    (P.result binding n data t word).2.2.1 =
      evaluation (R:=ℤ) (actualEnvironment binding n data) (liftMap word) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
    ((SourceOperationExecution.Coefficients.expression_eval _ _).trans
      (congrArg (fun environment => evaluation (R:=ℤ) environment (liftMap word))
        (source_environment binding n data)))

theorem actual_new_kernel (t : S) (word : P.Word (W:=W) (X:=X) n t) :
    evaluation (R:=ℤ) (actualEnvironment binding n data)
      (relationMap (R:=ℤ) (P.sourceEnv binding n data)
        ((P.paidTrace binding n data t word).relationWords (R:=ℤ))) = 0 :=
  (congrArg (fun environment => evaluation (R:=ℤ) environment
    (relationMap (R:=ℤ) (P.sourceEnv binding n data) ((P.paidTrace binding n data t word).relationWords (R:=ℤ))))
    (source_environment binding n data).symm).trans (P.generated_new_kernel binding n data t word)

abbrev nextPacket := Lower.SourceFamily.step (C.factory (s:=s) binding) n data
abbrev jointRaw := Lower.SourceFamily.Foresight.Contextual.Inquiry.rawAt binding (n+1)
  (nextPacket binding n data).2 (E.epoch (nextPacket binding n data).1)
  (Q.actualOccurrence (nextPacket binding n data).1)
abbrev jointFace := G.face (nextPacket binding n data).2 (E.epoch (nextPacket binding n data).1)
  (Q.actualOccurrence (nextPacket binding n data).1) (jointRaw binding n data)

theorem joint_environment : (jointRaw binding n data).environment = actualEnvironment binding n data :=
  (Lower.SourceFamily.Foresight.Contextual.request_environment binding (n+1) (nextPacket binding n data).2
    (E.epoch (nextPacket binding n data).1) (C.actualIndex (n+1) (nextPacket binding n data).1)).trans
      (C.factory_environment binding (n+1) (nextPacket binding n data).2 (nextPacket binding n data).1).symm

theorem joint_word_read (word : Formal ℤ (PairValue (Lower.Value W (n+1))) X s) :
    (jointFace binding n data).freeEvaluation word =
      evaluation (R:=ℤ) (actualEnvironment binding n data) word := by
  have native : (jointFace binding n data).freeEvaluation word =
      evaluation (R:=ℤ) (jointRaw binding n data).environment word := by
    classical
    induction word using Finsupp.induction with
    | zero => exact (jointFace binding n data).freeEvaluation.map_zero
    | @single_add expression integer rest absent nonzero previous =>
        rw [map_add,map_add,freeEvaluation_single,previous]
        rw [evaluation,Finsupp.linearCombination_single]
        rfl
  exact native.trans (congrArg (fun environment => evaluation (R:=ℤ) environment word)
    (joint_environment binding n data))

theorem joint_new_kernel (word : P.Word (W:=W) (X:=X) n s) :
    (jointFace binding n data).freeEvaluation
      (relationMap (R:=ℤ) (P.sourceEnv binding n data)
        ((P.paidTrace binding n data s word).relationWords (R:=ℤ))) = 0 :=
  (joint_word_read binding n data _).trans (actual_new_kernel binding n data s word)

theorem joint_paid_value (word : P.Word (W:=W) (X:=X) n s) :
    (P.result binding n data s word).2.2.1 = (jointFace binding n data).freeEvaluation (liftMap word) :=
  (actual_paid_value binding n data s word).trans (joint_word_read binding n data _).symm

end Lower.SourceFamily.Foresight.Contextual.Effect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
