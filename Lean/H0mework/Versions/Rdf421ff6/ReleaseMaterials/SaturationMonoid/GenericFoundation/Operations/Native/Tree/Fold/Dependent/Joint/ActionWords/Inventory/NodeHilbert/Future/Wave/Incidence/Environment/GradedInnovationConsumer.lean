import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovationFactory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Completion.Consumer
import H0mework.Realization.Operations.CompleteWordDual
import H0mework.Realization.Operations.Execution.Substitution.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement SourceOperationScalarRelations SourceOperationScalarPresentation
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (AdmissionPacket stockCfg stock_action_reader nextBase nextCfg next_action_reader template nextSeed nativeAfterAdmission bornAfterNative write)
end AS
namespace D
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (packetAt packetAt_successor packetAt_successor_grade actual_index historyAt history_end_index)
end D
namespace Native
export ActualCofinalSourceAction
  (nativePacket nativeValue receipt environmentTransport packetTransport selected sourceBorn bornStock bornPairStock receiver_ast receiver_input born_inventory born_pair_inventory actual_next_packet
   old_event_in_born old_pair_event_in_born whole_paid_in_born generated_joint_in_born sourceWordAction source_word_action_in_born born_environment)
end Native
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
end S
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
  (oldPaid native_value updated_total)
end WB
namespace Request
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input expression)
end Request
namespace Completed
export SourceFamilyActualCurrentMaterialCompletedDisposition
  (completedAction completedOldRow completedBornRow consume_completed_answer completed_compiles completed_target_current completed_successor_valid)
end Completed

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K)

omit [InnerProductSpace ℂ K] in
theorem source_binding (environment : Env (Original K) X) :
    (fun target name => (sourceBinding (K:=K) target name).eval environment)=
      J.decode (environment .joint PUnit.unit) := by
  funext target name
  cases target with
  | old target => cases target <;> rfl
  | measured => rfl
  | joint => exact PEmpty.elim name

def fullDecode (value : W K .joint) : Env (W K) JointMeasured.Var :=
  fun target name =>
    ((J.decode value.1.1 target name,J.decode value.1.2 target name),
      (J.decode value.2.1 target name,J.decode value.2.2 target name))
omit [InnerProductSpace ℂ K] in
theorem full_binding (environment : Env (W K) X) :
    (fun target name => (Origin.binding (K:=K) target name).eval environment)=
      fullDecode (environment .joint PUnit.unit) := by
  funext target name
  cases target with
  | old target => cases target <;> rfl
  | measured => rfl
  | joint => exact PEmpty.elim name

omit [InnerProductSpace ℂ K] in
theorem request_origin (grade : Nat) (currentFrame : Frame (K:=K) grade) (index : Index grade currentFrame) :
    ∃ front back, (stock grade currentFrame).trace=
      front++((requests grade currentFrame).get index).sourceEvent::back ∧
      ((requests grade currentFrame).get index).position=front.length ∧
      (((requests grade currentFrame).get index).expression,((requests grade currentFrame).get index).coefficient) ∈
        SourceInventoryExecutionFeed.eventItems ((requests grade currentFrame).get index).sourceEvent :=
  SourceInventoryExecutionFeed.request_origin _ _ (List.get_mem _ index)

theorem local_physical_raw (grade : Nat) (seed : SF.Seed (W K) X .joint grade)
    (currentFrame : Frame (K:=K) grade) :
    (R.actualMaterial currentFrame (localCfg read grade seed)).raw=
      CF.codeAt (baseCode read grade (A.epoch currentFrame) (S.actualOccurrence currentFrame)) grade := rfl

def featureValue (grade : Nat) {target : J.Slot}
    (value : PairValue (L.Value (W K) grade) target) : PairValue (Original K) target :=
  CF.collapseValue (W:=Original K) 2 (CF.collapseValue (W:=W K) grade value)
def featureEnvironment (grade : Nat) (environment : Env (PairValue (L.Value (W K) grade)) X) :
    Env (PairValue (Original K)) X := fun target name => featureValue grade (environment target name)

theorem code_feature (grade : Nat) (currentFrame : Frame (K:=K) grade)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : I.Occurrence currentFrame (current:=current))
    (environment : Env (PairValue (L.Value (W K) grade)) X) :
    featureValue grade ((CF.codeAt (baseCode read grade currentFrame supplied) grade).eval environment)=
      (liftExpr ((J.expression read (columns read grade currentFrame supplied)).subst sourceBinding)).eval
        (featureEnvironment grade environment) :=
  (congrArg (CF.collapseValue (W:=Original K) 2)
    (CF.code_base_value (baseCode read grade currentFrame supplied) grade environment)).trans
      (CF.code_base_value
        (liftExpr ((J.expression read (columns read grade currentFrame supplied)).subst sourceBinding)) 2 _)

theorem code_feature_total (grade : Nat) (currentFrame : Frame (K:=K) grade)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : I.Occurrence currentFrame (current:=current))
    (environment : Env (PairValue (L.Value (W K) grade)) X) :
    let value := featureValue grade ((CF.codeAt (baseCode read grade currentFrame supplied) grade).eval environment)
    let feature := featureEnvironment grade environment
    let total := fun target name => (feature target name).1+(feature target name).2
    value.1+value.2=
      (J.expression read (columns read grade currentFrame supplied)).eval
        (J.decode (total .joint PUnit.unit)) := by
  dsimp only
  rw [code_feature]
  let expression := (J.expression read (columns read grade currentFrame supplied)).subst sourceBinding
  let feature := featureEnvironment grade environment
  let before := fun target name => (feature target name).1
  let increment := fun target name => (feature target name).2
  have lifted := eval_liftExpr expression before increment
  have total := (congrArg (fun value : PairValue (Original K) .joint => value.1+value.2) lifted).trans
    (Expr.eval_update expression before increment).symm
  exact total.trans ((Expr.eval_subst _ _ _).trans
    (congrArg (fun environment => (J.expression read (columns read grade currentFrame supplied)).eval environment)
      (source_binding (before+increment))))

def HasFreshCode (grade : Nat)
    (programme : A.Programme (PhysicalValue:=L.Value (W K) grade) (PhysicalVar:=X) (sort:=.joint))
    (sameVar : programme.LowVar=X) : Prop :=
  ∀ (currentFrame : Frame (K:=K) grade)
    {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current currentFrame.registered}
    (supplied : I.Occurrence currentFrame (current:=current)),
    (R.actionReader currentFrame (AS.stockCfg programme) supplied).expression=
      (sameVar.symm ▸ CF.codeAt (baseCode read grade (A.epoch currentFrame) supplied) grade :
        Expr (PairValue (L.Value (W K) grade)) programme.LowVar .joint)

theorem native_after_admission_fresh
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) :
    HasFreshCode read (AS.nativeAfterAdmission (factory read) packet).1
      (AS.nativeAfterAdmission (factory read) packet).2.2.1
      (AS.nativeAfterAdmission (factory read) packet).2.2.2.down := by
  rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar=X at sameVar
    cases sameVar
    change HasFreshCode read (grade+1)
      (AS.nextCfg (factory read) grade data ⟨X,datum,inventory,pairInventory⟩ rfl) rfl
    intro currentFrame current supplied
    exact (congrArg (fun raw => raw.expression)
      (AS.stock_action_reader currentFrame
        (AS.nextCfg (factory read) grade data ⟨X,datum,inventory,pairInventory⟩ rfl) supplied)).trans
      ((congrArg (fun raw => raw.expression)
        (AS.next_action_reader (factory read) grade data ⟨X,datum,inventory,pairInventory⟩ rfl currentFrame supplied)).trans rfl)

theorem born_after_native_fresh
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint))
    (generated : HasFreshCode read packet.1 packet.2.2.1 packet.2.2.2.down) :
    HasFreshCode read (AS.bornAfterNative packet).1 (AS.bornAfterNative packet).2.2.1
      (AS.bornAfterNative packet).2.2.2.down := by
  intro currentFrame current supplied
  exact (congrArg (fun raw => raw.expression)
    (AS.stock_action_reader currentFrame (AS.stockCfg packet.2.2.1) supplied)).trans
      (generated currentFrame supplied)

def RawSourceCode (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) : Prop :=
  (R.actualMaterial packet.2.1.1 packet.2.2.1).raw=
    (packet.2.2.2.down.symm ▸ CF.codeAt
      (baseCode read packet.1 (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)) packet.1 :
        Expr (PairValue (L.Value (W K) packet.1)) packet.2.2.1.LowVar .joint)

theorem raw_of_fresh (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint))
    (fresh : HasFreshCode read packet.1 packet.2.2.1 packet.2.2.2.down) : RawSourceCode read packet := by
  unfold RawSourceCode
  exact (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value:=PairValue (L.Value (W K) packet.1)) (Var:=packet.2.2.1.LowVar) (sort:=.joint) => raw.expression)
    (AS.stock_action_reader packet.2.1.1 packet.2.2.1 (S.actualOccurrence packet.2.1.1))).symm.trans
      (fresh packet.2.1.1 (S.actualOccurrence packet.2.1.1))

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] in
private theorem receipt_raw {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ target,AddCommGroup (Value target)] {sort : Sorts}
    (receiver : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value:=Value) (Var:=Var) (sort:=sort))
    (programme : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort)) :
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.atReceipt programme receiver 0).rawRead=receiver.rawRead := by
  apply Prefix.receipt_read programme receiver (fun stage => (S.frames receiver programme stage).rawRead)
  intro stage paid action
  have next : S.frames receiver programme (stage+1)=(S.frames receiver programme stage).mathNext := by
    change S.next _ _ = _
    unfold S.next
    rw [action]
  exact (congrArg (fun candidate : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
    (Value:=Value) (Var:=Var) (sort:=sort) => candidate.rawRead) next).trans rfl

theorem native_selected_raw
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) :
    (Native.selected (factory read) packet).rawRead=(Native.nativePacket (factory read) packet).2.1.1.rawRead :=
  receipt_raw (Native.nativePacket (factory read) packet).2.1.1
    (AS.stockCfg (Native.nativePacket (factory read) packet).2.2.1)

theorem native_input_value
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) :
    Native.nativeValue (factory read) packet=
      (Request.expression (R.actualMaterial packet.2.1.1 packet.2.2.1)).eval
        (Request.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment := by
  have value := SourceOperationExecutionDebt.completed_value
    (Native.selected (factory read) packet).event.state (Native.receipt (factory read) packet).2.1
  change Native.nativeValue (factory read) packet=
    (Native.selected (factory read) packet).rawRead.expression.eval
      (Native.selected (factory read) packet).rawRead.environment at value
  rw [native_selected_raw] at value
  exact value

theorem native_updated_total
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) :
    WB.oldPaid packet.2.1.1 packet.2.2.1+Native.nativeValue (factory read) packet=
      (R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
        (Request.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment :=
  (congrArg (fun value => WB.oldPaid packet.2.1.1 packet.2.2.1+value)
    ((native_input_value read packet).trans
      (WB.native_value packet.2.1.1 packet.2.2.1
        (AS.write (factory read) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)).symm)).trans
    (WB.updated_total packet.2.1.1 packet.2.2.1
      (AS.write (factory read) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down))

theorem born_stock_read
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) :
    HEq (stock (Native.packetTransport packet.2.2.2.down (Native.sourceBorn (factory read) packet)).1
      (Native.packetTransport packet.2.2.2.down (Native.sourceBorn (factory read) packet)).2.1.1)
      (T.preserve (Native.sourceBorn (factory read) packet).2.1.1.inventory
        (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
          (Native.sourceBorn (factory read) packet).2.1.1.rawRead.expression))) := by
  rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
      change lowVar=X at sameVar
      cases sameVar
      dsimp only [Native.packetTransport]
      exact HEq.rfl

theorem born_joint_written
    (packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint)) :
    HEq ((Native.packetTransport packet.2.2.2.down (Native.sourceBorn (factory read) packet)).2.1.1.activeEnvironment
      .joint PUnit.unit)
      (SourceGeneratedInquiryReceiptAction.Configured.Writeback.oldPaid packet.2.1.1 packet.2.2.1+
        Native.nativeValue (factory read) packet) := by
  rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
      change lowVar=X at sameVar
      cases sameVar
      have written := Native.born_environment (factory read)
        (⟨grade,data,⟨X,datum,inventory,pairInventory⟩,⟨rfl⟩⟩ : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint))
      have coordinate := congrArg (fun environment : Env (PairValue (L.Value (W K) grade)) X =>
        environment .joint PUnit.unit) written
      simp only [AS.write] at coordinate
      simp only [dif_pos True.intro] at coordinate
      dsimp only [Native.packetTransport,id]
      change HEq
        ((Native.sourceBorn (factory read)
          (⟨grade,data,⟨X,datum,inventory,pairInventory⟩,⟨rfl⟩⟩ : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint))).2.1.1.activeEnvironment .joint PUnit.unit) _
      exact heq_of_eq coordinate

namespace Integrated
variable (sourceFrame : JointMeasured.Frame (K:=K))
abbrev initial := Origin.initial read sourceFrame
abbrev firstCfg := Origin.firstCfg read sourceFrame
abbrev site (ordinal : Nat) := D.packetAt (factory read) (initial read sourceFrame) (firstCfg read sourceFrame) rfl ordinal

theorem origin_is_actual_canonical_next :
    (SourceGeneratedInquiryReceiptAction.generatedAction
      (Origin.paidFrame read sourceFrame) (Origin.paidCfg read sourceFrame)).target.targetAnswerAndNext.nextCurrent=
      ⟨_,(initial read sourceFrame).old.root.toAuthoritativeRoot,(initial read sourceFrame).old.visit⟩ :=
  SourceGeneratedInquiryReceiptAction.literal_next (Origin.paidFrame read sourceFrame) (Origin.paidCfg read sourceFrame)

theorem origin_joint_is_paid : (initial read sourceFrame).activeEnvironment .joint PUnit.unit=
    (SourceGeneratedInquiryReceiptAction.actionResultAt
      (Origin.paidFrame read sourceFrame) (Origin.paidCfg read sourceFrame)
      (S.actualOccurrence (Origin.paidFrame read sourceFrame))).2.2.1 := rfl

theorem cofinal_fresh (ordinal : Nat) :
    let packet := site read sourceFrame ordinal
    HasFreshCode read packet.1 packet.2.2.1 packet.2.2.2.down := by
  cases ordinal with
  | zero =>
      change HasFreshCode read 0 (firstCfg read sourceFrame) rfl
      unfold HasFreshCode
      intro currentFrame current supplied
      rfl
  | succ ordinal =>
      dsimp only [site]
      rw [D.packetAt_successor]
      exact born_after_native_fresh read _ (native_after_admission_fresh read _)

theorem actual_physical_raw (ordinal : Nat) : RawSourceCode read (site read sourceFrame ordinal) :=
  raw_of_fresh read (site read sourceFrame ordinal) (cofinal_fresh read sourceFrame ordinal)

abbrev native (ordinal : Nat) := Native.nativePacket (factory read) (site read sourceFrame ordinal)
abbrev selected (ordinal : Nat) := Native.selected (factory read) (site read sourceFrame ordinal)
abbrev born (ordinal : Nat) := Native.sourceBorn (factory read) (site read sourceFrame ordinal)

theorem receiver_has_fresh_source (ordinal : Nat) :
    (native read sourceFrame ordinal).2.1.1.registered.input.expression=
      RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
        (R.actualMaterial (site read sourceFrame ordinal).2.1.1 (site read sourceFrame ordinal).2.2.1) :=
  Native.receiver_ast (factory read) _

theorem next_packet_is_actual (ordinal : Nat) : type_of% (Native.actual_next_packet
    (factory read) (initial read sourceFrame) (firstCfg read sourceFrame) rfl ordinal) :=
  Native.actual_next_packet (factory read) (initial read sourceFrame) (firstCfg read sourceFrame) rfl ordinal
theorem next_inventory_is_actual (ordinal : Nat) : type_of% (Native.born_inventory
    (factory read) (site read sourceFrame ordinal)) :=
  Native.born_inventory (factory read) (site read sourceFrame ordinal)
theorem next_pair_inventory_is_actual (ordinal : Nat) : type_of% (Native.born_pair_inventory
    (factory read) (site read sourceFrame ordinal)) :=
  Native.born_pair_inventory (factory read) (site read sourceFrame ordinal)

theorem next_stock_from_actual_born (ordinal : Nat) :
    HEq (stock (site read sourceFrame (ordinal+1)).1 (site read sourceFrame (ordinal+1)).2.1.1)
      (T.preserve (born read sourceFrame ordinal).2.1.1.inventory
        (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
          (born read sourceFrame ordinal).2.1.1.rawRead.expression))) := by
  rw [show site read sourceFrame (ordinal+1)=_ from next_packet_is_actual read sourceFrame ordinal]
  exact born_stock_read read (site read sourceFrame ordinal)

theorem next_joint_is_actual (ordinal : Nat) :
    HEq ((site read sourceFrame (ordinal+1)).2.1.1.activeEnvironment .joint PUnit.unit)
      (SourceGeneratedInquiryReceiptAction.Configured.Writeback.oldPaid
        (site read sourceFrame ordinal).2.1.1 (site read sourceFrame ordinal).2.2.1+
        Native.nativeValue (factory read) (site read sourceFrame ordinal)) := by
  rw [show site read sourceFrame (ordinal+1)=_ from next_packet_is_actual read sourceFrame ordinal]
  exact born_joint_written read (site read sourceFrame ordinal)

theorem born_fresh_vector (ordinal : Nat) :
    let packet := site read sourceFrame ordinal
    let output := featureValue packet.1
      (WB.oldPaid packet.2.1.1 packet.2.2.1+Native.nativeValue (factory read) packet)
    let environment := Native.environmentTransport packet.2.2.2.down
      (Request.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment
    let feature := featureEnvironment packet.1 environment
    let total := fun target name => (feature target name).1+(feature target name).2
    let decoded := J.decode (total .joint PUnit.unit)
    let source := columns read packet.1 (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)
    output.1+output.2=
      (PaidSourceMacroHistory.programme.eval (JointMeasured.oldEnvironment decoded),
        FG.innovationCLM source ((JointMeasured.inputTerm read).eval decoded)) := by
  have fresh := cofinal_fresh read sourceFrame ordinal
  generalize packetEq : site read sourceFrame ordinal=packet at fresh ⊢
  rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
      change lowVar=X at sameVar
      cases sameVar
      let programme : A.Programme (PhysicalValue:=L.Value (W K) grade) (PhysicalVar:=X) (sort:=.joint) :=
        ⟨X,datum,inventory,pairInventory⟩
      let packet : AS.AdmissionPacket (W:=W K) (X:=X) (s:=.joint) := ⟨grade,data,programme,⟨rfl⟩⟩
      let material := R.actualMaterial data.1 programme
      let environment := (Request.input material).environment
      have code : material.raw=
          CF.codeAt (baseCode read grade (A.epoch data.1) (S.actualOccurrence data.1)) grade :=
        raw_of_fresh read packet fresh
      have updated := congrArg (fun value : PairValue (L.Value (W K) grade) .joint =>
        (featureValue grade value).1+(featureValue grade value).2) (native_updated_total read packet)
      have sourceRead := congrArg (fun expression : Expr (PairValue (L.Value (W K) grade)) X .joint =>
        let value := featureValue grade (expression.eval environment)
        value.1+value.2) code
      have vector := (code_feature_total read grade (A.epoch data.1) (S.actualOccurrence data.1) environment).trans
        (JointMeasured.expression_value _ _ _)
      exact updated.trans (sourceRead.trans vector)

def wholeWordRecovery (ordinal : Nat) :=
  SourceGeneratedCompleteWordDual.coimageRecovery
    (Index:=Expr (L.Value (W K) (site read sourceFrame ordinal).1) X .joint)
theorem whole_word_inverse (ordinal : Nat)
    (word : Formal ℤ (L.Value (W K) (site read sourceFrame ordinal).1) X .joint) :
    wholeWordRecovery read sourceFrame ordinal
      (SourceGeneratedPerfectification.canonicalMap SourceGeneratedCompleteWordDual.pairing word)=word :=
  SourceGeneratedCompleteWordDual.recovery_source word

def completed (ordinal : Nat) :=
  Completed.consume_completed_answer (selected read sourceFrame ordinal) (native read sourceFrame ordinal).2.2.1
    (fun generated _answer _receipt _compiled _next _valid _whole => generated)
theorem completed_whole (ordinal : Nat) : type_of% (completed read sourceFrame ordinal).target.firstDestination_heq :=
  (completed read sourceFrame ordinal).target.firstDestination_heq
theorem completed_next (ordinal : Nat) : type_of% (Completed.completed_target_current
    (selected read sourceFrame ordinal) (native read sourceFrame ordinal).2.2.1) :=
  Completed.completed_target_current (selected read sourceFrame ordinal) (native read sourceFrame ordinal).2.2.1

def actual_graded_innovation_next (ordinal : Nat) :=
  (Origin.material read sourceFrame,
    (⟨origin_is_actual_canonical_next read sourceFrame⟩ : PLift (_)),
    (⟨origin_joint_is_paid read sourceFrame⟩ : PLift (_)),
    (site read sourceFrame ordinal).2.1.1,
    (R.actualMaterial (site read sourceFrame ordinal).2.1.1 (site read sourceFrame ordinal).2.2.1),
    (⟨actual_physical_raw read sourceFrame ordinal⟩ : PLift (_)),
    (⟨receiver_has_fresh_source read sourceFrame ordinal⟩ : PLift (_)),
    (⟨next_packet_is_actual read sourceFrame ordinal⟩ : PLift (_)),
    (⟨next_inventory_is_actual read sourceFrame ordinal⟩ : PLift (_)),
    (⟨next_pair_inventory_is_actual read sourceFrame ordinal⟩ : PLift (_)),
    (⟨next_stock_from_actual_born read sourceFrame ordinal⟩ : PLift (_)),
    (⟨next_joint_is_actual read sourceFrame ordinal⟩ : PLift (_)),
    (⟨born_fresh_vector read sourceFrame ordinal⟩ : PLift (_)),
    (⟨actual_physical_raw read sourceFrame (ordinal+1)⟩ : PLift (_)),
    Native.sourceWordAction (site read sourceFrame ordinal),
    wholeWordRecovery read sourceFrame ordinal,
    completed read sourceFrame ordinal)
end Integrated

namespace Actual
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)
variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
variable (word : PaidSourceMacroHistory.Word.{u}) (stage cut offset ordinal : Nat)
abbrev actual_graded_innovation_next := Integrated.actual_graded_innovation_next
  (JointMeasured.Actual.actualRead root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter cut)
  (JointMeasured.Actual.frameAt root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter word stage cut offset)
  ordinal
end Actual
end PaidSourceContentEnvironment.GradedInnovation
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
