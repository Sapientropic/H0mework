import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local instance] levelGroups
variable {W X : PUnit.{u+1} → Type u} [∀ t, AddCommGroup (W t)]
variable (factory : SF.Factory W X PUnit.unit) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : sourceCfg.LowVar = X)

abbrev action := Admission.generatedAction data.1 sourceCfg
  (scalar factory n data sourceCfg language) (pair factory n data sourceCfg language)
  (nextCfg factory n data sourceCfg language)

theorem actual_compiles : type_of% (Admission.compiles data.1 sourceCfg
    (scalar factory n data sourceCfg language) (pair factory n data sourceCfg language)
    (nextCfg factory n data sourceCfg language)) :=
  Admission.compiles data.1 sourceCfg (scalar factory n data sourceCfg language)
    (pair factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
theorem actual_whole : type_of% (action factory n data sourceCfg language).target.firstDestination_heq :=
  (action factory n data sourceCfg language).target.firstDestination_heq
theorem actual_next : type_of% (Admission.target_current data.1 sourceCfg
    (scalar factory n data sourceCfg language) (pair factory n data sourceCfg language)
    (nextCfg factory n data sourceCfg language) (Admission.sourceEvent data.1 sourceCfg)) :=
  Admission.target_current data.1 sourceCfg (scalar factory n data sourceCfg language)
    (pair factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
    (Admission.sourceEvent data.1 sourceCfg)
theorem actual_target_root : type_of% (Admission.target_root data.1 sourceCfg
    (scalar factory n data sourceCfg language) (pair factory n data sourceCfg language)
    (nextCfg factory n data sourceCfg language) (Admission.sourceEvent data.1 sourceCfg)) :=
  Admission.target_root data.1 sourceCfg (scalar factory n data sourceCfg language)
    (pair factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
    (Admission.sourceEvent data.1 sourceCfg)
theorem calculation_target_root : type_of% (B.original_target_root data.1 sourceCfg
    (scalar factory n data sourceCfg language) (pair factory n data sourceCfg language)
    (nextCfg factory n data sourceCfg language) (SourceGeneratedInquiryReceiptAction.sourceEvent data.1 sourceCfg)) :=
  B.original_target_root data.1 sourceCfg (scalar factory n data sourceCfg language)
    (pair factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
    (SourceGeneratedInquiryReceiptAction.sourceEvent data.1 sourceCfg)

theorem target_first_source (event : SourceGeneratedInquiryReceiptAction.Configured.Event data.1 sourceCfg) : HEq
    (Admission.targetAt data.1 sourceCfg (scalar factory n data sourceCfg language)
      (pair factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
      event).firstSuccessor
    (B.originalTargetAt data.1 sourceCfg (scalar factory n data sourceCfg language)
      (pair factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
      event).firstSuccessor := HEq.rfl

theorem installed_decoder :
    (S.datum (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)).nextEnvironmentReadAt =
      ((WB.programme data.1 sourceCfg (write n sourceCfg)).datum
        (A.epoch (receiver factory n data sourceCfg language))).nextEnvironmentReadAt := rfl
theorem receiver_inventories :
    (receiver factory n data sourceCfg language).inventory = some (scalar factory n data sourceCfg language) ∧
    (receiver factory n data sourceCfg language).pairInventory = some (pair factory n data sourceCfg language) := ⟨rfl, rfl⟩

abbrev receipt := Complete.receipt (nextCfg factory n data sourceCfg language)
  (receiver factory n data sourceCfg language) 0
abbrev selected := Complete.atReceipt (nextCfg factory n data sourceCfg language)
  (receiver factory n data sourceCfg language) 0
def nativeValue : PairValue (L.Value W n) PUnit.unit := (receipt factory n data sourceCfg language).2.1.1
abbrev born := S.nextBorn (selected factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)

theorem selected_raw : (selected factory n data sourceCfg language).rawRead =
    (receiver factory n data sourceCfg language).rawRead := by
  apply Prefix.receipt_read (nextCfg factory n data sourceCfg language) (receiver factory n data sourceCfg language)
    (fun stage => (S.frames (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) stage).rawRead)
  intro stage paid actual
  have next : S.frames (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) (stage + 1) =
      (S.frames (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) stage).mathNext := by
    change S.next _ _ = _
    unfold S.next
    rw [actual]
  exact (congrArg (fun candidate : A.M.Frame (Value := PairValue (L.Value W n))
    (Var := sourceCfg.LowVar) (sort := PUnit.unit) => candidate.rawRead) next).trans rfl

theorem native_value : nativeValue factory n data sourceCfg language =
    (N.expression (sourceMaterial n data sourceCfg)).eval (N.input (sourceMaterial n data sourceCfg)).environment := by
  have paid := SourceOperationExecutionDebt.completed_value
    (selected factory n data sourceCfg language).event.state (receipt factory n data sourceCfg language).2.1
  change nativeValue factory n data sourceCfg language =
    (selected factory n data sourceCfg language).rawRead.expression.eval
      (selected factory n data sourceCfg language).rawRead.environment at paid
  rw [selected_raw] at paid
  exact paid

theorem updated_total : oldPair n data sourceCfg + nativeValue factory n data sourceCfg language =
    (sourceMaterial n data sourceCfg).raw.eval (N.input (sourceMaterial n data sourceCfg)).environment := by
  have same : nativeValue factory n data sourceCfg language = WB.nativeValue data.1 sourceCfg (write n sourceCfg) :=
    (native_value factory n data sourceCfg language).trans (WB.native_value data.1 sourceCfg (write n sourceCfg)).symm
  exact (congrArg (fun value => oldPair n data sourceCfg + value) same).trans
    (WB.updated_total data.1 sourceCfg (write n sourceCfg))

theorem born_environment : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
    (born factory n data sourceCfg language)
    (write n sourceCfg (oldPair n data sourceCfg + nativeValue factory n data sourceCfg language)) := by
  intro current occurrence
  change write n sourceCfg (oldPair n data sourceCfg +
    WB.nativeAt sourceCfg (A.epoch (selected factory n data sourceCfg language))
      (S.actualOccurrence (selected factory n data sourceCfg language))) = _
  change write n sourceCfg (oldPair n data sourceCfg + WB.nativeEventValue
    (S.actualVisit (selected factory n data sourceCfg language)).current.2) = _
  have eventEq : (S.actualVisit (selected factory n data sourceCfg language)).current.2 =
      (selected factory n data sourceCfg language).event := rfl
  have same := congrArg WB.nativeEventValue eventEq
  have actual : WB.nativeEventValue (selected factory n data sourceCfg language).event =
      nativeValue factory n data sourceCfg language := by
    unfold SourceGeneratedInquiryReceiptAction.Configured.Writeback.nativeEventValue
    have chosen := (receipt factory n data sourceCfg language).2.2.2
    dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.action] at chosen
    rw [chosen]
    rfl
  exact congrArg (fun value => write n sourceCfg (oldPair n data sourceCfg + value)) (same.trans actual)

theorem actual_writeback : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
    (born factory n data sourceCfg language)
    (write n sourceCfg ((sourceMaterial n data sourceCfg).raw.eval
      (N.input (sourceMaterial n data sourceCfg)).environment)) := by
  intro current occurrence
  exact ((born_environment factory n data sourceCfg language) occurrence).trans
    (congrArg (write n sourceCfg) (updated_total factory n data sourceCfg language))

theorem frames_born : S.frames (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
    ((receipt factory n data sourceCfg language).1 + 1) = born factory n data sourceCfg language := by
  have actual := (receipt factory n data sourceCfg language).2.2.2
  have same : S.frames (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
      ((0 + (receipt factory n data sourceCfg language).1) + 1) = born factory n data sourceCfg language := by
    change S.next (S.frames (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
      (0 + (receipt factory n data sourceCfg language).1)) (nextCfg factory n data sourceCfg language) = _
    unfold S.next
    rw [actual]
  simpa only [Nat.zero_add] using same

theorem full_frame : NF.read (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
    ((S.runtime (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)).stateAt
      ((receipt factory n data sourceCfg language).1 + 1)) = born factory n data sourceCfg language :=
  (NF.actual (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language)
    ((receipt factory n data sourceCfg language).1 + 1)).trans (frames_born factory n data sourceCfg language)

theorem born_inventories :
    (born factory n data sourceCfg language).inventory = (template factory n data sourceCfg language).nextInventory
      (selected factory n data sourceCfg language) ∧
    (born factory n data sourceCfg language).pairInventory = (template factory n data sourceCfg language).nextPairInventory
      (selected factory n data sourceCfg language) := ⟨rfl, rfl⟩

def successorSeed := SourceHistoryCommon.seed (seed factory n data sourceCfg language)
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
    (born factory n data sourceCfg language).registered.input.expression))
def successorPacket : SF.Packet (W := W) (X := sourceCfg.LowVar) (s := PUnit.unit) (n + 1) :=
  ⟨born factory n data sourceCfg language, successorSeed factory n data sourceCfg language⟩
theorem successor_registered_present :
    PresentedRelationEventAt.generator (born factory n data sourceCfg language).registered.input.expression ∈
      (successorSeed factory n data sourceCfg language).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 _ List.mem_cons_self
abbrev successorOldPaid := WB.oldPaid (successorPacket factory n data sourceCfg language).1
  (nextCfg factory n data sourceCfg language)

def secondNextCfg := nextCfg (nextFactory factory n sourceCfg language) (n + 1)
  (successorPacket factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) (by rfl)

theorem second_decoder : type_of% (decoder_source (nextFactory factory n sourceCfg language) (n + 1)
    (successorPacket factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) (by rfl)
    (receiver (nextFactory factory n sourceCfg language) (n + 1) (successorPacket factory n data sourceCfg language)
      (nextCfg factory n data sourceCfg language) (by rfl))) :=
  decoder_source (nextFactory factory n sourceCfg language) (n + 1)
    (successorPacket factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) (by rfl)
    (receiver (nextFactory factory n sourceCfg language) (n + 1) (successorPacket factory n data sourceCfg language)
      (nextCfg factory n data sourceCfg language) (by rfl))

theorem second_writeback : type_of% (@actual_writeback _ _ _ (nextFactory factory n sourceCfg language) (n + 1)
    (successorPacket factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) (by rfl)) :=
  @actual_writeback _ _ _ (nextFactory factory n sourceCfg language) (n + 1)
    (successorPacket factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) (by rfl)

def cofinal (bound : Nat) := Births.cover (nextCfg factory n data sourceCfg language)
  (receiver factory n data sourceCfg language) bound

theorem complete_word (word : SourceOperationInquiry.Carrier
    (S.runtime (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language))) :
    type_of% (NF.fullword_read (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) word) :=
  NF.fullword_read (receiver factory n data sourceCfg language) (nextCfg factory n data sourceCfg language) word

end SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
