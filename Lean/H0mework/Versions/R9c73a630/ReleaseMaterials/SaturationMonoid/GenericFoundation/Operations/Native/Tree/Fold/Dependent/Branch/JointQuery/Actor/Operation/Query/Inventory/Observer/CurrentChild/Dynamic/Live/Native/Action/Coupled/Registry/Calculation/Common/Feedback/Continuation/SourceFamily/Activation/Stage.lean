import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} (W : Sorts → Type u) [∀ target, AddCommGroup (W target)]
local instance levelStageGroups (n : Nat) (target : Sorts) : AddCommGroup (Lower.Value W n target) := Lower.groups W n target
variable (X : Sorts → Type u) (s : Sorts)
private inductive Stage where
 | admission (grade : Nat) (data : SF.Packet (W := W) (X := X) (s := s) grade)
   (cfg : A.Programme (PhysicalValue := Lower.Value W grade) (PhysicalVar := X) (sort := s))
   (language : cfg.LowVar = X)
 | continuation (grade : Nat) (data : SF.Packet (W := W) (X := X) (s := s) grade)
   (base : A.Programme (PhysicalValue := Lower.Value W grade) (PhysicalVar := X) (sort := s))
   (language : base.LowVar = X)
variable {W X s}
private def transport {Y Z : Sorts → Type u} (same : Y = Z) : Stage W Y s → Stage W Z s := by
 cases same
 exact id
variable (factory : SF.Factory W X s)
private def presented : Stage W X s → RootInquiryStatePresentation
 | .admission n data cfg language => SA.presentation data.1 cfg
   (scalar factory n data cfg language) (pair factory n data cfg language) (nextCfg factory n data cfg language)
 | .continuation _ data base _language => ST.presentation data.1 (stockCfg base)
private def selectedQuery : (stage : Stage W X s) → (presented factory stage).Query
 | .admission _ data cfg _ => SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.query data.1 cfg
 | .continuation _ data base _ => SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.query data.1 (stockCfg base)
private theorem query_unique (stage : Stage W X s) (candidate : (presented factory stage).Query) :
 candidate = selectedQuery factory stage := by
 cases stage with
 | admission n data cfg language => exact SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique data.1 cfg candidate
 | continuation n data base language => exact SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique data.1 (stockCfg base) candidate

private def advance : Stage W X s → Stage W X s
 | .admission n data cfg language => transport language
   (.continuation (n+1) ⟨receiver factory n data cfg language,nextSeed factory n data cfg language⟩
    (nextBase factory n data cfg language) rfl)
 | .continuation n data base language =>
   match data.1.action with
   | .inr _paid => .continuation n ⟨data.1.mathNext,data.2⟩ base language
   | .inl _settled =>
      let born := S.nextBorn data.1 (stockCfg base)
      .admission n ⟨born,SourceHistoryCommon.seed data.2
        (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator born.registered.input.expression))⟩
        (stockCfg base) language

private theorem presented_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (targetFactory : SF.Factory W Z s) (stage : Stage W Y s) :
 (presented targetFactory (transport same stage)).erase =
 (presented (same.symm ▸ targetFactory) stage).erase := by
 cases same
 rfl

namespace SA
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
 (compiles sourceEvent)
end SA
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (birthProgram target_current target_root)
end ST

private theorem presented_transport_full {Y Z : Sorts → Type u} (same : Y = Z)
 (targetFactory : SF.Factory W Z s) (stage : Stage W Y s) :
 presented targetFactory (transport same stage) = presented (same.symm ▸ targetFactory) stage := by
 cases same
 rfl
private theorem root_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (targetFactory : SF.Factory W Z s) (stage : Stage W Y s) :
 HEq (presented targetFactory (transport same stage)).state.base.root
  (presented (same.symm ▸ targetFactory) stage).state.base.root := by
 cases same
 rfl

private theorem advance_valid (current : Stage W X s) (candidate : (presented factory current).Query) :
 (presented factory (advance factory current)).erase =
  (RootInquiryProcessNode.answered (presented factory current) candidate).erase ∧
 (.active (presented factory current) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt candidate
  (.active (presented factory (advance factory current))) := by
 cases query_unique factory current candidate
 cases current with
 | admission n data cfg language =>
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid
   (presented factory (.admission n data cfg language))
   (presented factory (advance factory (.admission n data cfg language)))
   (selectedQuery factory (.admission n data cfg language))
   (SA.generatedAction data.1 cfg (scalar factory n data cfg language) (pair factory n data cfg language)
    (nextCfg factory n data cfg language))
   (SA.compiles data.1 cfg (scalar factory n data cfg language) (pair factory n data cfg language)
    (nextCfg factory n data cfg language))
  · exact (presented_transport language factory
      (.continuation (n+1) ⟨receiver factory n data cfg language,nextSeed factory n data cfg language⟩
       (nextBase factory n data cfg language) rfl)).trans
     (SA.target_erasure data.1 cfg (scalar factory n data cfg language) (pair factory n data cfg language)
      (nextCfg factory n data cfg language))
  · exact (root_transport language factory
      (.continuation (n+1) ⟨receiver factory n data cfg language,nextSeed factory n data cfg language⟩
       (nextBase factory n data cfg language) rfl)).trans
     (SA.target_full_root data.1 cfg (scalar factory n data cfg language) (pair factory n data cfg language)
      (nextCfg factory n data cfg language))
 | continuation n data base language =>
  cases actual : data.1.action with
  | inr paid =>
   have valid := ST.successor_valid data.1 (stockCfg base)
    (selectedQuery factory (.continuation n data base language))
   simpa only [advance,actual,presented,S.next] using valid
  | inl settled =>
   apply RootInquiryProcessNode.active_debtAdmission_successor_valid
    (presented factory (.continuation n data base language))
    (presented factory (advance factory (.continuation n data base language)))
    (selectedQuery factory (.continuation n data base language))
    ((ST.birthProgram data.1 (stockCfg base)).generate
     ((SO.root data.1 (stockCfg base)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation.visit data.1 (stockCfg base))))
    (ST.compiles_settled data.1 (stockCfg base) settled actual)
   · simp only [advance,actual]
     apply congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent.{u}))
     exact (ST.target_current data.1 (stockCfg base) _).symm
   · dsimp only [advance]
     rw [actual]
     change HEq (SO.root (S.nextBorn data.1 (stockCfg base)) (stockCfg base)) _
     exact heq_of_eq (ST.target_root data.1 (stockCfg base) _).symm

private def sourceCurrent : Stage W X s → AnyAuthoritativeRootCurrent.{u}
 | .admission _ data cfg _ => SO.current data.1 cfg
 | .continuation _ data base _ => SO.current data.1 (stockCfg base)
private def rawShape : Stage W X s → SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Shape
 | .admission _ data _ _ | .continuation _ data _ _ => SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.shape data.1.rawRead.expression
private def sourceRank : Stage W X s → Nat × Nat
 | .admission _ data _ _ | .continuation _ data _ _ => (Lower.Stock.size data.1,data.1.depth+1)
private theorem rank_transport {Y Z : Sorts → Type u} (same : Y = Z) (stage : Stage W Y s) :
 sourceRank (transport same stage) = sourceRank stage := by cases same; rfl
private theorem presented_current (stage : Stage W X s) : (presented factory stage).erase = sourceCurrent stage := by
 cases stage <;> rfl
private theorem current_stock (stage : Stage W X s) :
 RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation (sourceCurrent stage) =
 ⟨ULift.{u} (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Shape × Nat),
  ULift.up (rawShape stage,(sourceRank stage).1)⟩ := by cases stage <;> rfl
private theorem current_depth (stage : Stage W X s) :
 RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.erasedDepth (sourceCurrent stage) =
  (sourceRank stage).2 := by
 cases stage with
 | admission n data cfg language => exact SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.depth_source data.1 cfg
 | continuation n data base language => exact SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.depth_source data.1 (stockCfg base)
private theorem rank_of_current (first second : Stage W X s)
 (same : (presented factory first).erase = (presented factory second).erase) :
 sourceRank first = sourceRank second := by
 rw [presented_current,presented_current] at same
 apply Prod.ext
 · have reads := congrArg RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.observation same
   rw [current_stock,current_stock] at reads
   exact congrArg Prod.snd (congrArg ULift.down (eq_of_heq (Sigma.mk.inj reads).2))
 · exact (current_depth first).symm.trans
    ((congrArg RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.erasedDepth same).trans
     (current_depth second))
private theorem advance_progress (stage : Stage W X s) :
 RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Before
  (sourceRank stage) (sourceRank (advance factory stage)) := by
 cases stage with
 | admission n data cfg language =>
  change _ ∨ _
  left
  unfold advance
  rw [rank_transport]
  exact receiver_stock_grows factory n data cfg language
 | continuation n data base language =>
  cases actual : data.1.action with
  | inr paid =>
   change _ ∨ _
   right
   simp only [advance,actual]
   exact ⟨rfl,Nat.lt_succ_self _⟩
  | inl settled =>
   change _ ∨ _
   left
   simp only [advance,actual]
   exact birth_stock_grows data.1 base

variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (firstCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : firstCfg.LowVar = X)
private def first : Stage W X s := .admission 0
 ⟨initial,RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator initial.registered.input.expression)⟩ firstCfg language
private def stageAt : Nat → Stage W X s := Nat.rec (first initial firstCfg language) (fun _ current => advance factory current)
def presentationAt (count : Nat) := presented factory (stageAt factory initial firstCfg language count)
def queryAt (count : Nat) : (presentationAt factory initial firstCfg language count).Query :=
 selectedQuery factory (stageAt factory initial firstCfg language count)
theorem queryAt_unique (count : Nat) (candidate : (presentationAt factory initial firstCfg language count).Query) :
 candidate = queryAt factory initial firstCfg language count := query_unique factory _ candidate

theorem successor_valid (count : Nat) (candidate : (presentationAt factory initial firstCfg language count).Query) :
 (presentationAt factory initial firstCfg language (count+1)).erase =
  (RootInquiryProcessNode.answered (presentationAt factory initial firstCfg language count) candidate).erase ∧
 (.active (presentationAt factory initial firstCfg language count) : RootInquiryProcessNode).PreservesGeneratedLivingLawAt
  candidate (.active (presentationAt factory initial firstCfg language (count+1))) :=
 advance_valid factory _ candidate

private theorem stages_forward (first distance : Nat) :
 RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Before
  (sourceRank (stageAt factory initial firstCfg language first))
  (sourceRank (stageAt factory initial firstCfg language (first+distance+1))) := by
 induction distance with
 | zero => exact advance_progress factory _
 | succ distance previous =>
  apply RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.before_trans previous
  have actual := advance_progress factory (stageAt factory initial firstCfg language (first+distance+1))
  change RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.Before
   (sourceRank (stageAt factory initial firstCfg language (first+distance+1)))
   (sourceRank (stageAt factory initial firstCfg language ((first+distance+1)+1))) at actual
  simpa only [Nat.add_assoc] using actual

theorem erasure_injective : Function.Injective
 (fun count => (presentationAt factory initial firstCfg language count).erase) := by
 intro first second same
 have ranks := rank_of_current factory (stageAt factory initial firstCfg language first)
  (stageAt factory initial firstCfg language second) same
 rcases lt_trichotomy first second with less | equal | greater
 · obtain ⟨distance,index⟩ := Nat.exists_eq_add_of_lt less
   have progress := stages_forward factory initial firstCfg language first distance
   rw [←index,ranks] at progress
   exact False.elim (RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.before_irrefl _ progress)
 · exact equal
 · obtain ⟨distance,index⟩ := Nat.exists_eq_add_of_lt greater
   have progress := stages_forward factory initial firstCfg language second distance
   rw [←index,ranks] at progress
   exact False.elim (RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation.before_irrefl _ progress)

abbrev firstData : SF.Packet (W := W) (X := X) (s := s) 0 :=
 ⟨initial,RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator initial.registered.input.expression)⟩
abbrev firstReceiver := receiver factory 0 (firstData initial) firstCfg language
abbrev firstSeed := nextSeed factory 0 (firstData initial) firstCfg language
abbrev firstBase := nextBase factory 0 (firstData initial) firstCfg language
abbrev firstProgramme := nextCfg factory 0 (firstData initial) firstCfg language

theorem first_presentation_full : presentationAt factory initial firstCfg language 0 =
 SA.presentation initial firstCfg (scalar factory 0 (firstData initial) firstCfg language)
  (pair factory 0 (firstData initial) firstCfg language) (firstProgramme factory initial firstCfg language) := rfl

theorem first_target_full : presentationAt factory initial firstCfg language 1 =
 SA.targetPresentation initial firstCfg (scalar factory 0 (firstData initial) firstCfg language)
  (pair factory 0 (firstData initial) firstCfg language) (firstProgramme factory initial firstCfg language) :=
 presented_transport_full language factory (.continuation 1
  ⟨firstReceiver factory initial firstCfg language,firstSeed factory initial firstCfg language⟩
  (firstBase factory initial firstCfg language) rfl)

namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_paid_prefix)
end Prefix
namespace Steps
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames)
end Steps
abbrev firstReceiptRaw := Complete.receipt (firstProgramme factory initial firstCfg language)
 (firstReceiver factory initial firstCfg language) 0
def firstReceipt : Σ distance : Nat,
 { settled : SourceOperationExecutionDebt.Settlement
    (Steps.frames (firstReceiver factory initial firstCfg language) (firstProgramme factory initial firstCfg language) distance).event.state //
   distance ≤ remaining (firstReceiver factory initial firstCfg language).event.state.1 ∧
    (Steps.frames (firstReceiver factory initial firstCfg language) (firstProgramme factory initial firstCfg language) distance).action = .inl settled } :=
 let actual := firstReceiptRaw factory initial firstCfg language
 ⟨actual.1,Eq.mp (congrArg (fun index =>
   { settled : SourceOperationExecutionDebt.Settlement
      (Steps.frames (firstReceiver factory initial firstCfg language) (firstProgramme factory initial firstCfg language) index).event.state //
    actual.1 ≤ remaining (firstReceiver factory initial firstCfg language).event.state.1 ∧
     (Steps.frames (firstReceiver factory initial firstCfg language) (firstProgramme factory initial firstCfg language) index).action = .inl settled })
   (Nat.zero_add actual.1)) actual.2⟩
abbrev firstSelected := Steps.frames (firstReceiver factory initial firstCfg language)
 (firstProgramme factory initial firstCfg language) (firstReceipt factory initial firstCfg language).1
abbrev firstBorn := S.nextBorn (firstSelected factory initial firstCfg language)
 (firstProgramme factory initial firstCfg language)
private abbrev PaidAt {U Y : Sorts → Type u} [∀ target,AddCommGroup (U target)]
 (frame : M.Frame (Value := U) (Var := Y) (sort := s)) :=
 Σ paid : DebtActivationWorld.GeneratedStepAt
    (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state,
  PLift (frame.action = .inr paid)
def firstPaidAt (offset : Fin (firstReceipt factory initial firstCfg language).1) :
 PaidAt (Steps.frames (firstReceiver factory initial firstCfg language)
  (firstProgramme factory initial firstCfg language) offset.val) :=
 Eq.mp (congrArg (fun index => PaidAt (Steps.frames (firstReceiver factory initial firstCfg language)
   (firstProgramme factory initial firstCfg language) index)) (Nat.zero_add offset.val))
 (Prefix.receipt_paid_prefix (firstProgramme factory initial firstCfg language)
  (firstReceiver factory initial firstCfg language) 0 offset)

private theorem advance_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (targetFactory : SF.Factory W Z s) (stage : Stage W Y s) :
 advance targetFactory (transport same stage) = transport same (advance (same.symm ▸ targetFactory) stage) := by
 cases same
 rfl

private theorem first_native_stage (offset : Nat)
 (within : offset ≤ (firstReceipt factory initial firstCfg language).1) :
 stageAt factory initial firstCfg language (1+offset) = transport language
  (.continuation 1
   ⟨Steps.frames (firstReceiver factory initial firstCfg language) (firstProgramme factory initial firstCfg language) offset,
    firstSeed factory initial firstCfg language⟩ (firstBase factory initial firstCfg language) rfl) := by
 induction offset with
 | zero => rfl
 | succ offset previous =>
  have prior := previous (by omega)
  have index : 1+(offset+1) = (1+offset)+1 := by omega
  rw [index]
  change advance factory (stageAt factory initial firstCfg language (1+offset)) = _
  rw [prior,advance_transport]
  apply congrArg (transport language)
  let paid := firstPaidAt factory initial firstCfg language ⟨offset,by omega⟩
  have actual := paid.2.down
  have next : Steps.frames (firstReceiver factory initial firstCfg language)
      (firstProgramme factory initial firstCfg language) (offset+1) =
    (Steps.frames (firstReceiver factory initial firstCfg language)
      (firstProgramme factory initial firstCfg language) offset).mathNext := by
   change S.next _ _ = _
   unfold S.next
   rw [actual]
  simp only [advance,actual,next]

theorem first_native_full (offset : Nat)
 (within : offset ≤ (firstReceipt factory initial firstCfg language).1) :
 presentationAt factory initial firstCfg language (1+offset) = ST.presentation
  (Steps.frames (firstReceiver factory initial firstCfg language) (firstProgramme factory initial firstCfg language) offset)
  (firstProgramme factory initial firstCfg language) := by
 unfold presentationAt
 rw [first_native_stage factory initial firstCfg language offset within]
 exact presented_transport_full language factory _

abbrev firstBornPacket : SF.Packet (W := W) (X := firstCfg.LowVar) (s := s) 1 :=
 ⟨firstBorn factory initial firstCfg language,
  SourceHistoryCommon.seed (firstSeed factory initial firstCfg language)
   (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
    (firstBorn factory initial firstCfg language).registered.input.expression))⟩
abbrev secondFactory : SF.Factory W firstCfg.LowVar s := language.symm ▸ factory
abbrev secondCfg := nextCfg (secondFactory factory firstCfg language) 1
 (firstBornPacket factory initial firstCfg language) (firstProgramme factory initial firstCfg language) rfl
abbrev secondPresentation := SA.presentation (firstBorn factory initial firstCfg language)
 (firstProgramme factory initial firstCfg language)
 (scalar (secondFactory factory firstCfg language) 1 (firstBornPacket factory initial firstCfg language)
  (firstProgramme factory initial firstCfg language) rfl)
 (pair (secondFactory factory firstCfg language) 1 (firstBornPacket factory initial firstCfg language)
  (firstProgramme factory initial firstCfg language) rfl)
 (secondCfg factory initial firstCfg language)

theorem first_born_full :
 presentationAt factory initial firstCfg language (1+(firstReceipt factory initial firstCfg language).1+1) =
 secondPresentation factory initial firstCfg language := by
 change presented factory (advance factory (stageAt factory initial firstCfg language
  (1+(firstReceipt factory initial firstCfg language).1))) = _
 rw [first_native_stage factory initial firstCfg language _ (Nat.le_refl _),advance_transport]
 have actual := (firstReceipt factory initial firstCfg language).2.2.2
 simp only [advance,actual]
 apply Eq.trans (presented_transport_full language factory _)
 rfl

private theorem stage_shift (start offset : Nat) :
 stageAt factory initial firstCfg language (start+offset) =
  (advance factory)^[offset] (stageAt factory initial firstCfg language start) := by
 induction offset with
 | zero => rfl
 | succ offset previous =>
  change advance factory (stageAt factory initial firstCfg language (start+offset)) = _
  rw [previous,Function.iterate_succ_apply']

private theorem advance_paid (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (base : A.Programme (PhysicalValue := Lower.Value W n) (PhysicalVar := X) (sort := s))
 (sameVar : base.LowVar = X)
 (paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law data.1.registered.input.environment data.1.registered.input.expression) data.1.event.state)
 (actual : data.1.action = .inr paid) :
 advance factory (.continuation n data base sameVar) =
  .continuation n ⟨data.1.mathNext,data.2⟩ base sameVar := by simp only [advance,actual]

private theorem advance_settled (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (base : A.Programme (PhysicalValue := Lower.Value W n) (PhysicalVar := X) (sort := s))
 (sameVar : base.LowVar = X) (settled : SourceOperationExecutionDebt.Settlement data.1.event.state)
 (actual : data.1.action = .inl settled) :
 advance factory (.continuation n data base sameVar) =
  .admission n ⟨S.nextBorn data.1 (stockCfg base),SourceHistoryCommon.seed data.2
   (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator
    (S.nextBorn data.1 (stockCfg base)).registered.input.expression))⟩
   (stockCfg base) sameVar := by simp only [advance,actual]

private theorem shared_next_paid (n : Nat)
 (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s))
 (base : A.Programme (PhysicalValue := Lower.Value W n) (PhysicalVar := X) (sort := s))
 (paid : DebtActivationWorld.GeneratedStepAt
  (RootGeneratedDebtActivationJointSource.Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state)
 (actual : frame.action = .inr paid) :
 S.next frame (stockCfg base) = frame.mathNext := by
 unfold S.next
 rw [actual]

private theorem native_iterate (n : Nat) (data : SF.Packet (W := W) (X := X) (s := s) n)
 (base : A.Programme (PhysicalValue := Lower.Value W n) (PhysicalVar := X) (sort := s))
 (sameVar : base.LowVar = X) (offset : Nat)
 (within : offset ≤ (Complete.receipt (stockCfg base) data.1 0).1) :
 (advance factory)^[offset] (.continuation n data base sameVar) =
 .continuation n ⟨Steps.frames data.1 (stockCfg base) (0+offset),data.2⟩ base sameVar := by
 induction offset with
 | zero => rfl
 | succ offset previous =>
  rw [Function.iterate_succ_apply',previous (by omega)]
  let paid := Prefix.receipt_paid_prefix (stockCfg base) data.1 0 ⟨offset,by omega⟩
  have next : Steps.frames data.1 (stockCfg base) (0+(offset+1)) =
   (Steps.frames data.1 (stockCfg base) (0+offset)).mathNext := by
   change S.next _ _ = _
   exact shared_next_paid n _ base paid.1 paid.2.down
  exact (advance_paid factory n
    ⟨Steps.frames data.1 (stockCfg base) (0+offset),data.2⟩ base sameVar paid.1 paid.2.down).trans
   (congrArg (fun frame => Stage.continuation n ⟨frame,data.2⟩ base sameVar) next.symm)

abbrev AdmissionPacket := Σ grade : Nat,
 Σ _data : SF.Packet (W := W) (X := X) (s := s) grade,
 Σ cfg : A.Programme (PhysicalValue := Lower.Value W grade) (PhysicalVar := X) (sort := s),
 PLift (cfg.LowVar = X)

private def admissionStage (packet : AdmissionPacket (W := W) (X := X) (s := s)) : Stage W X s :=
 .admission packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down

def admissionPresentation (packet : AdmissionPacket (W := W) (X := X) (s := s)) :=
 presented factory (admissionStage packet)

def localNativeReceipt (packet : AdmissionPacket (W := W) (X := X) (s := s)) :=
 Complete.receipt (stockCfg packet.2.2.1) packet.2.1.1 0

def localPaidAt (packet : AdmissionPacket (W := W) (X := X) (s := s))
 (offset : Fin (localNativeReceipt packet).1) :=
 Prefix.receipt_paid_prefix (stockCfg packet.2.2.1) packet.2.1.1 0 offset

private def nativeStageAt (packet : AdmissionPacket (W := W) (X := X) (s := s)) (offset : Nat) : Stage W X s :=
 .continuation packet.1
  ⟨Steps.frames packet.2.1.1 (stockCfg packet.2.2.1) (0+offset),packet.2.1.2⟩
  packet.2.2.1 packet.2.2.2.down

private abbrev StageAdmissionReceipt (start : Nat) := Σ distance : Nat,
 Σ packet : AdmissionPacket (W := W) (X := X) (s := s),
 PLift (stageAt factory initial firstCfg language (start+distance) = admissionStage packet) ×
 (PLift (distance = 0) ⊕
  Σ native : AdmissionPacket (W := W) (X := X) (s := s),
   PLift (distance = (localNativeReceipt native).1+1) ×
   ((offset : Fin (localNativeReceipt native).1) → type_of% (localPaidAt native offset)) ×
   PLift (∀ offset,offset ≤ (localNativeReceipt native).1 →
    stageAt factory initial firstCfg language (start+offset) = nativeStageAt native offset))

/-- The native stop constructs the full born frame from its own receipt. -/
def bornAfterNative (packet : AdmissionPacket (W := W) (X := X) (s := s)) :
 AdmissionPacket (W := W) (X := X) (s := s) :=
 let receipt := localNativeReceipt packet
 let selected := Steps.frames packet.2.1.1 (stockCfg packet.2.2.1) (0+receipt.1)
 let born := S.nextBorn selected (stockCfg packet.2.2.1)
 ⟨packet.1,⟨born,SourceHistoryCommon.seed packet.2.1.2
  (RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator born.registered.input.expression))⟩,
  stockCfg packet.2.2.1,packet.2.2.2⟩

private theorem stageAt_succ (count : Nat) :
 stageAt factory initial firstCfg language (count+1) =
 advance factory (stageAt factory initial firstCfg language count) := rfl

attribute [local irreducible] stageAt

-- Compute source fields before proving their dependent runtime certificate.
private def sourceStopData : Stage W X s → Nat × AdmissionPacket (W := W) (X := X) (s := s)
 | .admission n data cfg sameVar => (0,⟨n,data,cfg,⟨sameVar⟩⟩)
 | .continuation n data base sameVar =>
   let native : AdmissionPacket (W := W) (X := X) (s := s) := ⟨n,data,base,⟨sameVar⟩⟩
   ((localNativeReceipt native).1+1,bornAfterNative native)


private def sourceStopCertificate (current : Stage W X s) :
 PLift ((advance factory)^[(sourceStopData current).1] current =
  admissionStage (sourceStopData current).2) ×
 (PLift ((sourceStopData current).1 = 0) ⊕
  Σ native : AdmissionPacket (W := W) (X := X) (s := s),
   PLift ((sourceStopData current).1 = (localNativeReceipt native).1+1) ×
   ((offset : Fin (localNativeReceipt native).1) → type_of% (localPaidAt native offset)) ×
   PLift (∀ offset,offset ≤ (localNativeReceipt native).1 →
    (advance factory)^[offset] current = nativeStageAt native offset)) := by
 cases current with
 | admission n data cfg sameVar => exact ⟨⟨rfl⟩,.inl ⟨rfl⟩⟩
 | continuation n data base sameVar =>
   let native : AdmissionPacket (W := W) (X := X) (s := s) := ⟨n,data,base,⟨sameVar⟩⟩
   let receipt := localNativeReceipt native
   refine ⟨⟨?_⟩,.inr ⟨native,⟨rfl⟩,localPaidAt native,⟨?_⟩⟩⟩
   · change (advance factory)^[receipt.1+1] (Stage.continuation n data base sameVar) =
      admissionStage (bornAfterNative native)
     rw [Function.iterate_succ_apply']
     exact (congrArg (advance factory)
      (native_iterate factory n data base sameVar receipt.1 (Nat.le_refl _))).trans
       (advance_settled factory n
        ⟨Steps.frames data.1 (stockCfg base) (0+receipt.1),data.2⟩ base sameVar receipt.2.1 receipt.2.2.2)
   · intro offset within
     exact native_iterate factory n data base sameVar offset within


/-- Source phase elimination consumes the current generated stage only.
The existing completion receipt determines a native segment's stopping distance. -/
private def nextAdmissionStage (start : Nat) : StageAdmissionReceipt factory initial firstCfg language start :=
 ⟨(sourceStopData (stageAt factory initial firstCfg language start)).1,
  (sourceStopData (stageAt factory initial firstCfg language start)).2,by
   let certificate := sourceStopCertificate factory (stageAt factory initial firstCfg language start)
   refine ⟨⟨(stage_shift factory initial firstCfg language start _).trans certificate.1.down⟩,?_⟩
   exact Sum.map id (fun native =>
    ⟨native.1,native.2.1,native.2.2.1,⟨fun offset within =>
     (stage_shift factory initial firstCfg language start offset).trans
      (native.2.2.2.down offset within)⟩⟩) certificate.2⟩


def nativePresentation (packet : AdmissionPacket (W := W) (X := X) (s := s)) (offset : Nat) :=
 ST.presentation (Steps.frames packet.2.1.1 (stockCfg packet.2.2.1) (0+offset)) (stockCfg packet.2.2.1)

abbrev AdmissionReceipt (start : Nat) := Σ distance : Nat,
 Σ packet : AdmissionPacket (W := W) (X := X) (s := s),
 PLift (presentationAt factory initial firstCfg language (start+distance) = admissionPresentation factory packet) ×
 (PLift (distance = 0) ⊕
  Σ native : AdmissionPacket (W := W) (X := X) (s := s),
   PLift (distance = (localNativeReceipt native).1+1) ×
   ((offset : Fin (localNativeReceipt native).1) → type_of% (localPaidAt native offset)) ×
   PLift (∀ offset,offset ≤ (localNativeReceipt native).1 →
    presentationAt factory initial firstCfg language (start+offset) = nativePresentation native offset))

/-- The source-generated receipt exposes full presentations, not root erasures. -/
def nextAdmissionAt (start : Nat) : AdmissionReceipt factory initial firstCfg language start := by
 rcases nextAdmissionStage factory initial firstCfg language start with ⟨distance,packet,actual,segment⟩
 refine ⟨distance,packet,⟨congrArg (presented factory) actual.down⟩,?_⟩
 cases segment with
 | inl already => exact .inl already
 | inr native =>
  exact .inr ⟨native.1,native.2.1,native.2.2.1,⟨fun offset within =>
   congrArg (presented factory) (native.2.2.2.down offset within)⟩⟩

abbrev admissionDistance (start : Nat) := (nextAdmissionAt factory initial firstCfg language start).1
abbrev admissionPoint (start : Nat) := (nextAdmissionAt factory initial firstCfg language start).2.1

theorem nextAdmission_full (start : Nat) :
 presentationAt factory initial firstCfg language (start+admissionDistance factory initial firstCfg language start) =
 admissionPresentation factory (admissionPoint factory initial firstCfg language start) :=
 (nextAdmissionAt factory initial firstCfg language start).2.2.1.down

def admissionSegment (start : Nat) := (nextAdmissionAt factory initial firstCfg language start).2.2.2




private theorem stopped_stage (start : Nat) :
 stageAt factory initial firstCfg language
  (start + admissionDistance factory initial firstCfg language start) =
 admissionStage (admissionPoint factory initial firstCfg language start) :=
 (nextAdmissionStage factory initial firstCfg language start).2.2.1.down

private def packetTransport {Y Z : Sorts → Type u} (same : Y = Z) :
 AdmissionPacket (W := W) (X := Y) (s := s) → AdmissionPacket (W := W) (X := Z) (s := s) := by
 cases same
 exact id

private theorem packetTransport_grade {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : AdmissionPacket (W := W) (X := Y) (s := s)) :
 (packetTransport same packet).1 = packet.1 := by cases same; rfl

private theorem nativeStageAt_transport {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : AdmissionPacket (W := W) (X := Y) (s := s)) (offset : Nat) :
 nativeStageAt (packetTransport same packet) offset = transport same (nativeStageAt packet offset) := by
 cases same
 rfl

/-- This admission's original receiver, seed and programme at the next grade. -/
def nativeAfterAdmission (packet : AdmissionPacket (W := W) (X := X) (s := s)) :
 AdmissionPacket (W := W) (X := X) (s := s) :=
 packetTransport packet.2.2.2.down
  ⟨packet.1+1,⟨receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
   nextBase factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,⟨rfl⟩⟩

theorem nativeAfterAdmission_grade
 (packet : AdmissionPacket (W := W) (X := X) (s := s)) :
 (nativeAfterAdmission factory packet).1 = packet.1+1 := packetTransport_grade _ _

private theorem advance_admission_native
 (packet : AdmissionPacket (W := W) (X := X) (s := s)) :
 advance factory (admissionStage packet) = nativeStageAt (nativeAfterAdmission factory packet) 0 :=
 (nativeStageAt_transport packet.2.2.2.down
  ⟨packet.1+1,⟨receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
   nextBase factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,⟨rfl⟩⟩ 0).symm


private theorem admissionPoint_source (start : Nat) :
 admissionPoint factory initial firstCfg language start =
 (sourceStopData (stageAt factory initial firstCfg language start)).2 := rfl

private theorem admissionPoint_of_native (start : Nat)
 (packet : AdmissionPacket (W := W) (X := X) (s := s))
 (actual : stageAt factory initial firstCfg language start = nativeStageAt packet 0) :
 admissionPoint factory initial firstCfg language start = bornAfterNative packet :=
 (admissionPoint_source factory initial firstCfg language start).trans
  (congrArg (fun stage => (sourceStopData stage).2) actual)


/-- The same admission source, native receipt and birth generate the entire next packet. -/
theorem admissionPoint_successor (start : Nat) :
 admissionPoint factory initial firstCfg language
  (start + admissionDistance factory initial firstCfg language start + 1) =
 bornAfterNative (nativeAfterAdmission factory
  (admissionPoint factory initial firstCfg language start)) := by
 apply admissionPoint_of_native
 exact (stageAt_succ factory initial firstCfg language _).trans
  ((congrArg (advance factory) (stopped_stage factory initial firstCfg language start)).trans
   (advance_admission_native factory _))

theorem admissionPoint_successor_grade (start : Nat) :
 (admissionPoint factory initial firstCfg language
  (start + admissionDistance factory initial firstCfg language start + 1)).1 =
 (admissionPoint factory initial firstCfg language start).1+1 :=
 (congrArg Sigma.fst (admissionPoint_successor factory initial firstCfg language start)).trans
  (nativeAfterAdmission_grade factory _)



end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
