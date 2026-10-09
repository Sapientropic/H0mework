import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Payment.Consumer
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Consumer
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open Cursor.Native.Feed.Source Cursor.Native.Feed.Continuation.Source

theorem source_value (depth count : Nat) (frame : Frame depth count) :
 (Shared.resultFace frame (continuous depth count)).rootRead.2.2.1 =
 (sourceRaw depth count (A.epoch frame)).expression.eval (sourceRaw depth count (A.epoch frame)).environment :=
 O.source_value (Shared.baseRoot frame (continuous depth count)).toAuthoritativeRoot
  (Shared.datum frame (continuous depth count)).reader (Shared.actualOccurrence frame)
theorem paid_environment (depth count : Nat) (frame : Frame depth count) :
 (Shared.resultFace frame (continuous depth count)).rootRead.2.2.1.1 +
 (Shared.resultFace frame (continuous depth count)).rootRead.2.2.1.2 =
 (programme depth count).eval (A.epoch frame).activeEnvironment := by
 rw [source_value]
 unfold sourceRaw
 rw [eval_liftExpr]
 have updated := Expr.eval_update (programme depth count)
  (A.epoch frame).rawRead.environment ((A.epoch frame).activeEnvironment - (A.epoch frame).rawRead.environment)
 rw [add_sub_cancel] at updated
 exact updated.symm
theorem programme_source (depth count : Nat) (env : Env (Values depth count) Vars) :
 ((programme depth count).eval env).1 =
 Cursor.Native.Action.actualAction depth count (env false Unit.unit) := by
 simp only [programme, Expr.eval, intoFirst, intoSecond, intoThird,
  AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk_add_mk, zero_add, add_zero]
 rfl
theorem born_environment (depth count : Nat) (frame : Frame depth count)
 {current : (Shared.nextBorn frame (continuous depth count)).V.Current}
 (occurrence : (Shared.nextBorn frame (continuous depth count)).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
 (Shared.nextBorn frame (continuous depth count)).environment occurrence =
 environmentAt depth count (A.epoch frame).activeEnvironment (((programme depth count).eval (A.epoch frame).activeEnvironment).1) :=
 congrArg (fun result : Values depth count true => environmentAt depth count (A.epoch frame).activeEnvironment result.1) (paid_environment depth count frame)
theorem born_source_action (depth count : Nat) (frame : Frame depth count) :
 (A.epoch (Shared.nextBorn frame (continuous depth count))).activeEnvironment false Unit.unit =
 Cursor.Native.Action.actualAction depth count ((A.epoch frame).activeEnvironment false Unit.unit) :=
 (congrArg (fun env : Env (Values depth count) Vars => env false Unit.unit)
  (born_environment depth count frame _)).trans (programme_source depth count _)

namespace Runtime
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (next root visit root_math birthProgram target_next frames query successor_valid actual_next)
end Runtime
abbrev physicalWritten (depth count : Nat) (frame : Frame depth count) :=
 SourceOperationPaidRelations.exposure frame.paidRead.state.2
abbrev queryWritten (depth count : Nat) (frame : Frame depth count) :=
 SourceOperationPaidRelations.exposure (sourceResult depth count frame).2.1.2
abbrev PhysicalEvent (depth count : Nat) :=
 CofinalHistorySettlement.PresentedRelationEventAt (Expr (Values depth count) Vars true)
abbrev PairEvent (depth count : Nat) :=
 CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue (Values depth count)) Vars true)
abbrev birth (depth count : Nat) (frame : Frame depth count) :=
 (Runtime.birthProgram frame (continuous depth count)).generate
  ((Runtime.root frame (continuous depth count)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (Runtime.visit frame (continuous depth count)))

/-- The actual action selects either paid forward fields or the decoded birth.
No actor action is asserted for a mere syntax-payment tick. -/
theorem actual_branch (depth count : Nat) (frame : Frame depth count) :
 match frame.action with
 | .inr _ => A.epoch (Runtime.next frame (continuous depth count)) = A.epoch frame ∧
     HEq (Runtime.root (Runtime.next frame (continuous depth count)) (continuous depth count))
       (Runtime.root frame (continuous depth count)) ∧
     (Runtime.next frame (continuous depth count)).inventory = frame.inventory ∧
     (Runtime.next frame (continuous depth count)).pairInventory = frame.pairInventory
 | .inl _ =>
     (A.epoch (Runtime.next frame (continuous depth count))).activeEnvironment false Unit.unit =
       Cursor.Native.Action.actualAction depth count ((A.epoch frame).activeEnvironment false Unit.unit) ∧
     (∀ name : Vars true, (A.epoch (Runtime.next frame (continuous depth count))).activeEnvironment true name =
       (A.epoch frame).activeEnvironment true name) ∧
     type_of% (birth depth count frame).target.firstDestination_heq ∧
     type_of% (Runtime.target_next frame (continuous depth count)
       ((Runtime.root frame (continuous depth count)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
         (Runtime.visit frame (continuous depth count)))) ∧
     ∀ projection, type_of% ((birth depth count frame).target.oldOutcome_heq projection) := by
 cases selected : frame.action with
 | inr paid =>
     have same : Runtime.next frame (continuous depth count) = frame.mathNext := by
       unfold Runtime.next; rw [selected]
     rw [same]
     exact ⟨SourceOperationInquiry.Context.Faces.Execution.Activation.epoch_math frame,
       heq_of_eq (Runtime.root_math frame (continuous depth count)), rfl, rfl⟩
 | inl settled =>
     have same : Runtime.next frame (continuous depth count) = Shared.nextBorn frame (continuous depth count) := by
       unfold Runtime.next; rw [selected]
     rw [same]
     exact ⟨born_source_action depth count frame,
       fun name => by
         have receipt := born_environment depth count frame
           ((Shared.nextBorn frame (continuous depth count)).old.root.emitted
             (Shared.nextBorn frame (continuous depth count)).old.visit.current)
         have read := congrArg (fun env : Env (Values depth count) Vars => env true name) receipt
         exact read,
       (birth depth count frame).target.firstDestination_heq,
       Runtime.target_next frame (continuous depth count) _,
       (birth depth count frame).target.oldOutcome_heq⟩

theorem next_inventory_paid (depth count : Nat) (frame : Frame depth count) (event : PhysicalEvent depth count)
 (present : event ∈ (physicalWritten depth count frame).trace) :
 ∃ written, nextInventory depth count frame = some written ∧ event ∈ written.trace := by
 unfold nextInventory
 cases frame.inventory with
 | none => exact ⟨_, rfl, present⟩
 | some prior => exact ⟨_, rfl, (SourceHistoryCommon.parallel_right _ _ _).1 event present⟩
theorem next_inventory_prior (depth count : Nat) (frame : Frame depth count) (prior)
 (carried : frame.inventory = some prior) (event : PhysicalEvent depth count) (present : event ∈ prior.trace) :
 ∃ written, nextInventory depth count frame = some written ∧ event ∈ written.trace := by
 refine ⟨SourceHistoryCommon.seed prior (physicalWritten depth count frame), ?_,
   (SourceHistoryCommon.parallel_left _ _ _).1 event present⟩
 simp only [nextInventory, carried]
theorem next_pair_paid (depth count : Nat) (frame : Frame depth count) (event : PairEvent depth count)
 (present : event ∈ (queryWritten depth count frame).trace) :
 ∃ written, nextPairInventory depth count frame = some written ∧ event ∈ written.trace := by
 unfold nextPairInventory
 cases frame.pairInventory with
 | none => exact ⟨_, rfl, present⟩
 | some prior => exact ⟨_, rfl, (SourceHistoryCommon.parallel_right _ _ _).1 event present⟩
theorem next_pair_prior (depth count : Nat) (frame : Frame depth count) (prior)
 (carried : frame.pairInventory = some prior) (event : PairEvent depth count) (present : event ∈ prior.trace) :
 ∃ written, nextPairInventory depth count frame = some written ∧ event ∈ written.trace := by
 refine ⟨SourceHistoryCommon.seed prior (queryWritten depth count frame), ?_,
   (SourceHistoryCommon.parallel_left _ _ _).1 event present⟩
 simp only [nextPairInventory, carried]

/-- Both real branches preserve every previously registered physical event. -/
theorem step_inventory_preserved (depth count : Nat) (frame : Frame depth count) (prior)
 (carried : frame.inventory = some prior) (event : PhysicalEvent depth count) (present : event ∈ prior.trace) :
 ∃ written, (Runtime.next frame (continuous depth count)).inventory = some written ∧ event ∈ written.trace := by
 unfold Runtime.next
 cases frame.action with
 | inr paid => exact ⟨prior, carried, present⟩
 | inl settled => exact next_inventory_prior depth count frame prior carried event present
theorem step_pair_preserved (depth count : Nat) (frame : Frame depth count) (prior)
 (carried : frame.pairInventory = some prior) (event : PairEvent depth count) (present : event ∈ prior.trace) :
 ∃ written, (Runtime.next frame (continuous depth count)).pairInventory = some written ∧ event ∈ written.trace := by
 unfold Runtime.next
 cases frame.action with
 | inr paid => exact ⟨prior, carried, present⟩
 | inl settled => exact next_pair_prior depth count frame prior carried event present

theorem frames_inventory_preserved (depth count : Nat) (initial : Frame depth count) (first distance : Nat) (prior)
 (carried : (Shared.frames initial (continuous depth count) first).inventory = some prior)
 (event : PhysicalEvent depth count) (present : event ∈ prior.trace) :
 ∃ written, (Shared.frames initial (continuous depth count) (first + distance)).inventory = some written ∧
   event ∈ written.trace := by
 induction distance with
 | zero => exact ⟨prior, carried, present⟩
 | succ distance previous =>
     obtain ⟨middle, atMiddle, remains⟩ := previous
     rw [Nat.add_succ]
     change ∃ written, (Runtime.next (Shared.frames initial (continuous depth count) (first + distance))
       (continuous depth count)).inventory = some written ∧ event ∈ written.trace
     exact step_inventory_preserved depth count _ middle atMiddle event remains
theorem frames_pair_preserved (depth count : Nat) (initial : Frame depth count) (first distance : Nat) (prior)
 (carried : (Shared.frames initial (continuous depth count) first).pairInventory = some prior)
 (event : PairEvent depth count) (present : event ∈ prior.trace) :
 ∃ written, (Shared.frames initial (continuous depth count) (first + distance)).pairInventory = some written ∧
   event ∈ written.trace := by
 induction distance with
 | zero => exact ⟨prior, carried, present⟩
 | succ distance previous =>
     obtain ⟨middle, atMiddle, remains⟩ := previous
     rw [Nat.add_succ]
     change ∃ written, (Runtime.next (Shared.frames initial (continuous depth count) (first + distance))
       (continuous depth count)).pairInventory = some written ∧ event ∈ written.trace
     exact step_pair_preserved depth count _ middle atMiddle event remains

/-- The actual continuous runtime retains the original generated AST inventory
while its source decoder, whole writes and same-debt consumers run branchwise. -/
theorem continuous_written_and_next (depth count stage : Nat) (event : PhysicalEvent depth count)
 (present : event ∈ (paidInventory depth count).trace) :
 let frame := Shared.frames (dynamicFeed depth count) (continuous depth count) stage
 (∃ written, frame.inventory = some written ∧ event ∈ written.trace) ∧
 type_of% (actual_branch depth count frame) ∧
 type_of% (Runtime.actual_next (dynamicFeed depth count) (continuous depth count) stage) ∧
 type_of% (Runtime.successor_valid frame (continuous depth count) (Runtime.query frame (continuous depth count))) ∧
 type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill (continuous depth count) frame) ∧
 type_of% (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded (continuous depth count) frame) := by
 dsimp only
 have retained := frames_inventory_preserved depth count (dynamicFeed depth count)
   0 stage (paidInventory depth count) rfl event present
 simp only [Nat.zero_add] at retained
 exact ⟨retained,
   actual_branch depth count _, Runtime.actual_next (dynamicFeed depth count) (continuous depth count) stage,
   Runtime.successor_valid _ (continuous depth count) _,
   SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill (continuous depth count) _,
   SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded (continuous depth count) _⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Consumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
