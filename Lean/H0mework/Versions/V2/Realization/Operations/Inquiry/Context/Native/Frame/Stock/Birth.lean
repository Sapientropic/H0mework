import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Births

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Frame.Stock.Birth
open SourceOperationEffects RootInquiryCompletion
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (frames runtime root visit query presentation state next nextBorn targetAt birthProgram
   target_root target_next actual_answer actual_next compiles_settled successor_valid)
end A
namespace B
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births
  (birthIndex settled actual_action actual_next actual_compiles)
end B
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory
  (programme installed sourceOutcome source_inventory)
end I
namespace K
export SourceOperationInquiry.Context.Native.Frame.Stock
  (frameAt frame_actual canonical_stock)
end K
variable {Sorts : Type u} {Value Var : Sorts → Type u}
  [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (initial : SourceOperationInquiry.Context.Native.Frame.SourceFrame (Value := Value) (Var := Var) (sort := sort))
variable (configuration : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

abbrev index (ordinal : Nat) := B.birthIndex (I.programme configuration) initial ordinal
abbrev current (ordinal : Nat) := A.frames initial (I.programme configuration) (index initial configuration ordinal)
abbrev after (ordinal : Nat) := A.frames initial (I.programme configuration) (index initial configuration ordinal + 1)
abbrev generated (ordinal : Nat) := (A.birthProgram (current initial configuration ordinal) (I.programme configuration)).generate
  ((A.root (current initial configuration ordinal) (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (A.visit (current initial configuration ordinal) (I.programme configuration)))
abbrev target (ordinal : Nat) := (generated initial configuration ordinal).target

theorem selected_action (ordinal : Nat) : type_of%
    (B.actual_action (I.programme configuration) initial ordinal) :=
  B.actual_action (I.programme configuration) initial ordinal
theorem selected_compile (ordinal : Nat) : type_of%
    (B.actual_compiles (I.programme configuration) initial ordinal) :=
  B.actual_compiles (I.programme configuration) initial ordinal
theorem after_birth (ordinal : Nat) : after initial configuration ordinal =
    A.nextBorn (current initial configuration ordinal) (I.programme configuration) := by
  change A.next _ _ = _
  unfold A.next
  rw [B.actual_action (I.programme configuration) initial ordinal]

theorem macro_answer (ordinal : Nat) :
    HEq ((A.runtime initial (I.programme configuration)).tickAt (index initial configuration ordinal)).answer
      (generated initial configuration ordinal).answer := by
  have read := A.actual_answer initial (I.programme configuration) (index initial configuration ordinal)
  have compiled := A.compiles_settled (current initial configuration ordinal) (I.programme configuration)
    (B.settled (I.programme configuration) initial ordinal)
    (B.actual_action (I.programme configuration) initial ordinal)
  rw [compiled] at read
  exact read
theorem macro_next (ordinal : Nat) : type_of%
    (B.actual_next (I.programme configuration) initial ordinal) :=
  B.actual_next (I.programme configuration) initial ordinal
theorem macro_next_current (ordinal : Nat) :
    ((A.runtime initial (I.programme configuration)).tickAt (index initial configuration ordinal)).next.node.erase =
      ⟨(target initial configuration ordinal).TargetN,
        (target initial configuration ordinal).targetAnswerAndNext.nextCurrent⟩ := by
  have generatedNext := A.actual_next initial (I.programme configuration) (index initial configuration ordinal)
  have frameNext := congrArg
    (fun frame => (RootInquiryProcessNode.active (A.presentation frame (I.programme configuration))).erase)
    (after_birth initial configuration ordinal)
  have targetNext := congrArg
    (fun value : SourceNativeAuthoritativeRootCurrentAt (target initial configuration ordinal).TargetN =>
      (⟨(target initial configuration ordinal).TargetN, value⟩ : AnyAuthoritativeRootCurrent))
    (A.target_next (current initial configuration ordinal) (I.programme configuration)
      ((A.root (current initial configuration ordinal) (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (A.visit (current initial configuration ordinal) (I.programme configuration)))).symm
  exact (congrArg RootInquiryProcessNode.erase generatedNext).trans (frameNext.trans targetNext)
theorem actual_root (ordinal : Nat) : HEq (target initial configuration ordinal).targetRoot
    (A.root (after initial configuration ordinal) (I.programme configuration)) := by
  rw [after_birth]
  exact heq_of_eq (A.target_root (current initial configuration ordinal) (I.programme configuration) _)

theorem selected_packet (ordinal : Nat) : type_of%
    (((target initial configuration ordinal).oldOutcome_heq
      ((I.installed (current initial configuration ordinal) configuration).embed PUnit.unit)).trans
        (I.source_inventory (current initial configuration ordinal) configuration)) := by
  let claim (frame : SourceOperationInquiry.Context.Native.Frame.SourceFrame (Value := Value) (Var := Var) (sort := sort)) : Prop :=
    let admission := A.targetAt frame (I.programme configuration)
      ((A.root frame (I.programme configuration)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
        (A.visit frame (I.programme configuration)))
    type_of% ((admission.oldOutcome_heq ((I.installed frame configuration).embed PUnit.unit)).trans
      (I.source_inventory frame configuration))
  have stock : claim (K.frameAt initial configuration (index initial configuration ordinal)) :=
    K.canonical_stock initial configuration (index initial configuration ordinal)
  exact Eq.mp (congrArg claim (K.frame_actual initial configuration (index initial configuration ordinal))) stock

def after_projection (ordinal : Nat) :
    (A.root (after initial configuration ordinal) (I.programme configuration)).toAuthoritativeRoot.source.projectionLaw.Projection :=
  (after_birth initial configuration ordinal).symm ▸
    (show (A.root (A.nextBorn (current initial configuration ordinal) (I.programme configuration))
      (I.programme configuration)).toAuthoritativeRoot.source.projectionLaw.Projection from
      (target initial configuration ordinal).oldProjection
        ((I.installed (current initial configuration ordinal) configuration).embed PUnit.unit))
/-- Inherited material is read at the actual successor root's admission-initial occurrence. -/
abbrev after_initial_read (ordinal : Nat) :=
  (A.root (after initial configuration ordinal) (I.programme configuration)).toAuthoritativeRoot.source.projectionLaw.outcomeAt
    (after_projection initial configuration ordinal)
    ((A.root (after initial configuration ordinal) (I.programme configuration)).emitted
      (A.root (after initial configuration ordinal) (I.programme configuration)).toAuthoritativeRoot.toRoot.source.initial)
/-- The successor also installs its fresh stock at its own actual current. -/
abbrev after_current_read (ordinal : Nat) :=
  I.sourceOutcome (after initial configuration ordinal) configuration

private theorem transport_initial_read
    (left right : SourceOperationInquiry.Context.Native.Frame.SourceFrame (Value := Value) (Var := Var) (sort := sort))
    (same : left = right)
    (projection : (A.root right (I.programme configuration)).toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((A.root left (I.programme configuration)).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (same.symm ▸ projection) ((A.root left (I.programme configuration)).emitted
        (A.root left (I.programme configuration)).toAuthoritativeRoot.toRoot.source.initial))
      ((A.root right (I.programme configuration)).toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection ((A.root right (I.programme configuration)).emitted
          (A.root right (I.programme configuration)).toAuthoritativeRoot.toRoot.source.initial)) := by
  cases same
  rfl

theorem initial_readback (ordinal : Nat) :
    HEq (after_initial_read initial configuration ordinal)
      ((target initial configuration ordinal).targetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        ((target initial configuration ordinal).oldProjection
          ((I.installed (current initial configuration ordinal) configuration).embed PUnit.unit))
        ((target initial configuration ordinal).targetRoot.emitted
          (target initial configuration ordinal).targetInitialVisit.current)) := by
  exact transport_initial_read configuration (after initial configuration ordinal)
    (A.nextBorn (current initial configuration ordinal) (I.programme configuration))
    (after_birth initial configuration ordinal)
    ((target initial configuration ordinal).oldProjection
      ((I.installed (current initial configuration ordinal) configuration).embed PUnit.unit))
theorem actual_complete_stock (ordinal : Nat) : type_of%
    ((initial_readback initial configuration ordinal).trans (selected_packet initial configuration ordinal)) :=
  (initial_readback initial configuration ordinal).trans (selected_packet initial configuration ordinal)
theorem current_complete_stock (ordinal : Nat) : type_of%
    (I.source_inventory (after initial configuration ordinal) configuration) :=
  I.source_inventory (after initial configuration ordinal) configuration
def macro_receipt (ordinal : Nat) :=
  ((A.runtime initial (I.programme configuration)).tickAt (index initial configuration ordinal)).receipt

end SourceOperationInquiry.Context.Native.Frame.Stock.Birth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
