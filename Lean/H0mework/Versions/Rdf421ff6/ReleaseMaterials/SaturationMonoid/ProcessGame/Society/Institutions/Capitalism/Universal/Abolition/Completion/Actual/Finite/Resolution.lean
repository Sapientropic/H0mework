import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite.NoCapture

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => Macro.Runtime.ActivatedFrame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount

def ActualReviewObstruction (state : F) : Prop := match state with
  | .original current => ∃ raw : Macro.Runtime.ActivatedFrame.OriginalBoundary current,
      ∃ failed, InitialAdmission.select (current.controlOrigin raw.germ) = .obstructed failed ∧
        InitialAdmission.Failure.publicObstruction (current.controlOrigin raw.germ) failed = failed ∧
        ∀ entry,
          (((InitialAdmission.Failure.generated (current.controlOrigin raw.germ) failed).target.initialOpenLedger).forward entry).1 = entry.1 ∧
          (((InitialAdmission.Failure.generated (current.controlOrigin raw.germ) failed).target.initialOpenLedger).forward entry).claim = entry.claim ∧
          (((InitialAdmission.Failure.generated (current.controlOrigin raw.germ) failed).target.initialOpenLedger).forward entry).progressBudget = entry.progressBudget
  | .enacted .. => False

theorem an_actual_obstruction_cannot_be_a_closed_review
    (state : F) (blocked : ActualReviewObstruction state) : ¬ NoUnresolvedReview state := by
  cases state with
  | original current =>
      obtain ⟨raw, failed, selected, _receipt, _ledger⟩ := blocked
      exact fun closed => closed raw ⟨failed, selected⟩
  | enacted origin admission current => exact blocked.elim

theorem the_source_keeps_a_public_current_public (state : F) (opened : state.isPublic = true) (steps : Nat) :
    (state.after steps).isPublic = true := by
  induction steps with
  | zero => exact opened
  | succ steps inherited =>
      rw [Macro.Runtime.ActivatedFrame.after_succ]
      cases actual : state.after steps with
      | original current => rw [actual] at inherited; cases inherited
      | enacted origin admission current => rfl

private theorem boundary_selection (state : F) (boundary : state.BoundaryAt) :
    (state.isPublic = true ∨ state.next.isPublic = true) ∨ ActualReviewObstruction state := by
  have conclusion := the_actual_boundary_generates_its_review_conclusion state boundary
  cases boundary with
  | original current raw =>
      cases selected : InitialAdmission.select (current.controlOrigin raw.germ) with
      | admitted admission =>
          dsimp only [ReviewConclusion] at conclusion
          rw [selected] at conclusion
          exact .inl (.inr conclusion.1)
      | obstructed failed =>
          exact .inr ⟨raw, failed, selected, rfl,
            Capital.an_obstruction_cannot_erase_a_bearer_claim_or_unspent_budget (current.controlOrigin raw.germ) failed⟩
  | enacted origin admission current done => exact .inl (.inl rfl)

variable (input depth sourceDepth)
  (datum : Macro.Ingress.Datum input depth sourceDepth) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceDepth))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "current" => Macro.Runtime.actualFrame (review := review)
  input depth sourceDepth datum prefixLimit renewalLimit reader

/-- One more real occurrence consumes the review. The endpoint is a
persistent public tail or an exact original-row obstruction, within the
current source inventory plus that review occurrence. -/
theorem the_actual_source_forces_a_finite_public_tail_or_its_exact_obstruction (tick : Nat) :
    ∃ steps ≤ (current tick).internalMass + 1,
      ((current (tick + steps)).isPublic = true ∧
        ∀ later, (current (tick + steps + later)).isPublic = true) ∨
      ActualReviewObstruction (current (tick + steps)) := by
  let steps := (current tick).complete.steps
  have within := (current tick).complete.within
  let boundary := Macro.Runtime.actualInternalBoundary (review := review)
    input depth sourceDepth datum prefixLimit renewalLimit reader tick
  have selected := boundary_selection (current (tick + steps)) boundary
  rcases selected with (opened | nextOpened) | blocked
  · refine ⟨steps, by omega, .inl ⟨opened, ?_⟩⟩
    intro later
    rw [← Macro.Runtime.actual_internal_fold_is_the_same_registered_history (review := review)
      input depth sourceDepth datum prefixLimit renewalLimit reader (tick + steps) later]
    exact the_source_keeps_a_public_current_public _ opened later
  · have same : current (tick + (steps + 1)) = (current (tick + steps)).next := by
      rw [Nat.add_succ]
      rfl
    have opened : (current (tick + (steps + 1))).isPublic = true := same.symm ▸ nextOpened
    refine ⟨steps + 1, by omega, .inl ⟨opened, ?_⟩⟩
    intro later
    rw [← Macro.Runtime.actual_internal_fold_is_the_same_registered_history (review := review)
      input depth sourceDepth datum prefixLimit renewalLimit reader (tick + (steps + 1)) later]
    exact the_source_keeps_a_public_current_public _ opened later
  · exact ⟨steps, by omega, .inr blocked⟩

#print axioms an_actual_obstruction_cannot_be_a_closed_review
#print axioms the_source_keeps_a_public_current_public
#print axioms the_actual_source_forces_a_finite_public_tail_or_its_exact_obstruction

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite
