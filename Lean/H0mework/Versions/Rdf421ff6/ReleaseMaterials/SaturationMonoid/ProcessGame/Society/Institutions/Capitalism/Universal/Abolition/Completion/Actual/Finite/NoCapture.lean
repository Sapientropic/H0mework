import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl Functions.Revision

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

local notation "F" => Macro.Runtime.ActivatedFrame (review := review)
  input depth count prefixLimit renewalLimit sourceDepth sourceCount

def GeneratesCapital (state : F) : Prop :=
  ∃ word, Nonempty (Kernel.CapitalRelationKernel state.interpreter state.actualState.raw word)

/-- A finality claim must account for every actual registered review. An
emitted obstruction is an open responsibility, not a closed settlement. -/
def NoUnresolvedReview (state : F) : Prop := match state with
  | .original current => ∀ raw : Macro.Runtime.ActivatedFrame.OriginalBoundary current,
      ¬ ∃ failed, InitialAdmission.select (current.controlOrigin raw.germ) = .obstructed failed
  | .enacted .. => True

theorem a_public_actual_current_cannot_generate_capital
    (state : F) (opened : state.isPublic = true) : ¬ GeneratesCapital state := by
  cases state with
  | original current => cases opened
  | enacted origin admission current =>
      rintro ⟨word, capital⟩
      exact Functions.open_permissions_have_no_capital_kernel _ (fun _ _ _ => rfl) _ word capital

private theorem public_next (state : F) (opened : state.isPublic = true) : state.next.isPublic = true := by
  cases state with
  | original current => cases opened
  | enacted origin admission current => rfl

private theorem public_after (state : F) (opened : state.isPublic = true) (steps : Nat) :
    (state.after steps).isPublic = true := by
  induction steps with
  | zero => exact opened
  | succ steps inherited =>
      rw [Macro.Runtime.ActivatedFrame.after_succ]
      exact public_next _ inherited

private theorem a_public_next_excludes_cofinal_capital
    (state : F) (opened : state.next.isPublic = true)
    (recurs : ∀ cutoff, ∃ steps ≥ cutoff, GeneratesCapital (state.after steps)) : False := by
  obtain ⟨steps, positive, capital⟩ := recurs 1
  cases steps with
  | zero => omega
  | succ steps =>
      rw [← Macro.Runtime.ActivatedFrame.after_next] at capital
      exact a_public_actual_current_cannot_generate_capital _ (public_after state.next opened steps) capital

private theorem a_real_review_prevents_closed_capital_absorption
    (state : F) (boundary : state.BoundaryAt)
    (recurs : ∀ cutoff, ∃ steps ≥ cutoff, GeneratesCapital (state.after steps))
    (closed : NoUnresolvedReview state) : False := by
  have conclusion := the_actual_boundary_generates_its_review_conclusion state boundary
  cases boundary with
  | original current raw =>
      change ∀ raw : Macro.Runtime.ActivatedFrame.OriginalBoundary current,
        ¬ ∃ failed, InitialAdmission.select (current.controlOrigin raw.germ) = .obstructed failed at closed
      cases selected : InitialAdmission.select (current.controlOrigin raw.germ) with
      | admitted admission =>
          dsimp only [ReviewConclusion] at conclusion
          rw [selected] at conclusion
          exact a_public_next_excludes_cofinal_capital _ conclusion.1 recurs
      | obstructed failed => exact closed raw ⟨failed, selected⟩
  | enacted origin admission current done =>
      obtain ⟨steps, _after, capital⟩ := recurs 0
      exact a_public_actual_current_cannot_generate_capital _ (public_after _ rfl steps) capital

variable (input depth sourceDepth)
  (datum : Macro.Ingress.Datum input depth sourceDepth) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceDepth))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "A" => Macro.Runtime.ActivatedFrame (review := review) input depth
  (Macro.Ingress.cut input depth sourceDepth) prefixLimit renewalLimit depth
  (Macro.Ingress.cut input depth sourceDepth)
local notation "current" => Macro.Runtime.actualFrame (review := review)
  input depth sourceDepth datum prefixLimit renewalLimit reader

/-- This quantifies over actual legal continuations, not the persistence of
a name. Complete C may be intermittent, but recurs in every tail; finality
also claims that every registered review has no unresolved responsibility. -/
def LegallyAdmittedAbsorbingCapitalism (tick : Nat) : Prop :=
  ∃ path : Nat → A, path 0 = current tick ∧
    (∀ step, path (step + 1) = (path step).next) ∧
    (∀ cutoff, ∃ step ≥ cutoff, GeneratesCapital (path step)) ∧ (∀ step, NoUnresolvedReview (path step))

theorem capitalism_cannot_obtain_a_legally_admitted_absorbing_finality (tick : Nat) :
    ¬ LegallyAdmittedAbsorbingCapitalism input depth sourceDepth datum prefixLimit renewalLimit reader review tick := by
  rintro ⟨path, starts, legal, capital, closed⟩
  obtain ⟨steps, _within, boundary, _conclusion, allPaths, _rootNext⟩ :=
    every_actual_current_has_a_finite_forced_review_cone input depth sourceDepth datum prefixLimit renewalLimit reader review tick
  have here := allPaths path starts legal
  have recurs : ∀ cutoff, ∃ offset ≥ cutoff, GeneratesCapital ((current (tick + steps)).after offset) := by
    intro cutoff
    obtain ⟨index, after, generated⟩ := capital (steps + cutoff)
    have fromCut := every_legal_continuation_is_the_original_actual_fold input depth sourceDepth datum
      prefixLimit renewalLimit reader review tick path starts legal index
    refine ⟨index - steps, by omega, ?_⟩
    rw [Macro.Runtime.actual_internal_fold_is_the_same_registered_history
      (review := review) input depth sourceDepth datum prefixLimit renewalLimit reader (tick + steps) (index - steps)]
    have same : tick + steps + (index - steps) = tick + index := by omega
    rw [same, ← fromCut]
    exact generated
  have resolved : NoUnresolvedReview (current (tick + steps)) := here ▸ closed steps
  exact a_real_review_prevents_closed_capital_absorption _ boundary recurs resolved

#print axioms a_public_actual_current_cannot_generate_capital
#print axioms capitalism_cannot_obtain_a_legally_admitted_absorbing_finality

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite
