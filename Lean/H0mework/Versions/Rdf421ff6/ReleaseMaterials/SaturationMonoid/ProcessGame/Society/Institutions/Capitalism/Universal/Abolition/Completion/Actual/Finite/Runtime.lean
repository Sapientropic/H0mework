import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite.Review
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Macro.Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input depth (Macro.Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "F" => Macro.Runtime.ActivatedFrame (review := review) input depth
  (Macro.Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth
  (Macro.Ingress.cut input depth sourceStart)
local notation "current" => Macro.Runtime.actualFrame (review := review)
  input depth sourceStart datum prefixLimit renewalLimit reader

/-- Universal path quantification is over the existing runtime's legal
successor relation. It neither supplies a successful endpoint nor chooses a
replacement source. -/
theorem every_legal_continuation_is_the_original_actual_fold
    (tick : Nat) (path : Nat → F) (starts : path 0 = current tick)
    (legal : ∀ step, path (step + 1) = (path step).next) (steps : Nat) :
    path steps = current (tick + steps) := by
  rw [← Macro.Runtime.actual_internal_fold_is_the_same_registered_history
    (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick steps]
  induction steps with
  | zero => exact starts
  | succ steps inherited => rw [legal, inherited, Macro.Runtime.ActivatedFrame.after_succ]

/-- The deadline is paid inventory, read from this actual occurrence.
At that finite deadline the real compiler selects public life or carries the
precise obstruction, and the same Engine consumes the whole-root next. -/
theorem every_actual_current_has_a_finite_forced_review_cone (tick : Nat) :
    ∃ steps ≤ (current tick).internalMass,
      ∃ boundary : (current (tick + steps)).BoundaryAt,
        ReviewConclusion (current (tick + steps)) boundary ∧
        (∀ path : Nat → F, path 0 = current tick →
          (∀ index, path (index + 1) = (path index).next) → path steps = current (tick + steps)) ∧
        type_of% (Macro.Runtime.the_boundary_action_preserves_the_whole_root_and_generates_next
          (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick) := by
  let steps := (current tick).complete.steps
  have within := (current tick).complete.within
  let boundary := Macro.Runtime.actualInternalBoundary (review := review)
    input depth sourceStart datum prefixLimit renewalLimit reader tick
  refine ⟨steps, within, boundary, the_actual_boundary_generates_its_review_conclusion _ boundary, ?_,
    Macro.Runtime.the_boundary_action_preserves_the_whole_root_and_generates_next
      (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick⟩
  intro path starts legal
  exact every_legal_continuation_is_the_original_actual_fold input depth sourceStart datum
    prefixLimit renewalLimit reader review tick path starts legal steps

#print axioms every_legal_continuation_is_the_original_actual_fold
#print axioms every_actual_current_has_a_finite_forced_review_cone

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Finite
