import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Compile.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Actual.State (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (code : Code Party Good Port Technology Instrument)

/-- Registration is an actual source input, but is not a material period,
repair instruction, fee payment, or replacement of the current phase. -/
theorem registration_preserves_the_complete_state :
    Compile.next input depth count prefixLimit renewalLimit current (.review code) = current := by
  cases result : Compile.compile input depth count prefixLimit renewalLimit current (.review code) with
  | refused reason => simp only [Compile.next, result, Compile.Result.next]
  | accepted checked =>
      rcases checked with ⟨command, original⟩
      cases original with
      | review code admitted => simp only [Compile.next, result, Compile.Result.next, Actual.Command.next]

theorem registration_has_no_material_instructions :
    Compile.requests input depth count prefixLimit renewalLimit current (.review code) = [] := by
  cases result : Compile.compile input depth count prefixLimit renewalLimit current (.review code) with
  | refused reason =>
      cases reason with
      | reviewBusy code operation notBoundary source =>
          simp only [Compile.requests, result, Compile.Result.requests, Compile.refusalRequests]
  | accepted checked =>
      rcases checked with ⟨command, original⟩
      cases original with
      | review code admitted =>
          simp only [Compile.requests, result, Compile.Result.requests, Actual.Command.requests]

theorem registration_is_not_a_fee_or_a_period :
    (Compile.execution input depth count prefixLimit renewalLimit current (.review code)).items = [] ∧
      (Compile.execution input depth count prefixLimit renewalLimit current (.review code)).final = current.raw := by
  change (input.law.execute current.raw 0 (Compile.requests input depth count prefixLimit renewalLimit current (.review code))).items = [] ∧
    (input.law.execute current.raw 0 (Compile.requests input depth count prefixLimit renewalLimit current (.review code))).final = current.raw
  rw [registration_has_no_material_instructions]
  exact ⟨rfl, rfl⟩

theorem accepted_registration_comes_from_the_original_boundary
    (accepted : (Compile.compile input depth count prefixLimit renewalLimit current (.review code)).isAccepted = true) :
    (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit := by
  cases result : Compile.compile input depth count prefixLimit renewalLimit current (.review code) with
  | refused reason => simp only [result, Compile.Result.isAccepted, Bool.false_eq_true] at accepted
  | accepted checked =>
      rcases checked with ⟨command, original⟩
      cases original with
      | review code admitted => exact admitted

theorem an_admissible_registration_is_actually_accepted
    (admitted : (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit) :
    (Compile.compile input depth count prefixLimit renewalLimit current (.review code)).isAccepted = true := by
  cases result : Compile.compile input depth count prefixLimit renewalLimit current (.review code) with
  | accepted checked => rfl
  | refused reason =>
      cases reason with
      | reviewBusy code operation notBoundary source =>
          cases observed : Actual.receive input depth count prefixLimit renewalLimit current with
          | received issue exhausted => cases exhausted.symm.trans source
          | receivedBoundary word phase paid produced =>
              have same := Actual.Outcome.action.inj (produced.symm.trans source)
              cases same
              exact False.elim notBoundary
          | busy other otherNotBoundary produced =>
              simp only [observed, Actual.SubmissionOutcome.admissible] at admitted

theorem review_registration_is_checked_at_its_own_source :
    (Compile.compile input depth count prefixLimit renewalLimit current (.review code)).isAccepted = true ↔
      (Actual.receive input depth count prefixLimit renewalLimit current).admissible input depth count prefixLimit renewalLimit :=
  ⟨accepted_registration_comes_from_the_original_boundary input depth count prefixLimit renewalLimit current code,
    an_admissible_registration_is_actually_accepted input depth count prefixLimit renewalLimit current code⟩

#print axioms registration_preserves_the_complete_state
#print axioms registration_is_not_a_fee_or_a_period
#print axioms review_registration_is_checked_at_its_own_source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
