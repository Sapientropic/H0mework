import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.Scan.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

private theorem original_renewal_source
    (before : Actual.State (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (phase : before.phase = .renewal word)
    (checked : Review.Guarded.Checks input (Actual.origin input depth count) before.raw (Actual.members input depth count) word) :
    Actual.decide input depth count prefixLimit renewalLimit before = .action (.renewal word phase checked) := by
  rcases before with ⟨raw, mode, remaining⟩
  change mode = .renewal word at phase
  subst mode
  obtain ⟨proof, inspected⟩ := Review.Guarded.inspect_selects_checked input (Actual.origin input depth count)
    raw (Actual.members input depth count) word checked
  simp only [Actual.decide, inspected]

theorem original_renewal_execution
    (before : Actual.State (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (word : RawEvent Party Good Port Technology Instrument)
    (phase : before.phase = .renewal word)
    (checked : Review.Guarded.Checks input (Actual.origin input depth count) before.raw (Actual.members input depth count) word) :
    Compile.requests input depth count prefixLimit renewalLimit before .advance = word ∧
      (Compile.next input depth count prefixLimit renewalLimit before .advance).raw = input.law.next before.raw word := by
  have original := original_renewal_source input depth count prefixLimit renewalLimit before word phase checked
  cases observed : Actual.dispatch input depth count prefixLimit renewalLimit before with
  | refusal obstruction refused => cases refused.symm.trans original
  | automatic generated =>
      have same := Actual.Outcome.action.inj (generated.source_exact.symm.trans original)
      simp only [Compile.requests, Compile.next, Compile.compile, observed, Compile.Result.requests,
        Compile.Result.next, Actual.Command.requests, Actual.Command.next, same, Actual.Operation.word, Actual.Operation.next,
        and_self]

namespace CandidateAt
variable {input depth count prefixLimit renewalLimit}
  {located : Located input depth count prefixLimit renewalLimit}
  {prepared : Prepared input depth count prefixLimit renewalLimit located}
  {start current : Physical.Cursor Party Good Port Technology Instrument}
  (candidate : CandidateAt input depth count prefixLimit renewalLimit located prepared start current)

def tailTarget := Physical.next (Physical.receive candidate.frontTarget .advance)

theorem original_tail_guard : Review.Guarded.Checks input (Actual.origin input depth count)
    (Material.rawAt input depth count prefixLimit renewalLimit candidate.frontTarget)
    (Actual.members input depth count) candidate.pair.2 := by
  have tail := candidate.original_command_feed.2.2.2
  have financial := Abolition.Material.Continuation.Balance.checked_word_is_nonfinancial .accumulating input.law
    (input.law.next (Material.rawAt input depth count prefixLimit renewalLimit current) candidate.pair.1) candidate.pair.2 tail.2.2.1
  change Review.Guarded.Checks input _
    (Physical.stateAt input depth count prefixLimit renewalLimit candidate.frontTarget.past).raw _ _
  rw [candidate.candidate_front_uses_the_original_compiler_and_locks_its_tail.1]
  exact ⟨financial, tail.2.1, tail.1⟩

theorem original_fixed_tail_is_really_executed :
    Compile.requests input depth count prefixLimit renewalLimit
        (Physical.stateAt input depth count prefixLimit renewalLimit candidate.frontTarget.past) .advance = candidate.pair.2 ∧
      Material.rawAt input depth count prefixLimit renewalLimit candidate.tailTarget =
        input.law.next (Material.rawAt input depth count prefixLimit renewalLimit candidate.frontTarget) candidate.pair.2 := by
  have executed := original_renewal_execution input depth count prefixLimit renewalLimit
    (Physical.stateAt input depth count prefixLimit renewalLimit candidate.frontTarget.past) candidate.pair.2
    candidate.candidate_front_uses_the_original_compiler_and_locks_its_tail.2 candidate.original_tail_guard
  refine ⟨executed.1, ?_⟩
  unfold Material.rawAt tailTarget
  rw [Physical.consumed_input_generates_its_own_after]
  exact executed.2

theorem the_paid_material_tail_still_has_its_original_native_responsibility :
    taskOfPayload (originalPayload input (Settlement.committedVisit input depth count).current) = some prepared.task.val ∧
      Material.rawAt input depth count prefixLimit renewalLimit candidate.tailTarget =
        input.law.next (Material.rawAt input depth count prefixLimit renewalLimit candidate.frontTarget) candidate.pair.2 :=
  ⟨prepared.task.property, candidate.original_fixed_tail_is_really_executed.2⟩

end CandidateAt

#print axioms CandidateAt.original_fixed_tail_is_really_executed
#print axioms CandidateAt.the_paid_material_tail_still_has_its_original_native_responsibility

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
