import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def step (current : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument)
    (review : Option (ReviewPhase.ContextAt input) := none) :=
  Physical.next (executionCursor input depth count prefixLimit renewalLimit current proposal (review := review))

theorem step_state (current : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument)
    (review : Option (ReviewPhase.ContextAt input) := none) :
    state input depth count prefixLimit renewalLimit (step input depth count prefixLimit renewalLimit current proposal (review := review)) =
      Compile.next input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current)
        (executionRaw input depth count prefixLimit renewalLimit current proposal (review := review)) :=
  Physical.consumed_input_generates_its_own_after input depth count prefixLimit renewalLimit _

theorem compile_advance_next
    (before : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (operation : Actual.Operation input depth count prefixLimit renewalLimit before)
    (source : Actual.decide input depth count prefixLimit renewalLimit before = .action operation) :
    Compile.next input depth count prefixLimit renewalLimit before .advance =
      operation.next input depth count prefixLimit renewalLimit := by
  cases observed : Actual.dispatch input depth count prefixLimit renewalLimit before with
  | refusal obstruction other => cases other.symm.trans source
  | automatic generated =>
      have same := Actual.Outcome.action.inj (generated.source_exact.symm.trans source)
      simp only [Compile.next, Compile.compile, observed, Compile.Result.next, Actual.Command.next, same]

theorem compile_advance_is_renewal
    (before : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (word : Source.Program.RawEvent Party Good Port Technology Instrument)
    (phase : before.phase = .renewal word)
    (checked : Review.Guarded.Checks input (Actual.origin input depth count) before.raw (Actual.members input depth count) word)
    (source : Actual.decide input depth count prefixLimit renewalLimit before = .action (.renewal word phase checked)) :
    WasRenewal input depth count prefixLimit renewalLimit (Compile.compile input depth count prefixLimit renewalLimit before .advance) := by
  cases observed : Actual.dispatch input depth count prefixLimit renewalLimit before with
  | refusal obstruction other => cases other.symm.trans source
  | automatic generated =>
      have same := Actual.Outcome.action.inj (generated.source_exact.symm.trans source)
      simp only [WasRenewal, Compile.compile, observed, isRenewal, same]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem previous_after_consuming (current : Physical.Cursor Party Good Port Technology Instrument)
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    previous? (Physical.next (Physical.receive current raw)) = some (Physical.receive current raw) := by
  rcases current with ⟨past, incoming⟩
  simp [previous?, Physical.next, Physical.receive, Physical.Prefix.eventCursor,
    Physical.Prefix.past_readback, List.get_eq_getElem, List.getElem_append_right]

theorem renewal_step_has_paid_boundary
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (proposal : Compile.RawInput Party Good Port Technology Instrument)
    (word : Source.Program.RawEvent Party Good Port Technology Instrument)
    (phase : (state input depth count prefixLimit renewalLimit current).phase = .renewal word)
    (checked : Review.Guarded.Checks input (Actual.origin input depth count)
      (state input depth count prefixLimit renewalLimit current).raw (Actual.members input depth count) word)
    (source : Actual.decide input depth count prefixLimit renewalLimit (state input depth count prefixLimit renewalLimit current) =
      .action (.renewal word phase checked))
    (mandatory : executionRaw input depth count prefixLimit renewalLimit current proposal = .advance) :
    PaidBoundary input depth count prefixLimit renewalLimit (step input depth count prefixLimit renewalLimit current proposal) := by
  unfold PaidBoundary step executionCursor
  rw [previous_after_consuming, mandatory]
  exact compile_advance_is_renewal input depth count prefixLimit renewalLimit _ word phase checked source

theorem checked_renewal_phase_selects_its_own_period
    (before : Actual.State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (word : Source.Program.RawEvent Party Good Port Technology Instrument)
    (phase : before.phase = .renewal word)
    (checked : Review.Guarded.Checks input (Actual.origin input depth count) before.raw (Actual.members input depth count) word) :
    Actual.decide input depth count prefixLimit renewalLimit before = .action (.renewal word phase checked) := by
  rcases before with ⟨raw, mode, remaining⟩
  change mode = .renewal word at phase
  subst mode
  obtain ⟨proof, inspected⟩ := Review.Guarded.inspect_selects_checked input (Actual.origin input depth count)
    raw (Actual.members input depth count) word checked
  simp only [Actual.decide, inspected]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory
