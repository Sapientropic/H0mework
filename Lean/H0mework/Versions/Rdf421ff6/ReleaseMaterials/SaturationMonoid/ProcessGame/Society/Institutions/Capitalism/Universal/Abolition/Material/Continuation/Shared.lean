import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Retiming

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

open Source.Program Source.ProgrammeControl Exit.AutonomousProduction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Only ports actually required by this finite execution are inspected.
The law may retain other, unused private permissions. -/
def SharedRequiredPorts (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ∀ item ∈ input.law.rawItems current word,
    ∀ port ∈ input.law.requiredPorts item.before item.request,
      ∀ person, input.law.allowed item.before.technology port person = true

theorem sharedRequiredPorts_noFreshControl
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (shared : SharedRequiredPorts input current word) : NoFreshControl input current word := by
  refine ⟨?_, ?_⟩
  · apply List.length_eq_zero_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro use _present
    have available := shared use.item.val use.item.property use.port use.required
    have classified := use.controlled
    simp only [localFamily, List.mem_append] at classified
    rcases classified with title | surplus
    · obtain ⟨_, _, _, phase⟩ := Kernel.AssetAuthority.generatedFamily_original_provenance
        input.law current word input.localAttempts use.item use.port title
      exact Bool.noConfusion ((available _).symm.trans phase.2)
    · obtain ⟨_, _, _, phase⟩ := Kernel.ActualSurplus.familyAt_has_original_witness
        input.law current word use.item use.port surplus
      exact Bool.noConfusion ((available _).symm.trans phase.2)
  · intro item present port required fresh
    obtain ⟨_, _, person, _, phase⟩ := fresh
    exact Bool.noConfusion ((shared item present port required person).symm.trans phase.2)

omit [DecidableEq Port] in
theorem sharedRequiredPorts_retime (timing : input.law.TimeIndependent)
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (word : RawEvent Party Good Port Technology Instrument) :
    SharedRequiredPorts input (current.retime clock round) word ↔
      SharedRequiredPorts input current word := by
  have trace := executed_items_retime input.law timing current clock round 0 word
  change input.law.rawItems (current.retime clock round) word =
    (input.law.rawItems current word).map (retimed clock round) at trace
  simp only [SharedRequiredPorts, trace, List.forall_mem_map, retimed]
  rfl

/-- A finite source certificate for joint production. Actual transfers are
admitted; every positive debit still belongs to its genuine signer. -/
def SharedPeriod (current : RawCurrent Party Good Technology Instrument)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  ActualAndIndependent input current word ∧
    Exit.Necessity.AllNeedsPaid input.law current members word ∧
    SharedRequiredPorts input current word ∧ PolicyExplained input

omit [DecidableEq Port] in
theorem sharedPeriod_retime (timing : input.law.TimeIndependent)
    (current : RawCurrent Party Good Technology Instrument) (clock : ℚ) (round : Nat)
    (members : List Party) (word : RawEvent Party Good Port Technology Instrument) :
    SharedPeriod input (current.retime clock round) members word ↔
      SharedPeriod input current members word := by
  simp only [SharedPeriod, actualAndIndependent_retime input timing,
    needsPaid_retime input timing, sharedRequiredPorts_retime input timing]

theorem sharedPeriod_checks
    (current : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument)
    (paid : SharedPeriod input current members word)
    (retained : (input.law.next current word).technology = current.technology) :
    PeriodChecks input current members word := by
  refine ⟨paid.1, paid.2.1, sharedRequiredPorts_noFreshControl input current word paid.2.2.1,
    ?_, paid.2.2.2⟩
  intro person _member
  rw [retained]
  simp [TechniqueDominates]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.sharedRequiredPorts_noFreshControl
