import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred.Choice

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (prefixLimit renewalLimit : Nat)

def compile : Outcome input origin current members prefixLimit renewalLimit :=
  match choose input origin current members prefixLimit renewalLimit with
  | some selected => .accepted selected.plan
  | none => compileMigration input origin current members prefixLimit renewalLimit

theorem selects_when_available
    (available : ∃ pair ∈ sourcePairs input current prefixLimit renewalLimit, PairChecks input origin current members pair) :
    ∃ plan, compile input origin current members prefixLimit renewalLimit = .accepted plan := by
  unfold compile
  cases chosen : choose input origin current members prefixLimit renewalLimit with
  | some selected => exact ⟨selected.plan, rfl⟩
  | none => exact compile_selects_when_available input origin current members prefixLimit renewalLimit available

theorem no_feasible_source_plan_can_strictly_improve_the_selection
    (plan : P input origin current members prefixLimit renewalLimit)
    (selected : compile input origin current members prefixLimit renewalLimit = .accepted plan)
    (other : P input origin current members prefixLimit renewalLimit) :
    ¬ Better input origin current members prefixLimit renewalLimit plan other := by
  unfold compile at selected
  cases chosen : choose input origin current members prefixLimit renewalLimit with
  | some best =>
      simp only [chosen, Outcome.accepted.injEq] at selected
      subst plan
      obtain ⟨actual, present, same⟩ := candidates_cover_every_checked_source_pair input origin current members
        prefixLimit renewalLimit other.pair other.generated other.checked
      have noBetter := best.maximal actual present
      change ¬ Dividend.Checks input.law current [best.plan.pair.1, best.plan.pair.2] [other.pair.1, other.pair.2]
      change ¬ Dividend.Checks input.law current [best.plan.pair.1, best.plan.pair.2] [actual.pair.1, actual.pair.2] at noBetter
      simpa only [same] using noBetter
  | none =>
      have empty := (choose_none_iff_empty input origin current members prefixLimit renewalLimit).mp chosen
      obtain ⟨actual, present, _⟩ := candidates_cover_every_checked_source_pair input origin current members
        prefixLimit renewalLimit other.pair other.generated other.checked
      rw [empty] at present
      exact (List.not_mem_nil present).elim

theorem typed_obstruction_preserves_full_source_coverage
    (obstruction : Obstruction input origin current members prefixLimit renewalLimit)
    (_produced : compile input origin current members prefixLimit renewalLimit = .obstructed obstruction) :
    ∀ pair ∈ sourcePairs input current prefixLimit renewalLimit, ¬ PairChecks input origin current members pair := by
  intro pair original checked
  obtain ⟨issue, _listed⟩ := obstruction.complete pair original
  exact issue.refutes input origin current members checked

#print axioms compile
#print axioms selects_when_available
#print axioms no_feasible_source_plan_can_strictly_improve_the_selection

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred
