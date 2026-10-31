import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred.Candidates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (members : List Party)
  (prefixLimit renewalLimit : Nat)

private structure Scanned (seed : P input origin current members prefixLimit renewalLimit)
    (remaining : List (P input origin current members prefixLimit renewalLimit)) where
  plan : P input origin current members prefixLimit renewalLimit
  advances : plan = seed ∨ Better input origin current members prefixLimit renewalLimit seed plan
  maximal : ∀ other ∈ remaining, ¬ Better input origin current members prefixLimit renewalLimit plan other

private theorem cannot_improve_seed
    {seed : P input origin current members prefixLimit renewalLimit} {remaining}
    (result : Scanned input origin current members prefixLimit renewalLimit seed remaining) :
    ¬ Better input origin current members prefixLimit renewalLimit result.plan seed := by
  intro backward
  rcases result.advances with same | forward
  · apply better_irreflexive input origin current members prefixLimit renewalLimit seed
    simpa only [same] using backward
  · exact better_irreflexive input origin current members prefixLimit renewalLimit seed
      (better_transitive input origin current members prefixLimit renewalLimit forward backward)

private def scan (seed : P input origin current members prefixLimit renewalLimit) :
    (remaining : List (P input origin current members prefixLimit renewalLimit)) →
      Scanned input origin current members prefixLimit renewalLimit seed remaining
  | [] => ⟨seed, .inl rfl, by simp⟩
  | head :: tail =>
      if improves : Better input origin current members prefixLimit renewalLimit seed head then
        let result := scan head tail
        { plan := result.plan
          advances := .inr (by
            rcases result.advances with same | further
            · exact same.symm ▸ improves
            · exact better_transitive input origin current members prefixLimit renewalLimit improves further)
          maximal := by
            intro other present
            rcases List.mem_cons.mp present with same | later
            · subst other
              exact cannot_improve_seed input origin current members prefixLimit renewalLimit result
            · exact result.maximal other later }
      else
        let result := scan seed tail
        { plan := result.plan
          advances := result.advances
          maximal := by
            intro other present
            rcases List.mem_cons.mp present with same | later
            · subst other
              intro backward
              rcases result.advances with unchanged | forward
              · exact improves (unchanged ▸ backward)
              · exact improves (better_transitive input origin current members prefixLimit renewalLimit forward backward)
            · exact result.maximal other later }

structure Selected where
  private mk ::
  plan : P input origin current members prefixLimit renewalLimit
  maximal : ∀ other ∈ candidates input origin current members prefixLimit renewalLimit,
    ¬ Better input origin current members prefixLimit renewalLimit plan other

/-- Source-generated candidates are scanned without a price weight. The
chosen feasible plan has no feasible source plan that strictly improves all
material shares and the actual time window. -/
def choose : Option (Selected input origin current members prefixLimit renewalLimit) :=
  match exactList : candidates input origin current members prefixLimit renewalLimit with
  | [] => none
  | head :: tail =>
      let result := scan input origin current members prefixLimit renewalLimit head tail
      some ⟨result.plan, by
        intro other present
        rw [exactList] at present
        rcases List.mem_cons.mp present with same | later
        · subst other
          exact cannot_improve_seed input origin current members prefixLimit renewalLimit result
        · exact result.maximal other later⟩

theorem choose_none_iff_empty : choose input origin current members prefixLimit renewalLimit = none ↔
    candidates input origin current members prefixLimit renewalLimit = [] := by
  unfold choose
  split <;> simp_all

#print axioms choose
#print axioms choose_none_iff_empty

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Preferred
