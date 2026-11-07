import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Law

/-! These consumers use the original first instruction visit.  A source
surplus finding enters the unified family by its actual summand, so the
root test does not recompute unrelated history searches. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical

open Source.Program Source.ProgrammeControl Source.ProgrammeFace
open Source.ProgrammeControl.Kernel.AssetAuthority

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def controls (visit : RootFace.Visit input) :=
  controlInventory input.law (ProgrammeSource.rawCurrent input visit.current)
    (ProgrammeSource.rawEvent input visit.current) (familyAtVisit input visit)

def interpreted (visit : RootFace.Visit input) : Prop :=
  Exit.Interpretation.Checks input.law (ProgrammeSource.rawCurrent input visit.current)
    (ProgrammeSource.rawEvent input visit.current) (familyAtVisit input visit)
    (ActualBirth.participants input visit)

instance (visit : RootFace.Visit input) : Decidable (interpreted input visit) :=
  inferInstanceAs (Decidable (Exit.Interpretation.Checks _ _ _ _ _))

theorem actual_surplus_is_in_unified_controls (visit : RootFace.Visit input)
    (positive : 0 < (Kernel.ActualSurplus.discovered input.law
      (ProgrammeSource.rawCurrent input visit.current)
      (ProgrammeSource.rawEvent input visit.current)).length) : controls input visit ≠ [] := by
  let findings := Kernel.ActualSurplus.discovered input.law
    (ProgrammeSource.rawCurrent input visit.current) (ProgrammeSource.rawEvent input visit.current)
  have notEmpty : findings ≠ [] := by
    intro empty
    change 0 < findings.length at positive
    rw [empty] at positive
    exact Nat.not_lt_zero _ positive
  let witness := findings.head notEmpty
  obtain ⟨use⟩ := Kernel.ActualSurplus.discovered_generates_actual_control input.law _ _ witness
    (List.head_mem notEmpty)
  have included : use.port ∈ familyAtVisit input visit use.item := by
    simp only [familyAtVisit, List.mem_append]
    exact Or.inl (Or.inr use.controlled)
  have original := controlInventory_complete input.law _ _ (familyAtVisit input visit)
    use.item use.accepted use.port use.required included
  intro empty
  rw [show controlInventory input.law _ _ (familyAtVisit input visit) = [] from empty] at original
  exact List.not_mem_nil original

theorem interpreted_word_has_no_unified_control (visit : RootFace.Visit input)
    (checked : interpreted input visit) : controls input visit = [] := by
  by_contra nonempty
  let use := (controls input visit).head nonempty
  exact Exit.Interpretation.classified_control_is_preserved input.law _ _ _ _ checked use

#print axioms actual_surplus_is_in_unified_controls
#print axioms interpreted_word_has_no_unified_control

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Consumers.Canonical
