import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- These limits bound source syntax enumeration. They do not measure
material payment, public-service deadlines, or elapsed real time. -/
def candidates := Material.Migration.sourcePairs source.input
  (state source depth count prefixLimit renewalLimit current).raw prefixLimit renewalLimit

structure Selection where
  private mk ::
  pair : Material.Migration.CodePair Party Good Port Technology Instrument
  generated : pair ∈ candidates source depth count prefixLimit renewalLimit current
  checked : Checks source depth count prefixLimit renewalLimit current pair

structure Obstruction where
  private mk ::
  problem : ∀ pair ∈ candidates source depth count prefixLimit renewalLimit current,
    Problem source depth count prefixLimit renewalLimit current pair

inductive Outcome : Type
  | selected (selection : Selection source depth count prefixLimit renewalLimit current)
  | exhausted (obstruction : Obstruction source depth count prefixLimit renewalLimit current)

/-- The second word is generated from the first word's own computed target.
Selection checks service, original livelihood, and renewed production in one
search; neither endpoint nor a successful pair is provided by the caller. -/
def compile : Outcome source depth count prefixLimit renewalLimit current :=
  match Material.inspectList (fun pair => ¬ Checks source depth count prefixLimit renewalLimit current pair)
      (candidates source depth count prefixLimit renewalLimit current) with
  | .failure pair generated absent => .selected ⟨pair, generated, not_not.mp absent⟩
  | .clear absent => .exhausted ⟨fun pair generated =>
      match inspect source depth count prefixLimit renewalLimit current pair with
      | .accepted checked => False.elim (absent pair generated checked)
      | .refused problem => problem⟩

theorem compile_selects_every_available_joint_pair
    (available : ∃ pair ∈ candidates source depth count prefixLimit renewalLimit current,
      Checks source depth count prefixLimit renewalLimit current pair) :
    ∃ selection, compile source depth count prefixLimit renewalLimit current = .selected selection := by
  cases result : compile source depth count prefixLimit renewalLimit current with
  | selected selection => exact ⟨selection, rfl⟩
  | exhausted obstruction =>
      obtain ⟨pair, generated, checked⟩ := available
      exact ((obstruction.problem pair generated).refutes source depth count prefixLimit renewalLimit current pair checked).elim

theorem exhausted_exactly_when_no_source_pair_is_jointly_admissible :
    (∃ obstruction, compile source depth count prefixLimit renewalLimit current = .exhausted obstruction) ↔
      ∀ pair ∈ candidates source depth count prefixLimit renewalLimit current,
        ¬ Checks source depth count prefixLimit renewalLimit current pair := by
  constructor
  · rintro ⟨obstruction, _⟩ pair generated checked
    exact (obstruction.problem pair generated).refutes source depth count prefixLimit renewalLimit current pair checked
  · intro absent
    cases result : compile source depth count prefixLimit renewalLimit current with
    | exhausted obstruction => exact ⟨obstruction, rfl⟩
    | selected selection => exact (absent selection.pair selection.generated selection.checked).elim

theorem selected_code_comes_from_both_original_source_alphabets
    (selection : Selection source depth count prefixLimit renewalLimit current) :
    (selection.pair.1.length ≤ prefixLimit ∧ ∀ request ∈ selection.pair.1,
      request ∈ Material.Migration.sourceAlphabet source.input
        (state source depth count prefixLimit renewalLimit current).raw) ∧
    (selection.pair.2.length ≤ renewalLimit ∧ ∀ request ∈ selection.pair.2,
      request ∈ Material.Migration.sourceAlphabet source.input
        (source.seed.law.next (state source depth count prefixLimit renewalLimit current).raw selection.pair.1)) :=
  (Material.Migration.sourcePairs_complete source.input _ _ _ selection.pair).mp selection.generated

#print axioms compile
#print axioms compile_selects_every_available_joint_pair
#print axioms exhausted_exactly_when_no_source_pair_is_jointly_admissible
#print axioms selected_code_comes_from_both_original_source_alphabets

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration
