import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census.Restriction
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census.Scope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : PublicFunction.OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (pair : Material.Migration.CodePair Party Good Port Technology Instrument)

def Checks : Prop :=
  Actual.Migration.Checks source.input (Actual.origin source.input depth count)
    (state source depth count prefixLimit renewalLimit current).raw
    (scope source depth count prefixLimit renewalLimit current pair) pair ∧
      Migration.SlotsKept source depth count prefixLimit renewalLimit current pair

theorem to_original_checks (checked : Checks source depth count prefixLimit renewalLimit current pair) :
    Migration.Checks source depth count prefixLimit renewalLimit current pair :=
  ⟨actual_migration_restrict source.input (Actual.origin source.input depth count)
    (state source depth count prefixLimit renewalLimit current).raw
    (Actual.members source.input depth count) (scope source depth count prefixLimit renewalLimit current pair)
    (every_original_member_is_in_scope source depth count prefixLimit renewalLimit current pair)
    pair checked.1, checked.2⟩

theorem to_original_actual_migration (checked : Checks source depth count prefixLimit renewalLimit current pair) :
    Actual.Migration.Checks source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw (Actual.members source.input depth count) pair :=
  (to_original_checks source depth count prefixLimit renewalLimit current pair checked).1

inductive Problem : Type
  | responsibility (issue : Actual.Migration.Issue source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw
      (scope source depth count prefixLimit renewalLimit current pair) pair)
  | original (issue : Migration.Problem source depth count prefixLimit renewalLimit current pair)

theorem Problem.refutes (problem : Problem source depth count prefixLimit renewalLimit current pair) :
    ¬ Checks source depth count prefixLimit renewalLimit current pair := by
  intro checked
  cases problem with
  | responsibility issue => exact issue.refutes source.input _ _ _ pair checked.1
  | original issue =>
      exact issue.refutes source depth count prefixLimit renewalLimit current pair
        (to_original_checks source depth count prefixLimit renewalLimit current pair checked)

inductive Check : Type
  | accepted (checked : Checks source depth count prefixLimit renewalLimit current pair)
  | refused (problem : Problem source depth count prefixLimit renewalLimit current pair)

/-- The census is recomputed from the completed physical prefix. Original
service diagnostics retain their existing slot and fixed windows. -/
def inspect : Check source depth count prefixLimit renewalLimit current pair :=
  match Actual.Migration.inspect source.input (Actual.origin source.input depth count)
      (state source depth count prefixLimit renewalLimit current).raw
      (scope source depth count prefixLimit renewalLimit current pair) pair with
  | .refused issue => .refused (.responsibility issue)
  | .accepted actual =>
      match Migration.inspect source depth count prefixLimit renewalLimit current pair with
      | .refused issue => .refused (.original issue)
      | .accepted original => .accepted ⟨actual, original.2⟩

instance : Decidable (Checks source depth count prefixLimit renewalLimit current pair) :=
  match inspect source depth count prefixLimit renewalLimit current pair with
  | .accepted checked => isTrue checked
  | .refused problem => isFalse (problem.refutes source depth count prefixLimit renewalLimit current pair)

#print axioms to_original_actual_migration
#print axioms inspect
#print axioms Problem.refutes

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Census
