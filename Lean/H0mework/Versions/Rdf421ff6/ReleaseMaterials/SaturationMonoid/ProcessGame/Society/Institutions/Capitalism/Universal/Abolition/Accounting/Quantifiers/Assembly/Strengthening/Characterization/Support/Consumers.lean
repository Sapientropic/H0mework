import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Exact
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Local
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Classification

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support

open Source.Program Source.ProgrammeControl
noncomputable section
open Models

/-- Both one-atom obstructions are sufficient. The fourth matrix cell
is an actual complete source circuit, not an abstract denial by itself. -/
theorem the_actual_permission_family_has_exactly_the_minimal_support_boundary
    (ownerGranted recipientGranted : Bool) :
    NoAsymmetry (Permissions.law ownerGranted recipientGranted) ↔
      ownerGranted = false ∨ recipientGranted = true := by
  constructor
  · intro shared
    cases ownerGranted with
    | false => exact Or.inl rfl
    | true =>
      cases recipientGranted with
      | true => exact Or.inr rfl
      | false =>
        have allowed := shared (Permissions.state 0 0) false true rfl
        exact False.elim (Bool.noConfusion allowed)
  · intro blocked
    exact (no_asymmetry_iff_no_private_phase _).2
      (Permissions.either_single_blocking_atom_excludes_every_private_phase ownerGranted recipientGranted blocked)

theorem the_actual_permission_family_no_capital_contract_has_exactly_two_obstructions
    (ownerGranted recipientGranted : Bool) :
    Global.NoCapital (Permissions.law ownerGranted recipientGranted) ↔
      ownerGranted = false ∨ recipientGranted = true :=
  (the_existing_no_capital_contract_iff_its_minimal_permission_support _).trans
    (the_actual_permission_family_has_exactly_the_minimal_support_boundary ownerGranted recipientGranted)

/-- This converse is source-family-specific: its paid access, real need,
reciprocity and disposal are generated before the permission test. -/
theorem actual_capital_regeneration_iff_failure_of_minimal_support_in_this_complete_source
    (ownerGranted recipientGranted : Bool) (clock : ℚ) (round : Nat) :
    Nonempty (Kernel.CapitalRelationKernel (Permissions.law ownerGranted recipientGranted)
      (Permissions.state clock round) Permissions.body) ↔
      ¬ NoAsymmetry (Permissions.law ownerGranted recipientGranted) := by
  rw [Permissions.capital_regeneration_is_exactly_the_two_actual_permission_atoms,
    the_actual_permission_family_has_exactly_the_minimal_support_boundary]
  cases ownerGranted <;> cases recipientGranted <;> decide

theorem the_actual_family_can_remove_capital_without_deleting_its_execution :
    Global.NoCapital (Permissions.law true true) ∧
      (type_of% Permissions.restoring_access_does_not_change_the_original_actual_execution) :=
  ⟨(the_actual_permission_family_no_capital_contract_has_exactly_two_obstructions true true).2 (Or.inr rfl),
    Permissions.restoring_access_does_not_change_the_original_actual_execution⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support
