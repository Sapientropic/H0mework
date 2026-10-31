import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Reproduction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support

open Source.Program Source.ProgrammeControl
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

omit [DecidableEq Port] in
/-- Invert an actual kernel at its original access address and original
successor. No renamed current, new denial, or replay is introduced. -/
theorem every_kernel_exposes_its_actual_bearing_failure
    (capital : Kernel.CapitalRelationKernel law current word) :
    law.Valid capital.proposal.access.access.val.before capital.proposal.access.access.val.request ∧
    capital.proposal.access.port ∈ law.requiredPorts capital.proposal.access.access.val.before
      capital.proposal.access.access.val.request ∧
    PrivatePhase law capital.proposal.access.access.val.before capital.proposal.access.port capital.proposal.access.recipient ∧
    PrivatePhase law (law.next current word) capital.proposal.access.port capital.proposal.access.recipient ∧
    ¬ NoAsymmetry law := by
  have original := capital.original_control_and_reproduced_phase law current word
  exact ⟨original.1,original.2.1,original.2.2.1,original.2.2.2,
    every_private_phase_refutes_the_exact_permission_support law _ _ _ original.2.2.1⟩

omit [DecidableEq Port] in
theorem a_proper_title_retains_the_same_original_bearing_failure
    (capital : Kernel.AssetAuthority.ProperCapitalKernel law current word) :
    type_of% (every_kernel_exposes_its_actual_bearing_failure law current word capital.dependency) :=
  every_kernel_exposes_its_actual_bearing_failure law current word capital.dependency

omit [DecidableEq Port] in
/-- The appropriation evidence is preserved independently of the excluded
access; neither profit nor a title price supplies that access witness. -/
theorem every_actual_surplus_retains_its_dependency_and_original_appropriation
    (capital : Kernel.ActualSurplus.Witness law current word) :
    (type_of% (every_kernel_exposes_its_actual_bearing_failure law current word capital.dependency)) ∧
      (type_of% (capital.actual_appropriation_has_original_source law current word)) :=
  ⟨every_kernel_exposes_its_actual_bearing_failure law current word capital.dependency,
    capital.actual_appropriation_has_original_source law current word⟩

omit [DecidableEq Port] in
theorem every_reproduced_control_exposes_source_and_successor_failure
    (capital : ReproducedControl law current word) :
    (type_of% (capital.production_is_original_control_use law current word)) ∧
    (type_of% (capital.actual_necessary_life law current word)) ∧
    PrivatePhase law capital.proposal.production.val.before capital.proposal.port capital.proposal.recipient ∧
    PrivatePhase law (law.next current word) capital.proposal.port capital.proposal.recipient ∧
    ¬ NoAsymmetry law :=
  ⟨capital.production_is_original_control_use law current word,capital.actual_necessary_life law current word,
    capital.checked.2.2.1,capital.checked.2.2.2.2.1,
    every_private_phase_refutes_the_exact_permission_support law _ _ _ capital.checked.2.2.1⟩

theorem every_paid_private_reproduction_retains_all_needs_and_the_bearing_failure
    (capital : PrivateProductionReproduction law current word) :
    (type_of% (capital.actual_surplus_and_all_source_needs law current word)) ∧
      (type_of% (every_reproduced_control_exposes_source_and_successor_failure law current word
        (capital.control law current word))) :=
  ⟨capital.actual_surplus_and_all_source_needs law current word,
    every_reproduced_control_exposes_source_and_successor_failure law current word (capital.control law current word)⟩

theorem every_contribution_reproduction_retains_its_original_private_production
    (capital : CapitalContributionReproduction law current word) :
    (capital.privateProduction law current word).proposal = capital.proposal.reproduction ∧
      (type_of% (every_paid_private_reproduction_retains_all_needs_and_the_bearing_failure law current word
        (capital.privateProduction law current word))) :=
  ⟨capital.private_proposal_exact law current word,
    every_paid_private_reproduction_retains_all_needs_and_the_bearing_failure law current word
      (capital.privateProduction law current word)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support
