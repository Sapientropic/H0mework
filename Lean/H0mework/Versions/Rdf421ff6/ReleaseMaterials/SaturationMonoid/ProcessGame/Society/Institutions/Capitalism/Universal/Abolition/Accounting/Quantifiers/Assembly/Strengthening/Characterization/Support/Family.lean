import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel.AssetAuthority
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (visit : RootFace.Visit input)

/-- All three original family producers invert to exclusion at this
actual item. Merely being in the family does not assert actual port use. -/
theorem every_unified_family_member_exposes_the_same_original_permission_failure
    (item : RootFace.Item input visit) (port : Port)
    (member : port ∈ Root.Structural.familyAtVisit input visit item) :
    (RootFace.original input visit item).instruction? input = some item.val ∧
    (∃ person, PrivatePhase input.law item.val.before port person) ∧ ¬ NoAsymmetry input.law := by
  have source := Root.Structural.family_has_original_source_provenance input visit item port member
  have excluded : ∃ person, PrivatePhase input.law item.val.before port person := by
    rcases source with ⟨capital,_,_,phase⟩ | ⟨capital,_,_,phase⟩ | ⟨capital,_,_,fresh⟩
    · exact ⟨capital.dependency.proposal.access.recipient,phase⟩
    · exact ⟨capital.dependency.proposal.access.recipient,phase⟩
    · obtain ⟨_,_,person,_,phase⟩ := fresh
      exact ⟨person,phase⟩
  obtain ⟨person,phase⟩ := excluded
  exact ⟨RootFace.original_decodes_exact_item input visit item,⟨person,phase⟩,
    every_private_phase_refutes_the_exact_permission_support input.law _ _ _ phase⟩

theorem minimal_permission_support_empties_the_entire_generated_family
    (shared : NoAsymmetry input.law) (item : RootFace.Item input visit) :
    Root.Structural.familyAtVisit input visit item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  exact (every_unified_family_member_exposes_the_same_original_permission_failure input visit item port member).2.2 shared

/-- Here the original ControlUse supplies acceptance and required-port
incidence. Its same item then supplies the family failure above. -/
theorem every_actual_unified_control_use_exposes_its_complete_original_failure
    (control : ControlUse input.law (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current) (Root.Structural.familyAtVisit input visit)) :
    input.law.Valid control.item.val.before control.item.val.request ∧
    control.port ∈ input.law.requiredPorts control.item.val.before control.item.val.request ∧
    (type_of% (every_unified_family_member_exposes_the_same_original_permission_failure
      input visit control.item control.port control.controlled)) :=
  ⟨control.accepted,control.required,
    every_unified_family_member_exposes_the_same_original_permission_failure input visit control.item control.port control.controlled⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support
