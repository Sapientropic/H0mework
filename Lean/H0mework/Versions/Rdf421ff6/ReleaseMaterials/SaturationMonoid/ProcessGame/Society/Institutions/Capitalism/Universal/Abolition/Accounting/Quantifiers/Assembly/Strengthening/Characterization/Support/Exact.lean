import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel.AssetAuthority
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (visit : RootFace.Visit input) (item : RootFace.Item input visit) (port : Port)

/-- Necessary and sufficient original support, not merely a list of
examples. Historical support alone does not replace current exclusion. -/
theorem original_source_failure_iff_unified_family_membership :
    port ∈ Root.Structural.familyAtVisit input visit item ↔
    ((∃ capital ∈ Kernel.AssetAuthority.discovered input.law (Root.ProgrammeSource.rawCurrent input visit.current)
        (Root.ProgrammeSource.rawEvent input visit.current) input.localAttempts,
      capital.dependency.proposal.access.port = port ∧
        PrivatePhase input.law item.val.before port capital.dependency.proposal.access.recipient) ∨
    (∃ capital ∈ Kernel.ActualSurplus.discovered input.law (Root.ProgrammeSource.rawCurrent input visit.current)
        (Root.ProgrammeSource.rawEvent input visit.current),
      capital.dependency.proposal.access.port = port ∧
        PrivatePhase input.law item.val.before port capital.dependency.proposal.access.recipient) ∨
    (∃ capital ∈ History.Discovery.discovered input (History.actual input visit),
      capital.access.port = port ∧ History.FreshControl input port item.val)) := by
  constructor
  · exact Root.Structural.family_has_original_source_provenance input visit item port
  · intro source
    simp only [Root.Structural.familyAtVisit,List.mem_append]
    rcases source with ⟨capital,listed,same,phase⟩ | ⟨capital,listed,same,phase⟩ | ⟨capital,listed,same,fresh⟩
    · left; left
      apply List.mem_filterMap.mpr
      refine ⟨capital,listed,?_⟩
      rw [same,if_pos phase]
    · left; right
      apply List.mem_filterMap.mpr
      refine ⟨capital,listed,?_⟩
      rw [same,if_pos phase]
    · right
      apply List.mem_filterMap.mpr
      refine ⟨capital,listed,?_⟩
      rw [same,if_pos fresh]

/-- Acceptance and actual required-port incidence are independent source
checks. The finite family criterion then constructs the original ControlUse. -/
theorem actual_control_use_exists_iff_its_original_execution_checks :
    (∃ control : ControlUse input.law (Root.ProgrammeSource.rawCurrent input visit.current)
      (Root.ProgrammeSource.rawEvent input visit.current) (Root.Structural.familyAtVisit input visit),
      control.item = item ∧ control.port = port) ↔
    input.law.Valid item.val.before item.val.request ∧
      port ∈ input.law.requiredPorts item.val.before item.val.request ∧
      port ∈ Root.Structural.familyAtVisit input visit item := by
  constructor
  · rintro ⟨control,sameItem,samePort⟩
    cases sameItem
    cases samePort
    exact ⟨control.accepted,control.required,control.controlled⟩
  · rintro ⟨accepted,required,controlled⟩
    exact ⟨⟨item,accepted,port,required,controlled⟩,rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support
