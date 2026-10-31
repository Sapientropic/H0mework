import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Realization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Family

/-! Functional separation, not an enacted migration: opening the existing
permission interpretation eliminates its exclusive-control witnesses.  The
original root has not been changed or replaced by these theorems. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel.AssetAuthority

universe u
variable {Party Good Port Technology Instrument : Type u}

/-- No world state or need bundle is changed by this conclusion. -/
theorem open_interpretation_has_no_private_phase
    (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) (port : Port) (person : Party) :
    ¬ PrivatePhase (PublicFunction.physicalLaw law) current port person := by
  simp only [PrivatePhase, PublicFunction.physicalLaw, Bool.true_eq_false, and_false, not_false_eq_true]

section Local
variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (opened : ∀ technology port person, law.allowed technology port person = true)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

include opened in
omit [DecidableEq Port] in
theorem open_permissions_have_no_capital_kernel :
    ¬ Nonempty (Kernel.CapitalRelationKernel law current word) := by
  rintro ⟨capital⟩
  have denied := capital.checked.1.2.2.1.2
  rw [opened] at denied
  exact Bool.noConfusion denied

include opened in
theorem open_permissions_title_family_empty
    (localAttempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (item : OriginalItem law current word) :
    Kernel.AssetAuthority.generatedFamily law current word localAttempts item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  obtain ⟨capital, _source, _same, _phase⟩ :=
    Kernel.AssetAuthority.generatedFamily_original_provenance law current word localAttempts item port member
  exact open_permissions_have_no_capital_kernel law opened current word ⟨capital.dependency⟩

include opened in
theorem open_permissions_actual_surplus_family_empty (item : OriginalItem law current word) :
    Kernel.ActualSurplus.familyAt law current word item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  obtain ⟨capital, _source, _same, _phase⟩ :=
    Kernel.ActualSurplus.familyAt_has_original_witness law current word item port member
  exact open_permissions_have_no_capital_kernel law opened current word ⟨capital.dependency⟩

theorem open_interpretation_generated_families_empty
    (localAttempts : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument)
    (item : OriginalItem (PublicFunction.physicalLaw law) current word) :
    Kernel.AssetAuthority.generatedFamily (PublicFunction.physicalLaw law) current word localAttempts item = [] ∧
      Kernel.ActualSurplus.familyAt (PublicFunction.physicalLaw law) current word item = [] :=
  ⟨open_permissions_title_family_empty (PublicFunction.physicalLaw law) (fun _ _ _ => rfl)
      current word localAttempts item,
    open_permissions_actual_surplus_family_empty (PublicFunction.physicalLaw law) (fun _ _ _ => rfl)
      current word item⟩

omit [DecidableEq Port] in
/-- A uniform realization contract for every original lawful word.  The
counterpart keeps all five state coordinates and every old payment bundle;
no disappearance of a capital family is supplied as a premise. -/
theorem functional_realization_without_exclusive_control
    (legal : ∀ item ∈ law.rawItems current word, law.Valid item.before item.request)
    (members : List Party) :
    (PublicFunction.physicalLaw law).next current word = law.next current word ∧
    ((PublicFunction.physicalLaw law).rawItems current word = law.rawItems current word) ∧
    (Exit.Necessity.AllNeedsPaid (PublicFunction.physicalLaw law) current members word ↔
      Exit.Necessity.AllNeedsPaid law current members word) ∧
    ¬ Nonempty (Kernel.CapitalRelationKernel (PublicFunction.physicalLaw law) current word) :=
  ⟨original_full_next_is_preserved law current word legal,
    original_items_and_before_states_are_preserved law current word legal,
    original_needs_and_maintenance_are_preserved law current word legal members,
    open_permissions_have_no_capital_kernel (PublicFunction.physicalLaw law) (fun _ _ _ => rfl) current word⟩
end Local

section RootReadout
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (opened : ∀ technology port person, input.law.allowed technology port person = true)

include opened in
theorem open_permissions_history_family_empty (visit : History.Visit input)
    (item : RootFace.Item input visit) : History.generatedFamily input visit item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  exact History.self_supply_cannot_reuse_old_exclusion input visit item port
    (fun person _ => opened _ port person) member

include opened in
/-- This is a readout for an already given open-interpretation source.  It
constructs no root, installs no source and claims no actual institutional change. -/
theorem open_permissions_unified_source_family_empty (visit : History.Visit input)
    (item : RootFace.Item input visit) : Root.Structural.familyAtVisit input visit item = [] := by
  have title := open_permissions_title_family_empty input.law opened
    (Root.ProgrammeSource.rawCurrent input visit.current)
    (Root.ProgrammeSource.rawEvent input visit.current) input.localAttempts item
  have surplus := open_permissions_actual_surplus_family_empty input.law opened
    (Root.ProgrammeSource.rawCurrent input visit.current)
    (Root.ProgrammeSource.rawEvent input visit.current) item
  have history := open_permissions_history_family_empty input opened visit item
  simp only [Root.Structural.familyAtVisit, title, surplus, history, List.nil_append]
end RootReadout

#print axioms functional_realization_without_exclusive_control
#print axioms open_interpretation_generated_families_empty
#print axioms open_permissions_history_family_empty
#print axioms open_permissions_unified_source_family_empty

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions
