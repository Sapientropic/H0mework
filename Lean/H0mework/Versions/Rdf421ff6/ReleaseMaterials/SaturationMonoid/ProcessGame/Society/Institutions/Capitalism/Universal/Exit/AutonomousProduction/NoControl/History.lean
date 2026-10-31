import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.NoControl
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.History.Family

/-! Present self-supply cannot renew an old excluded-subject use.  No
assumption about earlier words, earlier owners or earlier capital is needed. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction

open Source.Program Source.ProgrammeControl Source.ProgrammeControl.Kernel.AssetAuthority
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] [DecidableEq Instrument] in
theorem self_supply_affected_subject_is_signer
    (item : ExecutionItem Party Good Port Technology Instrument) (self : At input.law item)
    (subject : Party) (member : subject ∈ History.affectedSubjects input item) :
    subject = item.request.signer := by
  obtain credits | command := List.mem_append.mp (List.mem_dedup.mp member)
  · obtain ⟨lot, present, selected⟩ := List.mem_filterMap.mp credits
    split at selected
    · exact (Option.some.inj selected).symm.trans (self_credit_member_is_signer input.law item self lot present)
    · contradiction
  · have kind := self.1
    cases operation : item.request.operation with
    | produce operator =>
        simp only [SelfOperation, operation] at kind
        simp only [operation, List.mem_singleton] at command
        exact command.trans kind.symm
    | use bearer goods purpose =>
        simp only [SelfOperation, operation] at kind
        simp only [operation, if_pos kind.2, List.mem_singleton] at command
        exact command.trans kind.1.symm
    | _ => simp only [SelfOperation, operation] at kind

theorem self_supply_history_family_empty (visit : History.Visit input)
    (item : RootFace.Item input visit) (self : At input.law item.val) :
    History.generatedFamily input visit item = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro port member
  obtain ⟨_capital, _generated, _same, _accepted, required, _subject⟩ :=
    History.generatedFamily_actual_control input visit item port member
  apply History.self_supply_cannot_reuse_old_exclusion input visit item port _ member
  intro subject present
  rw [self_supply_affected_subject_is_signer input item.val self subject present]
  exact self_required_port_is_allowed input.law item.val self port required

theorem self_supply_generates_three_empty_families (visit : History.Visit input)
    (allSelf : ∀ item ∈ Source.ProgrammeFace.Registered.traceItems input visit.current, At input.law item)
    (item : RootFace.Item input visit) :
    Kernel.AssetAuthority.generatedFamily input.law
        (Root.ProgrammeSource.rawCurrent input visit.current)
        (Root.ProgrammeSource.rawEvent input visit.current) input.localAttempts item = [] ∧
    Kernel.ActualSurplus.familyAt input.law
        (Root.ProgrammeSource.rawCurrent input visit.current)
        (Root.ProgrammeSource.rawEvent input visit.current) item = [] ∧
    History.generatedFamily input visit item = [] :=
  ⟨self_supply_title_family_empty input.law _ _ allSelf input.localAttempts item,
    self_supply_actual_surplus_family_empty input.law _ _ allSelf item,
    self_supply_history_family_empty input visit item (allSelf item.val item.property)⟩

#print axioms self_supply_affected_subject_is_signer
#print axioms self_supply_history_family_empty
#print axioms self_supply_generates_three_empty_families

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction
