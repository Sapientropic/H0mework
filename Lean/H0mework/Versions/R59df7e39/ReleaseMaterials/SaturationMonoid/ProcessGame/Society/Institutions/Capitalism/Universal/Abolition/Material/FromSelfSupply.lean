import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Checks
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.NoControl.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.AutonomousProduction.Material

/-! Consume the already generated autonomous production, rather than prove
its material and no-control costs again inside the new period checker. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

open Source.Program Source.ProgrammeControl
open Exit.AutonomousProduction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem self_step_technology
    (item : ExecutionItem Party Good Port Technology Instrument) (self : At input.law item) :
    (input.law.step item.before item.request).technology = item.before.technology := by
  rw [RawLaw.step, if_pos self.2.2.1]
  have kind := self.1
  cases operation : item.request.operation with
  | produce _ | use _ _ _ => simp only [RawLaw.paidStep, operation]
  | _ => simp only [SelfOperation, operation] at kind

omit [DecidableEq Port] in
private theorem self_execution_technology
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (index : Nat)
    (checked : ∀ item ∈ (input.law.execute current index word).items, At input.law item) :
    (input.law.execute current index word).final.technology = current.technology := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [RawLaw.execute, List.forall_mem_cons] at checked
      exact (ih _ (index + 1) checked.2).trans
        (self_step_technology input ⟨index, current, request⟩ checked.1)

theorem periodChecks_of_self_items
    (current : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument)
    (allSelf : ∀ item ∈ input.law.rawItems current word, At input.law item)
    (needs : Exit.Necessity.AllNeedsPaid input.law current members word)
    (policy : PolicyExplained input) : PeriodChecks input current members word := by
  refine ⟨?_, needs, ⟨?_, ?_⟩, ?_, policy⟩
  · intro item present
    have self := allSelf item present
    have same : withoutControllerConsents item.request = item.request := by
      have empty := self.2.1
      cases request : item.request
      simp only [request] at empty
      simp [withoutControllerConsents, empty]
    refine ⟨self.2.2.1, same ▸ self.2.2.1, ?_⟩
    intro lot paid _positive
    apply actual_debit_uses_own_stock input.law item self lot
    simpa only [RawLaw.actualDebit, if_pos self.2.2.1] using paid
  · apply List.length_eq_zero_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro use _inside
    have empty : localFamily input current word use.item = [] := by
      rw [localFamily,
        self_supply_title_family_empty input.law current word allSelf input.localAttempts,
        self_supply_actual_surplus_family_empty input.law current word allSelf]
      rfl
    exact List.not_mem_nil (empty ▸ use.controlled)
  · intro item inside port required fresh
    obtain ⟨_accepted, _required, subject, affected, exclusive⟩ := fresh
    have self := allSelf item inside
    have allowed := self_required_port_is_allowed input.law item self port required
    rw [self_supply_affected_subject_is_signer input item self subject affected] at exclusive
    exact Bool.noConfusion (allowed.symm.trans exclusive.2)
  · intro person _original
    have same : (input.law.next current word).technology = current.technology :=
      self_execution_technology input current word 0 allSelf
    rw [same]
    simp [TechniqueDominates]

theorem periodChecks_of_actual_self_supply
    (current : RawCurrent Party Good Technology Instrument) (members : List Party)
    (word : RawEvent Party Good Port Technology Instrument)
    (checked : Exit.AutonomousProduction.Checks input.law current members word)
    (policy : PolicyExplained input) : PeriodChecks input current members word :=
  periodChecks_of_self_items input current members word
    (fun item present => (checked.1 item present).1) checked.2 policy

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.periodChecks_of_actual_self_supply
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.periodChecks_of_self_items
