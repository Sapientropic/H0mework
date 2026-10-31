import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Head
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Evolution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (current : Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start current)

abbrev law := Epoch.Finance.Activation.law input depth count current.account (.inr registered.claim)
abbrev N := ExtendedNetwork prior.N (law current registered)

def family : Epoch.Finance.Future.Continuation.AccountFamily input depth count
    (N prior current registered) registered.admitted :=
  Epoch.Finance.Future.Continuation.admittedFamily prior current.account current.native (.inr registered.claim)

def nextCurrent : Current input depth count registered.admitted := registered.next

def oldSupport : world.Support := Accounting.support input depth count prior current

def initialSupport : (N prior current registered).Support := ⟨oldSupport prior current, some .pending⟩

def targetSupport : (N prior current registered).Support :=
  Accounting.support input depth count (family prior current registered) (nextCurrent current registered)

def firstStep : SourceFixedDebtAdmissionEventAt (law current registered) .pending :=
  Epoch.Finance.Activation.firstStep input depth count current.account (.inr registered.claim)

def admission : SourceGeneratedDebtAdmissionFirstWriteAt (oldSupport prior current) (firstStep current registered) :=
  generate (oldSupport prior current) (firstStep current registered)

theorem the_family_starts_at_the_literal_admitted_account :
    (family prior current registered).initial = registered.admitted := rfl

theorem the_current_is_the_original_consumed_head :
    nextCurrent current registered = registered.next ∧
      (nextCurrent current registered).account = registered.admitted ∧
      (nextCurrent current registered).position = current.position + 1 ∧
      (nextCurrent current registered).bodyPaid = true := ⟨rfl, rfl, rfl, rfl⟩

theorem the_born_financial_step_does_not_replay_the_physical_body :
    physical input depth count prefixLimit renewalLimit oldPast start (nextCurrent current registered) =
      physical input depth count prefixLimit renewalLimit oldPast start current := by
  simp only [physical, (the_current_is_the_original_consumed_head current registered).2.2.2, registered.paid, if_true]

theorem initial_row_has_positive_source_capacity :
    0 < (debtEntry (N := world) (law := law current registered) (oldSupport prior current) .pending).progressBudget :=
  (admission prior current registered).initialBudget_positive

theorem first_write_cannot_be_a_financial_settlement :
    ¬ Nonempty ((law current registered).SettlementAt (firstStep current registered).target) :=
  Epoch.Finance.Activation.registration_is_not_financial_settlement input depth count current.account (.inr registered.claim)

theorem the_first_write_installs_the_literal_actual_slot :
    registered.admitted.current.slots[current.account.current.slots.length]? =
      some (.live (Epoch.Finance.admission input depth count (.inr registered.claim)).toObligation) :=
  registered.the_first_write_installs_the_original_native_slot

#print axioms family
#print axioms admission
#print axioms the_born_financial_step_does_not_replay_the_physical_body
#print axioms first_write_cannot_be_a_financial_settlement

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born
