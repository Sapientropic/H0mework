import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Step
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Activation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

structure Registration (current : Current input depth count anchor) where
  private mk ::
  paid : current.bodyPaid = true
  item : Epoch.Finance.ActualItem input depth count
  present : item? input depth count prefixLimit renewalLimit oldPast start current = some item
  claim : Epoch.Finance.NewClaim input depth count
  issued : Epoch.Finance.readNewClaim input depth count item = some claim

def registration? (current : Current input depth count anchor) :
    Option (Registration input depth count prefixLimit renewalLimit oldPast start current) :=
  if paid : current.bodyPaid = true then
    match found : item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => none
    | some item => match issued : Epoch.Finance.readNewClaim input depth count item with
      | none => none
      | some claim => some ⟨paid, item, found, claim, issued⟩
  else none

namespace Registration

variable {input depth count prefixLimit renewalLimit oldPast start}
  {current : Current input depth count anchor}
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start current)

def admitted := Epoch.Finance.Activation.admitted input depth count current.account (.inr registered.claim)

def next : Current input depth count registered.admitted := current.afterIssued registered.paid registered.claim

def nativeAdmission : (Epoch.Finance.process input depth count).Run current.account.current registered.admitted.current :=
  .step .nil (.admit (P := Epoch.Finance.process input depth count) (.inr registered.claim))

theorem the_new_row_has_the_same_actual_source : registered.claim.origin = registered.item :=
  Epoch.Finance.readNewClaim_origin input depth count registered.item registered.claim registered.issued

theorem the_first_write_installs_the_original_native_slot :
    registered.admitted.current.slots[current.account.current.slots.length]? =
      some (.live (Epoch.Finance.admission input depth count (.inr registered.claim)).toObligation) :=
  Epoch.Finance.Activation.first_slot_is_the_actual_original_loan input depth count current.account (.inr registered.claim)

theorem the_born_current_consumes_exactly_the_registered_head :
    registered.next.account = registered.admitted ∧
      registered.next.position = current.position + 1 ∧ registered.next.bodyPaid = true := ⟨rfl, rfl, rfl⟩

end Registration

#print axioms registration?
#print axioms Registration.the_new_row_has_the_same_actual_source
#print axioms Registration.the_first_write_installs_the_original_native_slot
#print axioms Registration.the_born_current_consumes_exactly_the_registered_head

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
