import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.RawInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Raw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Evolving.NativeCurrent (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (request : Request Party Good Port Technology Instrument)
  (selected : current.actual.proposal current.reader = .primitive request)

variable (complete : ¬ Public.Inquiry.HasWork current.frame current.actual.actual)
  (noConsents : request.consents = [])
  (valid : (Physical.Public.interpreter current.input).Valid
    (Public.Scope.actualState current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast current.actual.snapshot).raw request)

local notation "body" => current.raw complete
local notation "items" => Public.Accounting.items current.input current.depth current.count current.prefixLimit
  current.renewalLimit current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)

include selected noConsents valid

theorem the_actual_primitive_has_its_own_financial_head :
    ∃ item, items = [item] ∧
      Public.Accounting.item? (body).input (body).depth (body).count (body).prefixLimit (body).renewalLimit
        (body).oldPast (body).start (body).actual.actual = some item := by
  obtain ⟨item,single⟩ := List.length_eq_one_iff.mp
    (the_actual_raw_has_one_original_position current request selected complete noConsents valid)
  change items = [item] at single
  refine ⟨item,single,?_⟩
  change (if true then items[0]? else none) = some item
  rw [single]
  rfl

theorem the_actual_primitive_must_consume_its_financial_head :
    Public.Inquiry.HasWork (body).frame (body).actual.actual := by
  obtain ⟨item,_,present⟩ := the_actual_primitive_has_its_own_financial_head current request selected complete noConsents valid
  exact Or.inr (by rw [present]; rfl)

theorem an_actual_settlement_has_no_new_claim_admission
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (settlement : request.operation = .settle instrument debtor holder quantity) :
    Public.Accounting.registration? (body).input (body).depth (body).count (body).prefixLimit (body).renewalLimit
      (body).oldPast (body).start (body).actual.actual = none := by
  obtain ⟨item,single,present⟩ := the_actual_primitive_has_its_own_financial_head current request selected complete noConsents valid
  have notIssued := an_actual_settlement_body_cannot_create_another_loan current request selected complete
    noConsents valid instrument debtor holder quantity settlement item (by
      change item ∈ items
      rw [single]
      exact List.mem_cons_self)
  cases registered : Public.Accounting.registration? (body).input (body).depth (body).count (body).prefixLimit
      (body).renewalLimit (body).oldPast (body).start (body).actual.actual with
  | none => rfl
  | some born =>
      have same := Option.some.inj (born.present.symm.trans present)
      have issued := born.issued
      rw [same] at issued
      change Epoch.Finance.readNewClaim current.input current.depth current.count item = some born.claim at issued
      rw [notIssued] at issued
      cases issued

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
