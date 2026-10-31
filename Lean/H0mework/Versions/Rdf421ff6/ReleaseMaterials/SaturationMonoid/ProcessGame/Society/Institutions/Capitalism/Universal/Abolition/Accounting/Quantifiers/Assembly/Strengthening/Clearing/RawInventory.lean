import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing.Inventory
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

include selected noConsents valid

theorem the_actual_raw_owns_its_one_original_native_item :
    (Public.Accounting.items (current.raw complete).input (current.raw complete).depth (current.raw complete).count
      (current.raw complete).prefixLimit (current.raw complete).renewalLimit (current.raw complete).oldPast
      (current.raw complete).start).map (Epoch.Finance.ActualItem.instruction current.input current.depth current.count) =
      [⟨0,(Public.Scope.actualState current.input current.depth current.count current.prefixLimit current.renewalLimit
        current.oldPast current.actual.snapshot).raw,request⟩] := by
  change (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
    current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)).map _ = _
  rw [the_current_primitive_uses_the_original_scope_delegate current request selected]
  exact the_primitive_body_owns_exactly_its_original_one_item current.input current.depth current.count
    current.prefixLimit current.renewalLimit current.oldPast current.actual.snapshot request noConsents valid

theorem the_actual_raw_has_one_original_position :
    (Public.Accounting.items (current.raw complete).input (current.raw complete).depth (current.raw complete).count
      (current.raw complete).prefixLimit (current.raw complete).renewalLimit (current.raw complete).oldPast
      (current.raw complete).start).length = 1 := by
  change (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
    current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)).length = 1
  have counted := congrArg List.length
    (the_actual_raw_owns_its_one_original_native_item current request selected complete noConsents valid)
  change (List.map (Epoch.Finance.ActualItem.instruction current.input current.depth current.count)
    (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
      current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader))).length = 1 at counted
  simpa only [List.length_map] using counted

theorem an_actual_settlement_body_cannot_create_another_loan
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (settlement : request.operation = .settle instrument debtor holder quantity)
    (item : Epoch.Finance.ActualItem current.input current.depth current.count)
    (listed : item ∈ Public.Accounting.items (current.raw complete).input (current.raw complete).depth (current.raw complete).count
      (current.raw complete).prefixLimit (current.raw complete).renewalLimit (current.raw complete).oldPast (current.raw complete).start) :
    Epoch.Finance.readNewClaim current.input current.depth current.count item = none := by
  have presented : item.instruction current.input current.depth current.count ∈
      (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
        current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)).map
          (Epoch.Finance.ActualItem.instruction current.input current.depth current.count) :=
    List.mem_map.mpr ⟨item,listed,rfl⟩
  have mapped := the_actual_raw_owns_its_one_original_native_item current request selected complete noConsents valid
  change (Public.Accounting.items current.input current.depth current.count current.prefixLimit current.renewalLimit
    current.oldPast (Factory.Direct.selectedStart current.full current.sourceActual current.reader)).map _ = _ at mapped
  rw [mapped] at presented
  have exactItem := List.mem_singleton.mp presented
  have operation : (item.instruction current.input current.depth current.count).request.operation =
      .settle instrument debtor holder quantity :=
    (congrArg (fun entry => entry.request.operation) exactItem).trans settlement
  cases found : Epoch.Finance.readNewClaim current.input current.depth current.count item with
  | none => rfl
  | some fresh =>
      have same := Epoch.Finance.readNewClaim_origin current.input current.depth current.count item fresh found
      have issue := fresh.operation
      rw [same,operation] at issue
      cases issue

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Clearing
