import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Validity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Accounts

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  (current : Position input)
  (history : List (Compile.RawInput Party Good Port Technology Instrument))
  (request : Request Party Good Port Technology Instrument)
  (sameStart : current.start = Primitive.start history request)
  (bodyPaid : current.actual.actual.bodyPaid = true)
  (position : current.actual.actual.position = 0)
  (noConsents : request.consents = [])
  (valid : (Physical.Public.interpreter input).Valid (Primitive.state input 0 0 history).raw request)

include sameStart noConsents valid in
theorem the_active_body_has_the_same_original_item_inventory :
    (Public.Accounting.items input 0 0 0 0 [] current.start).map (Epoch.Finance.ActualItem.instruction input 0 0) =
      [⟨0,(Primitive.state input 0 0 history).raw,request⟩] := by
  rw [sameStart]
  exact Primitive.one_checked_source_primitive_generates_its_own_original_native_inventory input 0 0
    history request noConsents valid

include sameStart bodyPaid position noConsents valid in
theorem the_active_root_has_the_original_single_financial_head :
    ∃ item, Public.Accounting.items input 0 0 0 0 [] current.start = [item] ∧
      Public.Accounting.item? input 0 0 0 0 [] current.start current.actual.actual = some item ∧
      (item.instruction input 0 0).request = request := by
  have mapped := the_active_body_has_the_same_original_item_inventory current history request sameStart noConsents valid
  have length : (Public.Accounting.items input 0 0 0 0 [] current.start).length = 1 := by
    simpa only [List.length_map,List.length_cons,List.length_nil] using congrArg List.length mapped
  obtain ⟨item,single⟩ := List.length_eq_one_iff.mp length
  refine ⟨item,single,?_,?_⟩
  · simp only [Public.Accounting.item?,bodyPaid,if_true,position,single,List.getElem?_cons_zero]
  · rw [single] at mapped
    have h := congrArg (fun items => (items[0]?).map ExecutionItem.request) mapped
    simpa only [List.map_cons,List.map_nil,List.getElem?_cons_zero,Option.map_some,Option.some.injEq] using h

include sameStart bodyPaid position noConsents valid in
theorem the_original_nonissue_body_is_an_actual_native_action
    (notIssue : ∀ instrument debtor holder quantity,request.operation ≠ .issue instrument debtor holder quantity) :
    Public.Inquiry.HasWork current.frame current.actual.actual ∧
      Public.Accounting.registration? input 0 0 0 0 [] current.start current.actual.actual = none := by
  obtain ⟨item,_,present,word⟩ := the_active_root_has_the_original_single_financial_head current history request
    sameStart bodyPaid position noConsents valid
  refine ⟨Or.inr (by rw [present]; rfl),?_⟩
  cases parsed : Public.Accounting.registration? input 0 0 0 0 [] current.start current.actual.actual with
  | none => rfl
  | some born =>
      have same := Option.some.inj (born.present.symm.trans present)
      have origin := Epoch.Finance.readNewClaim_origin input 0 0 born.item born.claim born.issued
      have operation := born.claim.operation
      rw [origin,same,word] at operation
      exact (notIssue _ _ _ _ operation).elim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
