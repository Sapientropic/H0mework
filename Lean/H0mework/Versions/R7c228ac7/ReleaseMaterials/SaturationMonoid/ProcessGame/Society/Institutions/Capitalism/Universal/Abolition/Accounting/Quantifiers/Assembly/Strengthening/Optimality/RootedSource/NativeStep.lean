import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Head

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

open private consumeItems from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

include sameStart bodyPaid position noConsents valid in
theorem the_root_consumes_the_identical_original_native_item :
    current.native.actual.actual.account =
      Primitive.accountAfter input 0 0 history [request] current.actual.actual.account := by
  obtain ⟨item,single,present,_⟩ := the_active_root_has_the_original_single_financial_head
    current history request sameStart bodyPaid position noConsents valid
  have consumed := Public.Accounting.every_actual_head_has_its_literal_source_account input 0 0 0 0 []
    current.start current.actual.actual bodyPaid item present
  change (Public.Accounting.nativeNext input 0 0 0 0 [] current.start current.actual.actual).account = _
  rw [consumed]
  change _ = Epoch.Finance.consumeVisit input 0 0 (Primitive.tag input 0 0 history request)
    (Primitive.visit input 0 0 history request) current.actual.actual.account
  unfold Epoch.Finance.consumeVisit
  change _ = consumeItems input 0 0 (Primitive.oneItems input 0 0 history request) current.actual.actual.account
  rw [sameStart] at single
  change Primitive.oneItems input 0 0 history request = [item] at single
  rw [single]
  rfl

include sameStart bodyPaid position noConsents valid in
theorem the_original_single_head_is_completely_consumed :
    current.native.actual.actual.bodyPaid = true ∧
      current.native.actual.actual.position = 1 ∧
      ¬ Public.Inquiry.HasWork current.native.frame current.native.actual.actual := by
  obtain ⟨item,single,present,_⟩ := the_active_root_has_the_original_single_financial_head
    current history request sameStart bodyPaid position noConsents valid
  have next : current.native.actual.actual = current.actual.actual.afterItem bodyPaid item := by
    change Public.Accounting.nativeNext input 0 0 0 0 [] current.start current.actual.actual = _
    rw [Public.Accounting.nativeNext,dif_pos bodyPaid,present]
  have fields := Public.Accounting.Current.after_item_reads_the_source_generated_native_account
    current.actual.actual bodyPaid item
  have paid : current.native.actual.actual.bodyPaid = true := by rw [next]; exact fields.2.2
  have index : current.native.actual.actual.position = 1 :=
    (congrArg (fun state : Public.Accounting.Current input 0 0 current.frame.anchor => state.position) next).trans
      (fields.2.1.trans (congrArg (fun i : Nat => i + 1) position))
  refine ⟨paid,index,?_⟩
  intro work
  rcases work with unpaid | head
  · cases paid.symm.trans unpaid
  · change (Public.Accounting.item? input 0 0 0 0 [] current.start current.native.actual.actual).isSome = true at head
    simp only [Public.Accounting.item?,paid,if_true,index,single,List.getElem?_cons_succ,
      List.getElem?_nil,Option.isSome_none] at head
    cases head

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
