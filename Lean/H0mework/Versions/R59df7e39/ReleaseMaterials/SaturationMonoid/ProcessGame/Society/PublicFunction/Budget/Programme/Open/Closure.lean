import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Dynamic
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.FlowCompletion

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Closure

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (fallback : Rule model.source.code)
  (reference : Program model.source.code)

def finiteCheck (readings : Dynamic.Cost.Coverage model.source.code (Dynamic.menu model domain)) (budget : Nat) : Prop :=
  Dynamic.cap model domain fallback reference readings ≤ budget ∧
    Support.SourceSupported model fallback domain reference ∧
    Selection.acceptable model domain fallback [reference,reference] reference reference

instance (readings : Dynamic.Cost.Coverage model.source.code (Dynamic.menu model domain)) (budget : Nat) :
    Decidable (finiteCheck model domain fallback reference readings budget) := by unfold finiteCheck;infer_instance

structure DynamicReceipt (budget : Nat) where
  readings : Dynamic.Cost.Coverage model.source.code (Dynamic.menu model domain)
  generated : Dynamic.countReadings model domain = .positive readings
  checked : finiteCheck model domain fallback reference readings budget
  refuted : ∀ program ∈ catalogue model domain budget,¬ Checked model domain fallback reference program
  query_exact : inquire model domain fallback reference budget = .pending refuted

inductive Receipt (budget : Nat) where
  | conservation (receipt : Completion.Receipt model domain fallback reference)
  | flow (receipt : FlowCompletion.Receipt model domain fallback reference)
  | dynamic (receipt : DynamicReceipt model domain fallback reference budget)

inductive Result (budget : Nat) where
  | complete (receipt : Receipt model domain fallback reference budget)
  | enquiry (query : Enquiry model domain fallback reference budget)
      (exact : query = inquire model domain fallback reference budget)

/-- Positive-cost sources retain the requested-layer search. A missing count can instead
close through an attained physical envelope, without imposing a bound on free words. -/
def prepare (budget : Nat) : Result model domain fallback reference budget :=
  match Completion.inspect model domain fallback reference with
  | some receipt => .complete (.conservation receipt)
  | none =>
    match generated : Dynamic.countReadings model domain with
    | .positive readings =>
      match queryExact : inquire model domain fallback reference budget with
      | .found discovery minimum same bounded => .enquiry (.found discovery minimum same bounded) queryExact.symm
      | .pending refuted =>
        if checked : finiteCheck model domain fallback reference readings budget then
          .complete (.dynamic ⟨readings,generated,checked,refuted,queryExact⟩)
        else .enquiry (.pending refuted) queryExact.symm
    | .unresolved _ _ _ _ _ =>
      match FlowCompletion.inspect model domain fallback reference with
      | some receipt => .complete (.flow receipt)
      | none => .enquiry (inquire model domain fallback reference budget) rfl

def dynamicReview (budget : Nat) : Bool := match Dynamic.countReadings model domain with
  | .positive readings => decide (finiteCheck model domain fallback reference readings budget ∧
      ¬ Within model domain fallback reference budget)
  | .unresolved _ _ _ _ _ => false

def Receipt.review {budget : Nat} : Receipt model domain fallback reference budget → Bool
  | .conservation _ => Completion.verify model domain fallback reference
  | .flow _ => FlowCompletion.verify model domain fallback reference
  | .dynamic _ => dynamicReview model domain fallback reference budget

def Receipt.observations {budget : Nat} : Receipt model domain fallback reference budget → List (Nat × Bool)
  | .conservation _ => []
  | .flow _ => []
  | .dynamic _ => [(budget,false)]

theorem every_completion_has_independent_source_review {budget : Nat}
    (receipt : Receipt model domain fallback reference budget) : receipt.review = true := by
  cases receipt with
  | conservation receipt => exact Completion.a_generated_completion_receipt_has_independent_review model domain fallback reference receipt
  | flow receipt => exact FlowCompletion.every_receipt_has_independent_review model domain fallback reference receipt
  | dynamic receipt =>
    change dynamicReview model domain fallback reference budget = true
    rw [dynamicReview,receipt.generated,decide_eq_true_eq]
    exact ⟨receipt.checked,fun ⟨program,inside,checked⟩ => receipt.refuted program inside checked⟩

theorem every_source_generated_completion_covers_the_entire_raw_domain {budget : Nat}
    (receipt : Receipt model domain fallback reference budget) :
    Supported model domain fallback reference ∧ Bounds.Accepted model domain fallback reference reference ∧
      ∀ raw : Program model.source.code,Supported model domain fallback raw →
        Bounds.Accepted model domain fallback reference raw → ¬ improves model domain fallback reference raw := by
  cases receipt with
  | conservation receipt =>
    exact Completion.a_generated_completion_receipt_certifies_the_entire_raw_domain model domain fallback reference receipt
  | flow receipt => exact FlowCompletion.every_receipt_covers_the_entire_raw_domain model domain fallback reference receipt
  | dynamic receipt =>
    have original := (Selection.acceptable_iff_every_common_external_opponent model domain fallback [reference,reference]
      reference reference (by simp) (by simp)).mp receipt.checked.2.2
    refine ⟨(Support.support_exact model fallback domain reference).mp receipt.checked.2.1,original,?_⟩
    intro raw supported accepted better
    obtain ⟨candidate,generated,checked⟩ := Dynamic.every_raw_improvement_occurs_within_the_source_generated_dynamic_cap
      model domain fallback reference receipt.readings raw supported accepted better
    exact receipt.refuted candidate
      (catalogue_is_monotone model domain (Dynamic.cap model domain fallback reference receipt.readings) budget
        receipt.checked.1 candidate generated) checked

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Closure
