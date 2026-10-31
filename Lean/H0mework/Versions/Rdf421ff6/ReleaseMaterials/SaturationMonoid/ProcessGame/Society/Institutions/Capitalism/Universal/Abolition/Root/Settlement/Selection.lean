import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement.Context
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Planner
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.NeedFloor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count))

def alphabet : List (Request Party Good Port Technology Instrument) :=
  input.localAttempts (initial input depth count datum) ++ ProgrammeSource.wordAt input (initial input depth count datum)

def rawCandidates (limit : Nat) : List (RawEvent Party Good Port Technology Instrument) :=
  PublicFunction.words (alphabet input depth count datum) limit

def originalNeedFloor (word : RawEvent Party Good Port Technology Instrument) : Prop :=
  Material.OriginalNeedFloor input (Continuation.initial input (oldFrame input depth count))
    (initial input depth count datum) (members input depth count) word

instance (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (originalNeedFloor input depth count datum word) := by
  unfold originalNeedFloor
  infer_instance

def candidates (limit : Nat) : List (RawEvent Party Good Port Technology Instrument) :=
  (rawCandidates input depth count datum limit).filter (fun word =>
    decide (NonFinancial word ∧ originalNeedFloor input depth count datum word))

theorem candidate_is_nonfinancial (limit : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (present : word ∈ candidates input depth count datum limit) : NonFinancial word :=
  (of_decide_eq_true (List.mem_filter.mp present).2).1

theorem candidate_keeps_original_need_floor (limit : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (present : word ∈ candidates input depth count datum limit) : originalNeedFloor input depth count datum word :=
  (of_decide_eq_true (List.mem_filter.mp present).2).2

def rawSelection (limit : Nat) := Material.compileRawPeriod input (initial input depth count datum)
  (members input depth count) (candidates input depth count datum limit)

structure Selected (limit : Nat) where
  private mk ::
  payment : Review.PaymentAt input.law (Admission.code input depth count datum).request
    (Continuation.initial input (oldFrame input depth count))
  paid_at_original_source : Admission.result input depth count datum = .inl payment
  plan : Material.RawPeriodPlanAt input (initial input depth count datum) (members input depth count)
    (candidates input depth count datum limit)
  selected_at_original_source : rawSelection input depth count datum limit = .accepted plan

inductive Outcome (limit : Nat) where
  | selected (selection : Selected input depth count datum limit)
  | reviewBlocked (blocked : Review.Blockage input.law (Admission.code input depth count datum).request
      (Admission.code input depth count datum).scope (Continuation.initial input (oldFrame input depth count)))
      (original : Admission.result input depth count datum = .inr blocked)
  | periodBlocked (obstruction : Material.RawPeriodObstructionAt input (initial input depth count datum)
      (members input depth count) (candidates input depth count datum limit))
      (original : rawSelection input depth count datum limit = .obstructed obstruction)

def select (limit : Nat) : Outcome input depth count datum limit :=
  match review : Admission.result input depth count datum with
  | .inr blocked => .reviewBlocked blocked review
  | .inl payment => match planned : rawSelection input depth count datum limit with
    | .accepted plan => .selected ⟨payment, review, plan, planned⟩
    | .obstructed obstruction => .periodBlocked obstruction planned

namespace Selected
variable {input depth count datum} {limit : Nat}
  (selected : Selected input depth count datum limit)

theorem nonfinancial : NonFinancial selected.plan.word :=
  candidate_is_nonfinancial input depth count datum limit selected.plan.word selected.plan.generated

theorem original_floor : originalNeedFloor input depth count datum selected.plan.word :=
  candidate_keeps_original_need_floor input depth count datum limit selected.plan.word selected.plan.generated

theorem source_word : selected.plan.word.length ≤ limit ∧
    ∀ request ∈ selected.plan.word, request ∈ alphabet input depth count datum :=
  (PublicFunction.mem_words_iff _ _ _).mp (List.mem_filter.mp selected.plan.generated).1

theorem every_original_member_is_paid (person : Party) (member : person ∈ members input depth count) :
    Exit.Necessity.BundlePaid input.law (initial input depth count datum) selected.plan.word person
      (input.law.necessities (initial input depth count datum) person) .necessity ∧
    Exit.Necessity.BundlePaid input.law (initial input depth count datum) selected.plan.word person
      (input.law.mandatoryMaintenance (initial input depth count datum) person) .maintenance :=
  Material.checked_period_original_member_needs input _ _ _ selected.plan.checked person member

end Selected

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Settlement
