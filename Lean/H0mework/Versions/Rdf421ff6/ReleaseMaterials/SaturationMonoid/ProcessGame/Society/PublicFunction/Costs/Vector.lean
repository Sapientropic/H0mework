import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.FinancedSource
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Source goods retain their units. Liability repayments have their own
coordinate and cannot enter the operating-cost scalarization. Time is the
original clock increment, not an invented per-command charge. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Costs

open Institutions.Capitalism.Universal.Source.Program

universe u

inductive Coordinate (Good : Type u)
  | operating (good : Good)
  | debtPayment (good : Good)
  | elapsed
  deriving DecidableEq

abbrev CostVector (Good : Type u) := Coordinate Good → ℚ

def BoundedBy {Good : Type u} (cost bound : CostVector Good) : Prop :=
  ∀ coordinate, cost coordinate ≤ bound coordinate

def envelope {Good : Type u} : List (CostVector Good) → CostVector Good
  | [] => 0
  | first :: rest => fun coordinate => max (first coordinate) (envelope rest coordinate)

theorem member_bounded {Good : Type u} (cost : CostVector Good)
    (inventory : List (CostVector Good)) (inside : cost ∈ inventory) :
    BoundedBy cost (envelope inventory) := by
  induction inventory with
  | nil => cases inside
  | cons first rest ih =>
      rcases List.mem_cons.mp inside with rfl | later
      · exact fun coordinate => le_max_left _ _
      · exact fun coordinate => (ih later coordinate).trans (le_max_right _ _)

theorem envelope_nonnegative {Good : Type u} (inventory : List (CostVector Good)) :
    BoundedBy 0 (envelope inventory) := by
  induction inventory with
  | nil => exact fun _ => le_refl _
  | cons first rest ih => exact fun coordinate => (ih coordinate).trans (le_max_right _ _)

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def isDebtPayment (request : Request Party Good Port Technology Instrument) : Bool :=
  match request.operation with | .settle .. => true | _ => false

def itemCost (law : RawLaw Party Good Port Technology Instrument)
    (bearer : Party) (item : ExecutionItem Party Good Port Technology Instrument) : CostVector Good
  | .operating good => if isDebtPayment item.request then 0 else
      flowAt (law.actualDebit item.before item.request) bearer good
  | .debtPayment good => if isDebtPayment item.request then
      flowAt (law.actualDebit item.before item.request) bearer good else 0
  | .elapsed => 0

def wordCost (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (bearer : Party) : CostVector Good
  | .elapsed => max 0 (law.duration current)
  | coordinate => ((law.rawItems current word).map (fun item => itemCost law bearer item coordinate)).sum

omit [DecidableEq Instrument] in
theorem actual_debit_nonnegative (law : RawLaw Party Good Port Technology Instrument)
    (item : ExecutionItem Party Good Port Technology Instrument) (bearer : Party) (good : Good) :
    0 ≤ flowAt (law.actualDebit item.before item.request) bearer good := by
  by_cases accepted : law.Valid item.before item.request
  · simpa only [RawLaw.actualDebit, if_pos accepted, flowAt] using
      amount_nonnegative (law.debit item.before item.request) accepted.2.2.2.1 (bearer, good)
  · simp [RawLaw.actualDebit, accepted, flowAt, amount]

omit [DecidableEq Instrument] in
theorem itemCost_nonnegative (law : RawLaw Party Good Port Technology Instrument)
    (bearer : Party) (item : ExecutionItem Party Good Port Technology Instrument) :
    BoundedBy 0 (itemCost law bearer item) := by
  intro coordinate
  cases coordinate with
  | operating good | debtPayment good =>
      simp only [itemCost]
      split <;> first | exact le_refl _ | exact actual_debit_nonnegative law item bearer good
  | elapsed => exact le_refl _

theorem wordCost_nonnegative (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (bearer : Party) :
    BoundedBy 0 (wordCost law current word bearer) := by
  intro coordinate
  cases coordinate with
  | elapsed => exact le_max_left _ _
  | operating good | debtPayment good =>
      change 0 ≤ ((_ : List (ExecutionItem Party Good Port Technology Instrument)).map _).sum
      induction law.rawItems current word with
      | nil => exact le_refl _
      | cons item rest ih =>
          exact add_nonneg (itemCost_nonnegative law bearer item _) ih

theorem wordCost_partitions_actual_debit (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (bearer : Party) (good : Good) :
    wordCost law current word bearer (.operating good) +
        wordCost law current word bearer (.debtPayment good) =
      law.totalDebit (law.rawItems current word) bearer good := by
  simp only [wordCost, RawLaw.totalDebit]
  induction law.rawItems current word with
  | nil => simp
  | cons item rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have first : itemCost law bearer item (.operating good) +
          itemCost law bearer item (.debtPayment good) =
          flowAt (law.actualDebit item.before item.request) bearer good := by
        simp only [itemCost]
        cases isDebtPayment item.request <;> simp
      linarith

/-- Explicit source units select distinct goods; the full vector still keeps
every remaining Good coordinate. This record performs no conversion. -/
structure Units (Good : Type u) where
  money : Good
  energy : Good
  communication : Good
  separate : money ≠ energy ∧ money ≠ communication ∧ energy ≠ communication

/-- Prices are a declared valuation, never operational permission. The
aggregation laws below verify additivity and order in that same valuation. -/
structure Valuation (Good : Type u) where
  goodPrice : Good → ℚ
  goodPrice_nonnegative : ∀ good, 0 ≤ goodPrice good
  timePrice : ℚ
  timePrice_nonnegative : 0 ≤ timePrice

namespace Valuation

omit [DecidableEq Good]
variable [Fintype Good] (valuation : Valuation Good)

def aggregate (cost : CostVector Good) : ℚ :=
  (∑ good, valuation.goodPrice good * cost (.operating good)) +
    valuation.timePrice * cost .elapsed

theorem aggregate_add (left right : CostVector Good) :
    valuation.aggregate (left + right) = valuation.aggregate left + valuation.aggregate right := by
  simp only [aggregate, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem aggregate_mono {cost bound : CostVector Good} (bounded : BoundedBy cost bound) :
    valuation.aggregate cost ≤ valuation.aggregate bound := by
  apply add_le_add
  · exact Finset.sum_le_sum fun good _ =>
      mul_le_mul_of_nonneg_left (bounded (.operating good)) (valuation.goodPrice_nonnegative good)
  · exact mul_le_mul_of_nonneg_left (bounded .elapsed) valuation.timePrice_nonnegative

theorem debtPayment_excluded (left right : CostVector Good)
    (sameOperating : ∀ good, left (.operating good) = right (.operating good))
    (sameTime : left .elapsed = right .elapsed) :
    valuation.aggregate left = valuation.aggregate right := by
  simp only [aggregate, sameOperating, sameTime]

end Valuation

end SaturationMonoid.ProcessGame.Society.PublicFunction.Costs
