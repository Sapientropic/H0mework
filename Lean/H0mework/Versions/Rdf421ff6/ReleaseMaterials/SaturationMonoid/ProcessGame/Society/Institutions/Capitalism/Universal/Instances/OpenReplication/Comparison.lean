import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication.Source

/-!
# Delivery, fuel and action comparison on the same task

Every quantity reads the corresponding RawLaw execution.  The welfare
weights are explicit valuations; strict improvement holds for every positive
combined valuation of retained fuel and avoided fuel consumption.  A batch
is a finite list of independent tasks, each reset to its declared initial
inventory.  It is not a repeated-use claim about one shared stock.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication
open Source.Program
open Exit

def usedFor (n : Nat) (word : List Input) (person good : Bool) (kind : Use) : ℚ :=
  (((law n).rawItems (initial n) word).map fun item =>
    match item.request.operation with
    | .use bearer _ purpose =>
        if bearer = person ∧ purpose = kind then
          flowAt ((law n).actualDebit item.before item.request) person good else 0
    | _ => 0).sum

def delivered (n : Nat) (word : List Input) : ℚ :=
  (law n).totalCredit ((law n).rawItems (initial n) word) true true

def reserve (n : Nat) (word : List Input) : ℚ :=
  ((law n).next (initial n) word).stock false false

def fuelConsumed (n : Nat) (word : List Input) : ℚ :=
  (initial n).stock false false - reserve n word


private theorem totalCredit_as_credit (n : Nat) (word : List Input)
    (person good : Bool)
    (accepted : ∀ item ∈ (law n).rawItems (initial n) word,
      (law n).Valid item.before item.request) :
    (law n).totalCredit ((law n).rawItems (initial n) word) person good =
      (((law n).rawItems (initial n) word).map fun item =>
        flowAt ((law n).credit item.before item.request) person good).sum := by
  unfold RawLaw.totalCredit
  congr 1
  apply List.map_congr_left
  intro item inside
  rw [RawLaw.actualCredit, if_pos (accepted item inside)]

private theorem usedFor_as_debit (n : Nat) (word : List Input)
    (accepted : ∀ item ∈ (law n).rawItems (initial n) word,
      (law n).Valid item.before item.request)
    (person good : Bool) (kind : Use) :
    usedFor n word person good kind =
      (((law n).rawItems (initial n) word).map fun item =>
        match item.request.operation with
        | .use bearer _ purpose =>
            if bearer = person ∧ purpose = kind then
              flowAt ((law n).debit item.before item.request) person good else 0
        | _ => 0).sum := by
  unfold usedFor
  congr 1
  apply List.map_congr_left
  intro item inside
  simp only [RawLaw.actualDebit, if_pos (accepted item inside)]

theorem actual_delivery_equal (n : Nat) :
    delivered n (exclusive n) = (n : ℚ) + 1 ∧
      delivered n (publicRoute n) = (n : ℚ) + 1 := by
  constructor
  · unfold delivered
    rw [totalCredit_as_credit n _ true true (exclusive_accepted n), RawLaw.rawItems, exclusive_execution]
    simp [RawLaw.credit, produce, deliver, consume, maintain, law, flowAt, amount, locate]
  · unfold delivered
    rw [totalCredit_as_credit n _ true true (public_accepted n), RawLaw.rawItems, public_execution]
    simp [RawLaw.credit, produce, deliver, consume, maintain, openAccess, law, flowAt, amount, locate]

theorem actual_necessity_equal (n : Nat) :
    usedFor n (exclusive n) true true .necessity = (n : ℚ) + 1 ∧
      usedFor n (publicRoute n) true true .necessity = (n : ℚ) + 1 := by
  constructor
  · rw [usedFor_as_debit n _ (exclusive_accepted n), RawLaw.rawItems, exclusive_execution]
    simp [produce, deliver, consume, maintain, RawLaw.debit, flowAt, amount, locate]
  · rw [usedFor_as_debit n _ (public_accepted n), RawLaw.rawItems, public_execution]
    simp [produce, deliver, consume, maintain, openAccess, RawLaw.debit, flowAt, amount, locate]

theorem actual_maintenance_equal (n : Nat) :
    usedFor n (exclusive n) false false .maintenance = 1 ∧
      usedFor n (publicRoute n) false false .maintenance = 1 := by
  constructor
  · rw [usedFor_as_debit n _ (exclusive_accepted n), RawLaw.rawItems, exclusive_execution]
    simp [produce, deliver, consume, maintain, RawLaw.debit, flowAt, amount, locate]
  · rw [usedFor_as_debit n _ (public_accepted n), RawLaw.rawItems, public_execution]
    simp [produce, deliver, consume, maintain, openAccess, RawLaw.debit, flowAt, amount, locate]

theorem reserve_exact (n : Nat) :
    reserve n (exclusive n) = 1 ∧ reserve n (publicRoute n) = (n : ℚ) + 2 := by
  simp [reserve, RawLaw.next, exclusive_execution, public_execution, state]

theorem fuelConsumed_exact (n : Nat) :
    fuelConsumed n (exclusive n) = (n : ℚ) + 4 ∧
      fuelConsumed n (publicRoute n) = 3 := by
  simp only [fuelConsumed, (reserve_exact n).1, (reserve_exact n).2]
  constructor <;> dsimp [initial, state] <;> ring

theorem no_fuel_credit (n : Nat) :
    (law n).totalCredit ((law n).rawItems (initial n) (exclusive n)) false false = 0 ∧
      (law n).totalCredit ((law n).rawItems (initial n) (publicRoute n)) false false = 0 := by
  constructor
  · rw [totalCredit_as_credit n _ false false (exclusive_accepted n),
      RawLaw.rawItems, exclusive_execution]
    simp [RawLaw.credit, produce, deliver, consume, maintain, law, flowAt, amount, locate]
  · rw [totalCredit_as_credit n _ false false (public_accepted n),
      RawLaw.rawItems, public_execution]
    simp [RawLaw.credit, produce, deliver, consume, maintain, openAccess, law, flowAt, amount, locate]

theorem fuel_depletion_is_actual_debit (n : Nat) :
    (law n).totalDebit ((law n).rawItems (initial n) (exclusive n)) false false =
        fuelConsumed n (exclusive n) ∧
      (law n).totalDebit ((law n).rawItems (initial n) (publicRoute n)) false false =
        fuelConsumed n (publicRoute n) := by
  have left := (law n).actual_next_material_balance (initial n) (exclusive n) false false
  have right := (law n).actual_next_material_balance (initial n) (publicRoute n) false false
  rw [(no_fuel_credit n).1] at left
  rw [(no_fuel_credit n).2] at right
  change reserve n (exclusive n) + _ = _ + 0 at left
  change reserve n (publicRoute n) + _ = _ + 0 at right
  unfold fuelConsumed
  constructor <;> linarith

def personalCopy : Input := ⟨true, [], none, [], .produce true⟩

theorem same_person_gains_executable_action (n : Nat) :
    ¬ (law n).Valid ((law n).next (initial n) (exclusive n)) personalCopy ∧
      (law n).Valid ((law n).next (initial n) (publicRoute n)) personalCopy := by
  dsimp only [RawLaw.next]
  rw [exclusive_execution, public_execution]
  simp [RawLaw.Valid,
    RawLaw.SignerMatches, RawLaw.ClaimGuard, RawLaw.operationAllowed, RawPolicy.eval,
    RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, NonnegativeBundle,
    flowAt, amount, locate, law, state, personalCopy]

  positivity

#print axioms actual_delivery_equal
#print axioms actual_maintenance_equal
#print axioms fuelConsumed_exact
#print axioms same_person_gains_executable_action

/-- Weights are explicit preferences; quantities come from actual execution. -/
def welfare (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ)
    (n : Nat) (word : List Input) : ℚ :=
  serviceWeight * usedFor n word true true .necessity +
    upkeepWeight * usedFor n word false false .maintenance +
    reserveWeight * reserve n word - fuelWeight * fuelConsumed n word

theorem welfare_gap_exact (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ) (n : Nat) :
    welfare serviceWeight upkeepWeight reserveWeight fuelWeight n (publicRoute n) -
      welfare serviceWeight upkeepWeight reserveWeight fuelWeight n (exclusive n) =
        (reserveWeight + fuelWeight) * ((n : ℚ) + 1) := by
  unfold welfare
  rw [(actual_necessity_equal n).1, (actual_necessity_equal n).2,
    (actual_maintenance_equal n).1, (actual_maintenance_equal n).2,
    (reserve_exact n).1, (reserve_exact n).2,
    (fuelConsumed_exact n).1, (fuelConsumed_exact n).2]
  ring

theorem strict_welfare_for_every_positive_resource_valuation
    (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ)
    (resourceValued : 0 < reserveWeight + fuelWeight) (n : Nat) :
    welfare serviceWeight upkeepWeight reserveWeight fuelWeight n (exclusive n) <
      welfare serviceWeight upkeepWeight reserveWeight fuelWeight n (publicRoute n) := by
  have positive : 0 < (reserveWeight + fuelWeight) * ((n : ℚ) + 1) :=
    mul_pos resourceValued (by positivity)
  have gap := welfare_gap_exact serviceWeight upkeepWeight reserveWeight fuelWeight n
  linarith

def batchWelfare (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ)
    (tasks : List Nat) (shared : Bool) : ℚ :=
  (tasks.map fun n => welfare serviceWeight upkeepWeight reserveWeight fuelWeight n
    (if shared then publicRoute n else exclusive n)).sum

theorem batch_gap_exact (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ)
    (tasks : List Nat) :
    batchWelfare serviceWeight upkeepWeight reserveWeight fuelWeight tasks true -
      batchWelfare serviceWeight upkeepWeight reserveWeight fuelWeight tasks false =
        (reserveWeight + fuelWeight) * (tasks.map fun (k : Nat) => (k : ℚ) + 1).sum := by
  induction tasks with
  | nil => simp [batchWelfare]
  | cons n tasks ih =>
      have one := welfare_gap_exact serviceWeight upkeepWeight reserveWeight fuelWeight n
      simp only [batchWelfare, List.map_cons, List.sum_cons, ↓reduceIte,
        Bool.false_eq_true] at *
      nlinarith

theorem strict_welfare_for_every_nonempty_batch
    (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ)
    (resourceValued : 0 < reserveWeight + fuelWeight)
    (tasks : List Nat) (nonempty : tasks ≠ []) :
    batchWelfare serviceWeight upkeepWeight reserveWeight fuelWeight tasks false <
      batchWelfare serviceWeight upkeepWeight reserveWeight fuelWeight tasks true := by
  have positive : 0 < (tasks.map fun (k : Nat) => (k : ℚ) + 1).sum := by
    cases tasks with
    | nil => exact (nonempty rfl).elim
    | cons n tasks =>
        simp only [List.map_cons, List.sum_cons]
        have tail : 0 ≤ (tasks.map fun (k : Nat) => (k : ℚ) + 1).sum := by
          clear nonempty
          induction tasks with
          | nil => simp
          | cons k rest ih =>
              simp only [List.map_cons, List.sum_cons]
              positivity
        positivity
  have gap := batch_gap_exact serviceWeight upkeepWeight reserveWeight fuelWeight tasks
  have gain := mul_pos resourceValued positive
  linarith

theorem empty_batch_has_no_strict_advantage
    (serviceWeight upkeepWeight reserveWeight fuelWeight : ℚ) :
    batchWelfare serviceWeight upkeepWeight reserveWeight fuelWeight [] false =
      batchWelfare serviceWeight upkeepWeight reserveWeight fuelWeight [] true := rfl

theorem zero_resource_valuation_has_no_welfare_advantage
    (serviceWeight upkeepWeight : ℚ) (n : Nat) :
    welfare serviceWeight upkeepWeight 0 0 n (exclusive n) =
      welfare serviceWeight upkeepWeight 0 0 n (publicRoute n) := by
  have gap := welfare_gap_exact serviceWeight upkeepWeight 0 0 n
  linarith

theorem skipping_maintenance_is_rejected :
    ¬ Necessity.AllNeedsPaid (law 0) (initial 0) [false, true]
      [produce, deliver 0, consume 0] := by
  decide +kernel

#print axioms fuel_depletion_is_actual_debit
#print axioms strict_welfare_for_every_nonempty_batch
#print axioms skipping_maintenance_is_rejected

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.OpenReplication
