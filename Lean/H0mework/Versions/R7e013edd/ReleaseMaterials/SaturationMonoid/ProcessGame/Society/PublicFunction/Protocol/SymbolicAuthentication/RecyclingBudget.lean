import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingLaw
import Mathlib.Data.Rat.Floor

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingBudget
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party)
open Repayment.Recovery (Good Current law)
open RecyclingLaw

structure Reserve (current : Current) (count : Nat) : Prop where
  producerFeed : 0 ≤ current.stock 1 .feedstock
  workerFeed : 0 ≤ current.stock 2 .feedstock
  workerWaste : 0 ≤ current.stock 2 .waste
  willing : current.technology.1 = true
  waste : 1 ≤ current.stock 1 .waste
  producerEnergy : (count : ℚ) ≤ current.stock 1 .energy
  producerLabor : (count : ℚ) ≤ current.stock 1 .labor
  workerEnergy : (count : ℚ) ≤ current.stock 2 .energy
  workerLabor : (count : ℚ) ≤ current.stock 2 .labor

def capacity (current : Current) : Nat :=
  min (min ⌊current.stock 1 .energy⌋₊ ⌊current.stock 1 .labor⌋₊)
    (min ⌊current.stock 2 .energy⌋₊ ⌊current.stock 2 .labor⌋₊)

def run (current : Current) : Nat → Current
  | 0 => current
  | count + 1 => run (law.next current word) count

def expected (current : Current) (count : Nat) : Current :=
  {current with
    stock := fun party good => current.stock party good +
      (if party = 1 ∧ good = .service then 3 * count else 0) -
      (if (party = 1 ∨ party = 2) ∧ (good = .energy ∨ good = .labor) then count else 0)
    clock := current.clock + count
    round := current.round + count}

theorem currentInputs (current : Current) (count : Nat) (reserve : Reserve current (count + 1)) : Inputs current := by
  refine ⟨reserve.producerFeed, reserve.workerFeed, reserve.workerWaste, reserve.willing, reserve.waste, ?_, ?_, ?_, ?_⟩
  all_goals have positive : (1 : ℚ) ≤ (count + 1 : Nat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le count)
  · exact positive.trans reserve.producerEnergy
  · exact positive.trans reserve.producerLabor
  · exact positive.trans reserve.workerEnergy
  · exact positive.trans reserve.workerLabor

theorem nextReserve (current : Current) (count : Nat) (reserve : Reserve current (count + 1)) :
    Reserve (law.next current word) count := by
  rw [actualNext current (currentInputs current count reserve)]
  refine ⟨?_, ?_, ?_, reserve.willing, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [successor] using reserve.producerFeed
  · simpa [successor] using reserve.workerFeed
  · simpa [successor] using reserve.workerWaste
  · simpa [successor] using reserve.waste
  · have h := reserve.producerEnergy
    norm_num [successor, show (Good.energy : Good) ≠ .service from by decide] at h ⊢
    linarith
  · have h := reserve.producerLabor
    norm_num [successor, show (Good.labor : Good) ≠ .service from by decide] at h ⊢
    linarith
  · have h := reserve.workerEnergy
    norm_num [successor, show (2 : Party) ≠ 1 from by decide] at h ⊢
    linarith
  · have h := reserve.workerLabor
    norm_num [successor, show (2 : Party) ≠ 1 from by decide] at h ⊢
    linarith

theorem expectedZero (current : Current) : expected current 0 = current := by
  apply RawCurrent.ext
  · funext party good; simp [expected]
  all_goals simp [expected]

theorem expectedSucc (current : Current) (count : Nat) :
    expected (successor current) count = expected current (count + 1) := by
  apply RawCurrent.ext
  · funext party good
    by_cases first : party = 1 <;> by_cases second : party = 2 <;> cases good <;>
      simp [expected, successor, first, second, Nat.cast_add, Nat.cast_one] <;> ring
  · rfl
  · rfl
  · simp [expected, successor, Nat.cast_add]; ring
  · change current.round + 1 + count = current.round + (count + 1)
    omega

theorem allFundedCycles (current : Current) (count : Nat) (reserve : Reserve current count) :
    run current count = expected current count ∧
      ∀ step, step < count → ∀ item ∈ law.rawItems (run current step) word,
        law.Valid item.before item.request := by
  induction count generalizing current with
  | zero => exact ⟨(expectedZero current).symm, by intro step bound; omega⟩
  | succ count ih =>
    have input := currentInputs current count reserve
    have next := actualNext current input
    have tail := ih (law.next current word) (nextReserve current count reserve)
    refine ⟨?_, ?_⟩
    · exact (show run current (count + 1) = run (law.next current word) count from rfl).trans
        (tail.1.trans ((congrArg (fun state => expected state count) next).trans (expectedSucc current count)))
    · intro step bound
      cases step with
      | zero => exact actualItems current input
      | succ step => exact tail.2 step (by omega)

theorem sourceCapacity (current : Current) (inputs : Inputs current) :
    0 < capacity current ∧ Reserve current (capacity current) := by
  have pe : 0 ≤ current.stock 1 .energy := by linarith [inputs.producerEnergy]
  have pl : 0 ≤ current.stock 1 .labor := by linarith [inputs.producerLabor]
  have we : 0 ≤ current.stock 2 .energy := by linarith [inputs.workerEnergy]
  have wl : 0 ≤ current.stock 2 .labor := by linarith [inputs.workerLabor]
  have left : capacity current ≤ min ⌊current.stock 1 .energy⌋₊ ⌊current.stock 1 .labor⌋₊ := min_le_left _ _
  have right : capacity current ≤ min ⌊current.stock 2 .energy⌋₊ ⌊current.stock 2 .labor⌋₊ := min_le_right _ _
  constructor
  · change 1 ≤ capacity current
    exact le_min (le_min ((Nat.one_le_floor_iff _).mpr inputs.producerEnergy)
      ((Nat.one_le_floor_iff _).mpr inputs.producerLabor))
      (le_min ((Nat.one_le_floor_iff _).mpr inputs.workerEnergy) ((Nat.one_le_floor_iff _).mpr inputs.workerLabor))
  · exact ⟨inputs.producerFeed, inputs.workerFeed, inputs.workerWaste, inputs.willing, inputs.waste,
      (Nat.cast_le.mpr (left.trans (min_le_left _ _))).trans (Nat.floor_le pe),
      (Nat.cast_le.mpr (left.trans (min_le_right _ _))).trans (Nat.floor_le pl),
      (Nat.cast_le.mpr (right.trans (min_le_left _ _))).trans (Nat.floor_le we),
      (Nat.cast_le.mpr (right.trans (min_le_right _ _))).trans (Nat.floor_le wl)⟩

theorem fundedCountCannotExceedActualCapacity (current : Current) (count : Nat) (reserve : Reserve current count) :
    count ≤ capacity current :=
  le_min (le_min (Nat.le_floor reserve.producerEnergy) (Nat.le_floor reserve.producerLabor))
    (le_min (Nat.le_floor reserve.workerEnergy) (Nat.le_floor reserve.workerLabor))

theorem the_generated_run_exhausts_at_least_one_actual_input (current : Current) (inputs : Inputs current) :
    ¬ Inputs (run current (capacity current)) := by
  intro next
  have funded := (allFundedCycles current (capacity current) (sourceCapacity current inputs).2).1
  rw [funded] at next
  have extra : Reserve current (capacity current + 1) := by
    refine ⟨inputs.producerFeed,inputs.workerFeed,inputs.workerWaste,inputs.willing,inputs.waste,?_,?_,?_,?_⟩
    · have h := next.producerEnergy
      norm_num [expected, show (Good.energy : Good) ≠ .service from by decide] at h ⊢
      linarith
    · have h := next.producerLabor
      norm_num [expected, show (Good.labor : Good) ≠ .service from by decide] at h ⊢
      linarith
    · have h := next.workerEnergy
      norm_num [expected, show (2 : Party) ≠ 1 from by decide] at h ⊢
      linarith
    · have h := next.workerLabor
      norm_num [expected, show (2 : Party) ≠ 1 from by decide] at h ⊢
      linarith
  have impossible := fundedCountCannotExceedActualCapacity current _ extra
  omega

instance (current : Current) : Decidable (Inputs current) :=
  decidable_of_iff
    (0 ≤ current.stock 1 .feedstock ∧ 0 ≤ current.stock 2 .feedstock ∧ 0 ≤ current.stock 2 .waste ∧
      current.technology.1 = true ∧ 1 ≤ current.stock 1 .waste ∧ 1 ≤ current.stock 1 .energy ∧
      1 ≤ current.stock 1 .labor ∧ 1 ≤ current.stock 2 .energy ∧ 1 ≤ current.stock 2 .labor)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩,
      fun h => ⟨h.producerFeed,h.workerFeed,h.workerWaste,h.willing,h.waste,h.producerEnergy,h.producerLabor,h.workerEnergy,h.workerLabor⟩⟩

inductive Result (current : Current) where
  | generated (positive : 0 < capacity current)
      (exhausted : ¬ Inputs (run current (capacity current)))
      (actual : run current (capacity current) = expected current (capacity current))
      (paid : ∀ step, step < capacity current → ∀ item ∈ law.rawItems (run current step) word,
        law.Valid item.before item.request)
  | blocked (obstruction : ¬ Inputs current)

def produce (current : Current) : Result current :=
  if ready : Inputs current then
    let funded := sourceCapacity current ready
    let actual := allFundedCycles current (capacity current) funded.2
    .generated funded.1 (the_generated_run_exhausts_at_least_one_actual_input current ready) actual.1 actual.2
  else .blocked ready

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingBudget
