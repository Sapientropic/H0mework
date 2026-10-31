import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Cycle
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Reserve

/-! A source may retain a real material surplus each period. Nonnegative
carry is computed from the finite paid execution; it is neither replenished
from outside nor removed to force a closed-state cycle. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (timing : input.law.TimeIndependent) (policy : input.law.ReserveInsensitive)
  (origin : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (gain : Party → Good → ℚ) (nonnegative : ∀ person good, 0 ≤ gain person good)

def accumulatedReserve (gain : Party → Good → ℚ) : Nat → Party → Good → ℚ
  | 0 => fun _ _ => 0
  | n + 1 => fun person good => gain person good + accumulatedReserve gain n person good

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem accumulatedReserve_exact (n : Nat) (person : Party) (good : Good) :
    accumulatedReserve gain n person good = (n : ℚ) * gain person good := by
  induction n with
  | zero => simp [accumulatedReserve]
  | succ n ih =>
      simp only [accumulatedReserve, ih, Nat.cast_add, Nat.cast_one]
      ring

include nonnegative in
omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem accumulatedReserve_nonnegative (n : Nat) (person : Party) (good : Good) :
    0 ≤ accumulatedReserve gain n person good := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact add_nonneg (nonnegative person good) ih

include timing policy in
omit [DecidableEq Port] in
theorem next_of_productive_period
    (productive : (input.law.execute origin 0 word).final = origin.addReserve gain)
    (accepted : ∀ item ∈ input.law.rawItems origin word, input.law.Valid item.before item.request)
    (reserve : Party → Good → ℚ) (funded : ∀ person good, 0 ≤ reserve person good)
    (clock : ℚ) (round : Nat) :
    input.law.next ((origin.addReserve reserve).retime clock round) word =
      (origin.addReserve (fun person good => gain person good + reserve person good)).retime
        (clock + max 0 (input.law.duration ((origin.addReserve reserve).retime clock round))) (round + 1) := by
  unfold RawLaw.next
  rw [input.law.execute_retime timing,
    (input.law.execute_addReserve policy origin reserve funded 0 word accepted).1, productive]
  apply RawCurrent.ext
  · funext person good
    simp only [RawCurrent.addReserve, RawCurrent.retime]
    exact add_assoc _ _ _
  · rfl
  · rfl
  · rfl
  · rfl

include timing policy nonnegative in
omit [DecidableEq Port] in
theorem generated_current_has_only_paid_accumulation
    (productive : (input.law.execute origin 0 word).final = origin.addReserve gain)
    (accepted : ∀ item ∈ input.law.rawItems origin word, input.law.Valid item.before item.request)
    (n : Nat) :
    ∃ clock round, (repeatPeriod input origin word).currentAt n =
      (origin.addReserve (accumulatedReserve gain n)).retime clock round := by
  induction n with
  | zero =>
      refine ⟨origin.clock, origin.round, ?_⟩
      change origin = _
      cases origin
      simp [RawCurrent.addReserve, RawCurrent.retime, accumulatedReserve]
  | succ n ih =>
      obtain ⟨clock, round, same⟩ := ih
      refine ⟨clock + max 0 (input.law.duration
        ((origin.addReserve (accumulatedReserve gain n)).retime clock round)), round + 1, ?_⟩
      change input.law.next ((repeatPeriod input origin word).currentAt n) word = _
      rw [same]
      exact next_of_productive_period input timing policy origin word gain productive accepted
        (accumulatedReserve gain n) (accumulatedReserve_nonnegative gain nonnegative n) clock round

include timing policy nonnegative in
/-- One finite paid programme, one actual nonnegative surplus and two local
law invariances generate all later paid periods. No future test is an input. -/
theorem productive_shared_period_generates_every_paid_period
    (members : List Party)
    (productive : (input.law.execute origin 0 word).final = origin.addReserve gain)
    (paid : SharedPeriod input origin members word) (n : Nat) :
    PeriodChecks input ((repeatPeriod input origin word).currentAt n) members word := by
  have accepted := fun item present => (paid.1 item present).1
  obtain ⟨clock, round, same⟩ := generated_current_has_only_paid_accumulation
    input timing policy origin word gain nonnegative productive accepted n
  rw [same]
  apply sharedPeriod_checks input _ members word
  · apply (sharedPeriod_retime input timing _ clock round members word).mpr
    exact sharedPeriod_addReserve input policy origin (accumulatedReserve gain n)
      (accumulatedReserve_nonnegative gain nonnegative n) members word paid
  · rw [next_of_productive_period input timing policy origin word gain productive accepted
      (accumulatedReserve gain n) (accumulatedReserve_nonnegative gain nonnegative n)]
    rfl

include timing policy nonnegative in
omit [DecidableEq Port] in
theorem productive_period_exact_resources
    (productive : (input.law.execute origin 0 word).final = origin.addReserve gain)
    (accepted : ∀ item ∈ input.law.rawItems origin word, input.law.Valid item.before item.request)
    (n : Nat) :
    (∀ person good, ((repeatPeriod input origin word).currentAt n).stock person good =
      origin.stock person good + (n : ℚ) * gain person good) ∧
    ((repeatPeriod input origin word).currentAt n).claims = origin.claims ∧
    ((repeatPeriod input origin word).currentAt n).technology = origin.technology := by
  obtain ⟨clock, round, same⟩ := generated_current_has_only_paid_accumulation
    input timing policy origin word gain nonnegative productive accepted n
  simp [same, RawCurrent.retime, RawCurrent.addReserve, accumulatedReserve_exact]

include timing policy nonnegative in
omit [DecidableEq Port] in
theorem productive_period_keeps_original_need_floor
    (needOrigin : RawCurrent Party Good Technology Instrument) (members : List Party)
    (productive : (input.law.execute origin 0 word).final = origin.addReserve gain)
    (accepted : ∀ item ∈ input.law.rawItems origin word, input.law.Valid item.before item.request)
    (floor : OriginalNeedFloor input needOrigin origin members word) (n : Nat) :
    OriginalNeedFloor input needOrigin ((repeatPeriod input origin word).currentAt n) members word := by
  obtain ⟨clock, round, same⟩ := generated_current_has_only_paid_accumulation
    input timing policy origin word gain nonnegative productive accepted n
  rw [same]
  apply (originalNeedFloor_retime input timing needOrigin _ clock round members word).mpr
  exact originalNeedFloor_addReserve input policy needOrigin origin (accumulatedReserve gain n)
    (accumulatedReserve_nonnegative gain nonnegative n) members word accepted floor

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.productive_shared_period_generates_every_paid_period
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.productive_period_exact_resources
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.productive_period_keeps_original_need_floor
