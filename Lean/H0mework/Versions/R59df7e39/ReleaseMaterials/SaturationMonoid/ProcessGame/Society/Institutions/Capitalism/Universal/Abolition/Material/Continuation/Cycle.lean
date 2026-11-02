import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Shared
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.FromSelfSupply

/-! A finite paid execution and local temporal covariance generate every
finite continuation. The programme is a reusable material producer, not an
assertion that a different word has already been selected by an existing root. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)
  (timing : input.law.TimeIndependent)
  (origin : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

def repeatPeriod : RawProgram Party Good Port Technology Instrument :=
  ⟨input.law, origin, fun _ => word⟩

include timing

omit [DecidableEq Port] in
theorem next_of_closed_period
    (closed : (input.law.execute origin 0 word).final = origin)
    (clock : ℚ) (round : Nat) :
    input.law.next (origin.retime clock round) word =
      origin.retime (clock + max 0 (input.law.duration (origin.retime clock round))) (round + 1) := by
  unfold RawLaw.next
  rw [input.law.execute_retime timing, closed]
  rfl

omit [DecidableEq Port] in
/-- The only induction uses the literal local interpreter. No future state,
successful execution or C-free tail is an input to this construction. -/
theorem generated_current_is_retime
    (closed : (input.law.execute origin 0 word).final = origin) (n : Nat) :
    ∃ clock round, (repeatPeriod input origin word).currentAt n = origin.retime clock round := by
  induction n with
  | zero =>
      refine ⟨origin.clock, origin.round, ?_⟩
      cases origin
      rfl
  | succ n ih =>
      obtain ⟨clock, round, same⟩ := ih
      refine ⟨clock + max 0 (input.law.duration (origin.retime clock round)), round + 1, ?_⟩
      change input.law.next ((repeatPeriod input origin word).currentAt n) word = _
      rw [same]
      exact next_of_closed_period input timing origin word closed clock round

omit [DecidableEq Port] in
theorem generated_resources_and_old_claims
    (closed : (input.law.execute origin 0 word).final = origin) (n : Nat) :
    ((repeatPeriod input origin word).currentAt n).stock = origin.stock ∧
    ((repeatPeriod input origin word).currentAt n).claims = origin.claims ∧
    ((repeatPeriod input origin word).currentAt n).technology = origin.technology := by
  obtain ⟨clock, round, same⟩ := generated_current_is_retime input timing origin word closed n
  simp only [same, RawCurrent.retime, and_self]

omit timing [DecidableEq Port] in
theorem generated_round_exact (n : Nat) :
    ((repeatPeriod input origin word).currentAt n).round = origin.round + n := by
  induction n with
  | zero => simp [repeatPeriod, RawProgram.currentAt]
  | succ n ih =>
      change ((repeatPeriod input origin word).currentAt n).round + 1 = _
      omega

omit timing [DecidableEq Port] in
theorem generated_clock_step (n : Nat) :
    ((repeatPeriod input origin word).currentAt (n + 1)).clock =
      ((repeatPeriod input origin word).currentAt n).clock +
        max 0 (input.law.duration ((repeatPeriod input origin word).currentAt n)) := rfl

theorem shared_cycle_generates_every_paid_period
    (members : List Party)
    (closed : (input.law.execute origin 0 word).final = origin)
    (paid : SharedPeriod input origin members word) (n : Nat) :
    PeriodChecks input ((repeatPeriod input origin word).currentAt n) members word := by
  obtain ⟨clock, round, same⟩ := generated_current_is_retime input timing origin word closed n
  rw [same]
  apply sharedPeriod_checks input _ members word
  · exact (sharedPeriod_retime input timing origin clock round members word).mpr paid
  · rw [next_of_closed_period input timing origin word closed]
    rfl

theorem autonomous_cycle_generates_every_paid_period
    (members : List Party)
    (closed : (input.law.execute origin 0 word).final = origin)
    (paid : Exit.AutonomousProduction.Checks input.law origin members word)
    (policy : PolicyExplained input) (n : Nat) :
    PeriodChecks input ((repeatPeriod input origin word).currentAt n) members word := by
  obtain ⟨clock, round, same⟩ := generated_current_is_retime input timing origin word closed n
  rw [same]
  exact periodChecks_of_actual_self_supply input _ members word
    ((Exit.AutonomousProduction.checks_retime input.law timing origin clock round members word).mpr paid)
    policy

omit [DecidableEq Port] in
/-- An original pre-fee floor is paid again by actual debits in every period.
The floor is never recomputed from diminished purchasing power. -/
theorem cycle_preserves_original_need_floor
    (needOrigin : RawCurrent Party Good Technology Instrument) (members : List Party)
    (closed : (input.law.execute origin 0 word).final = origin)
    (paid : OriginalNeedFloor input needOrigin origin members word) (n : Nat) :
    OriginalNeedFloor input needOrigin ((repeatPeriod input origin word).currentAt n) members word := by
  obtain ⟨clock, round, same⟩ := generated_current_is_retime input timing origin word closed n
  rw [same]
  exact (originalNeedFloor_retime input timing needOrigin origin clock round members word).mpr paid

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.shared_cycle_generates_every_paid_period
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.autonomous_cycle_generates_every_paid_period
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.cycle_preserves_original_need_floor
