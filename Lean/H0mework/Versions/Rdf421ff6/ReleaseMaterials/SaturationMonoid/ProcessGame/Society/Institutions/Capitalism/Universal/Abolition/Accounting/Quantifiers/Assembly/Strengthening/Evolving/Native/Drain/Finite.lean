import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.NativeCurrent.FiniteDrain

universe u
variable {State : Type u} (next : State → State)

def path (state : State) : Nat → State
  | 0 => state
  | tick + 1 => next (path state tick)

private theorem shift (state : State) (tick : Nat) :
    path next (next state) tick = path next state (tick + 1) := by
  induction tick with
  | zero => rfl
  | succ tick ih => exact congrArg next ih

variable (rank : State → Nat) (work : State → Prop) [DecidablePred work]
  (step : ∀ state, work state → rank (next state) + 1 = rank state)
  (zero : ∀ state, rank state = 0 → ¬ work state)

include step zero in
private theorem stopExists : (fuel : Nat) → (state : State) → rank state ≤ fuel →
    ∃ tick : Nat, tick ≤ rank state ∧ ¬ work (path next state tick)
  | 0, state, within => ⟨0,Nat.zero_le _,zero state (Nat.eq_zero_of_le_zero within)⟩
  | fuel + 1, state, within => by
      by_cases active : work state
      · have spent := step state active
        obtain ⟨tick,bound,done⟩ := stopExists fuel (next state) (by omega)
        exact ⟨tick+1,by omega,by rw [← shift next state tick]; exact done⟩
      · exact ⟨0,Nat.zero_le _,active⟩

/-- Only the original rank supplies the finite observation budget. -/
def generated (state : State) :
    {tick : Nat // tick ≤ rank state ∧ ¬ work (path next state tick)} :=
  let found := stopExists next rank work step zero (rank state) state le_rfl
  ⟨Nat.find found,Nat.find_spec found⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.NativeCurrent.FiniteDrain
