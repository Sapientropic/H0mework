import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Fields

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution
noncomputable section
open scoped Matrix InnerProductSpace
variable {n m : Type*} [Fintype n] [DecidableEq n]

def advance (source : Matrix n m ℂ → Matrix n n ℂ) (time : ℝ)
    (current : Matrix n m ℂ) : Matrix n m ℂ :=
  occupiedUpdate (source current) (time/2) current

def history (source : Matrix n m ℂ → Matrix n n ℂ) (time : ℝ)
    (depth : Nat) (current : Matrix n m ℂ) : Matrix n m ℂ :=
  Nat.rec current (fun _ previous => advance source time previous) depth

theorem actual_next (source : Matrix n m ℂ → Matrix n n ℂ) (time : ℝ)
    (depth : Nat) (current : Matrix n m ℂ) :
    history source time (depth+1) current = advance source time (history source time depth current) := rfl

theorem no_reinitialization (source : Matrix n m ℂ → Matrix n n ℂ) (time : ℝ)
    (depth : Nat) (current : Matrix n m ℂ) :
    history source time (depth+1) current =
      occupiedUpdate (source (history source time depth current)) (time/2)
        (history source time depth current) := rfl

theorem continuous_occupation (source : Matrix n m ℂ → Matrix n n ℂ)
    (generated : ∀ current, (source current).IsHermitian) (time : ℝ)
    (depth : Nat) (current : Matrix n m ℂ) :
    (history source time depth current).conjTranspose * history source time depth current =
      current.conjTranspose * current := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
    rw [actual_next,advance,occupied_gram _ (generated _) (time/2)]
    exact previous

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem continuous_fields (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (source : Matrix n m ℂ → Matrix n n ℂ) (generated : ∀ current, (source current).IsHermitian)
    (time : ℝ) (depth : Nat) (current : Matrix n m ℂ) (first second : m) :
    inner ℂ (fields basis (history source time depth current) first)
      (fields basis (history source time depth current) second) =
      inner ℂ (fields basis current first) (fields basis current second) := by
  rw [field_gram basis orthogonal,field_gram basis orthogonal,continuous_occupation source generated]

theorem continuous_slater {electrons : Nat} (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (source : Matrix n (Fin electrons) ℂ → Matrix n n ℂ)
    (generated : ∀ current, (source current).IsHermitian) (time : ℝ) (depth : Nat)
    (current : Matrix n (Fin electrons) ℂ) (normalized : current.conjTranspose * current = 1) :
    slaterDual (fields basis (history source time depth current))
      (slater (fields basis (history source time depth current))) = 1 :=
  slater_normalized _ (occupied_fields basis orthogonal _
    ((continuous_occupation source generated time depth current).trans normalized))

end
end CPS1ElectronicEvolution
