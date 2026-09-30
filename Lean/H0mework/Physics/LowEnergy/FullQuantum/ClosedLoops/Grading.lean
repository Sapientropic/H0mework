import H0mework.Physics.LowEnergy.FullQuantum.CAR

/-! Complete ordered loop words retain the original exterior-degree arrow. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops
open DiracExteriorMatterAction
noncomputable section

abbrev six : Mother := MixedSymbol.degreeSix

def Arrow (action : Mother) : Prop := six*action=action ∧ action*six=0

def Expansion (full diagonal : Mother) : Prop :=
  Commute six diagonal ∧ Arrow (full-diagonal)

namespace Arrow

theorem zero : Arrow (0 : Mother) := by simp [Arrow]

theorem add {A B : Mother} (a : Arrow A) (b : Arrow B) : Arrow (A+B) := by
  constructor
  · rw [mul_add,a.1,b.1]
  · rw [add_mul,a.2,b.2,add_zero]

theorem smul (c : ℂ) {A : Mother} (a : Arrow A) : Arrow (c • A) := by
  constructor
  · rw [mul_smul_comm,a.1]
  · rw [smul_mul_assoc,a.2,smul_zero]

theorem sub {A B : Mother} (a : Arrow A) (b : Arrow B) : Arrow (A-B) := by
  constructor
  · have distribute : six*(A-B)=six*A-six*B := by convert! mul_sub six A B using 1
    rw [distribute,a.1,b.1]
  · have distribute : (A-B)*six=A*six-B*six := by convert! sub_mul A B six using 1
    rw [distribute,a.2,b.2]
    convert! (sub_self (0 : Mother)) using 1

theorem compose_zero {A B : Mother} (a : Arrow A) (b : Arrow B) : A*B=0 := by
  calc
    _ = A*(six*B) := by rw [b.1]
    _ = (A*six)*B := (mul_assoc _ _ _).symm
    _ = 0 := by rw [a.2,zero_mul]

theorem diagonal_left {A B : Mother} (a : Commute six A) (b : Arrow B) : Arrow (A*B) := by
  constructor
  · rw [← mul_assoc,a.eq,mul_assoc,b.1]
  · rw [mul_assoc,b.2,mul_zero]

theorem diagonal_right {A B : Mother} (a : Arrow A) (b : Commute six B) : Arrow (A*B) := by
  constructor
  · rw [← mul_assoc,a.1]
  · rw [mul_assoc,← b.eq,← mul_assoc,a.2,zero_mul]

end Arrow

namespace Expansion

theorem refl (A : Mother) (diagonal : Commute six A) : Expansion A A := by
  refine ⟨diagonal,?_⟩
  convert! Arrow.zero using 1
  exact sub_self A

theorem one : Expansion (1 : Mother) 1 := refl 1 (Commute.one_right six)

theorem smul (c : ℂ) {A A₀ : Mother} (a : Expansion A A₀) : Expansion (c • A) (c • A₀) := by
  have difference : c • A-c • A₀=c • (A-A₀) := by convert! (smul_sub c A A₀).symm using 1
  exact ⟨a.1.smul_right c,by rw [difference]; exact a.2.smul c⟩

theorem sub {A A₀ B B₀ : Mother} (a : Expansion A A₀) (b : Expansion B B₀) :
    Expansion (A-B) (A₀-B₀) := by
  have difference : (A-B)-(A₀-B₀)=(A-A₀)-(B-B₀) := by
    have algebra {R : Type} [AddCommGroup R] (a a₀ b b₀ : R) :
        (a-b)-(a₀-b₀)=(a-a₀)-(b-b₀) := by abel
    convert! algebra A A₀ B B₀ using 1
  refine ⟨?_,?_⟩
  · change six*(A₀-B₀)=(A₀-B₀)*six
    have left : six*(A₀-B₀)=six*A₀-six*B₀ := by convert! mul_sub six A₀ B₀ using 1
    have right : (A₀-B₀)*six=A₀*six-B₀*six := by convert! sub_mul A₀ B₀ six using 1
    rw [left,right,a.1.eq,b.1.eq]
  · rw [difference]
    exact a.2.sub b.2

theorem mul {A A₀ B B₀ : Mother} (a : Expansion A A₀) (b : Expansion B B₀) :
    Expansion (A*B) (A₀*B₀) := by
  have killed : (A-A₀)*(B-B₀)=0 := a.2.compose_zero b.2
  have difference : A*B-A₀*B₀=A₀*(B-B₀)+(A-A₀)*B₀ := by
    calc
      _ = A₀*(B-B₀)+(A-A₀)*B₀+(A-A₀)*(B-B₀) := by
        have algebra {R : Type} [Ring R] (a a₀ b b₀ : R) :
            a*b-a₀*b₀=a₀*(b-b₀)+(a-a₀)*b₀+(a-a₀)*(b-b₀) := by noncomm_ring
        convert! algebra A A₀ B B₀ using 1
      _ = _ := by rw [killed,add_zero]
  exact ⟨a.1.mul_right b.1,by rw [difference]; exact (Arrow.diagonal_left a.1 b.2).add (Arrow.diagonal_right a.2 b.1)⟩

theorem arrow_left {A A₀ B : Mother} (a : Expansion A A₀) (b : Arrow B) : Arrow (A*B) := by
  have killed := a.2.compose_zero b
  have same : A*B=A₀*B := by
    have subtraction : (A-A₀)*B=A*B-A₀*B := by convert! sub_mul A A₀ B using 1
    rw [subtraction] at killed
    exact sub_eq_zero.mp killed
  rw [same]
  exact Arrow.diagonal_left a.1 b

theorem arrow_right {A B B₀ : Mother} (a : Arrow A) (b : Expansion B B₀) : Arrow (A*B) := by
  have killed := a.compose_zero b.2
  have same : A*B=A*B₀ := by
    have subtraction : A*(B-B₀)=A*B-A*B₀ := by convert! mul_sub A B B₀ using 1
    rw [subtraction] at killed
    exact sub_eq_zero.mp killed
  rw [same]
  exact Arrow.diagonal_right a b.1

theorem product (word : List (Mother × Mother))
    (generated : ∀ pair ∈ word, Expansion pair.1 pair.2) :
    Expansion (word.map Prod.fst).prod (word.map Prod.snd).prod := by
  induction word with
  | nil => simpa using one
  | cons pair rest induction =>
    simp only [List.map_cons,List.prod_cons]
    exact (generated pair (List.mem_cons_self)).mul
      (induction fun item member => generated item (List.mem_cons_of_mem pair member))

end Expansion

def loopTrace (action : Mother) : ℂ := Matrix.trace (Quantum.operatorMatrix action)

theorem loopTrace_mul_comm (A B : Mother) : loopTrace (A*B)=loopTrace (B*A) := by
  have product (X Y : Mother) : Quantum.operatorMatrix (X*Y)=
      Quantum.operatorMatrix X*Quantum.operatorMatrix Y := Quantum.matrix_composition X Y
  simp only [loopTrace,product]
  exact Matrix.trace_mul_comm _ _

theorem arrow_trace {A : Mother} (arrow : Arrow A) : loopTrace A=0 := by
  calc
    _ = loopTrace (six*A) := by rw [arrow.1]
    _ = loopTrace (A*six) := loopTrace_mul_comm _ _
    _ = 0 := by
      rw [arrow.2]
      change Matrix.trace (Quantum.operatorMatrix (0 : Mother))=0
      have zero : Quantum.operatorMatrix (0 : Mother)=0 := Quantum.operatorMatrix.map_zero
      rw [zero,Matrix.trace_zero]

theorem expansion_trace {A A₀ : Mother} (generated : Expansion A A₀) :
    loopTrace A=loopTrace A₀ := by
  have vanishes := arrow_trace generated.2
  have subtract : Quantum.operatorMatrix (A-A₀)=Quantum.operatorMatrix A-Quantum.operatorMatrix A₀ :=
    Quantum.operatorMatrix.map_sub A A₀
  rw [loopTrace,subtract,Matrix.trace_sub] at vanishes
  exact sub_eq_zero.mp vanishes

theorem ordered_loop (word : List (Mother × Mother))
    (generated : ∀ pair ∈ word, Expansion pair.1 pair.2) :
    loopTrace (word.map Prod.fst).prod=loopTrace (word.map Prod.snd).prod :=
  expansion_trace (Expansion.product word generated)

theorem ordered_loop_with_arrow (before after : List (Mother × Mother))
    (generatedBefore : ∀ pair ∈ before, Expansion pair.1 pair.2)
    (generatedAfter : ∀ pair ∈ after, Expansion pair.1 pair.2)
    (vertex : Mother) (generatedVertex : Arrow vertex) :
    loopTrace ((before.map Prod.fst).prod*vertex*(after.map Prod.fst).prod)=0 :=
  arrow_trace (Expansion.arrow_right
    ((Expansion.product before generatedBefore).arrow_left generatedVertex)
    (Expansion.product after generatedAfter))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops
