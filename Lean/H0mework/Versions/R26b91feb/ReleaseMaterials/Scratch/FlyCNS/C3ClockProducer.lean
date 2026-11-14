import Lean
set_option autoImplicit false
namespace FlyCNS.C3Clock

/-- Source metadata counters retain Nat throughout generation. Only the
original successful Int64 save determines admission to a finite fibre. -/
structure State where
  visit : Nat
  neural : Nat
  physics : Nat
  gates : Nat
  deriving DecidableEq
def initial : State := ⟨0,0,0,0⟩
def next (s : State) : State :=
  if s.visit==55 || s.visit==58 then ⟨s.visit+1,s.neural,s.physics,s.gates+1⟩
  else ⟨s.visit+1,s.neural+100,s.physics+1000,s.gates⟩
def generate : Nat → State
  | 0 => initial
  | n+1 => next (generate n)

theorem generated_visit (n : Nat) : (generate n).visit=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [generate,next]
    split <;> simp_all
theorem generated_physics (n : Nat) : (generate n).physics=10*(generate n).neural := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [generate,next]
    split <;> simp_all <;> omega
theorem generated_debit (n : Nat) : (generate n).neural+100*(generate n).gates=100*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [generate,next]
    split <;> simp_all <;> omega

def gateCount (n : Nat) : Nat := (if 55<n then 1 else 0)+(if 58<n then 1 else 0)
theorem generated_gates (n : Nat) : (generate n).gates=gateCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [generate,next,generated_visit]
    by_cases first : n=55
    · subst n
      simp [gateCount] at ih ⊢
      omega
    by_cases second : n=58
    · subst n
      simp [gateCount] at ih ⊢
      omega
    have gate : (n==55 || n==58)=false := by simp [first,second]
    have p' : (55<n+1) ↔ (55<n) := by omega
    have q' : (58<n+1) ↔ (58<n) := by omega
    simpa [gate,gateCount,p',q'] using ih

def signedLimit : Nat := 2^63-1
def successfulSave (state : State) : Bool := state.physics ≤ signedLimit
theorem successful_visit_bound (n : Nat) (accepted : successfulSave (generate n)=true) :
    n ≤ signedLimit/1000+2 := by
  have physical := generated_physics n
  have debit := generated_debit n
  have gates := generated_gates n
  have atMost : (generate n).gates≤2 := by
    rw [gates]
    by_cases p : 55<n <;> by_cases q : 58<n <;> simp [gateCount,p,q]
  have bound : (generate n).physics ≤ signedLimit := by simpa [successfulSave] using accepted
  have conserved : 1000*n=(generate n).physics+1000*(generate n).gates := by omega
  omega

def successfulVisit (n : Nat) (accepted : successfulSave (generate n)=true) : Fin (signedLimit/1000+3) :=
  ⟨n,by have bound := successful_visit_bound n accepted;omega⟩

def closed (visit : Nat) : State :=
  ⟨visit,100*(visit-gateCount visit),1000*(visit-gateCount visit),gateCount visit⟩

theorem state_ext (left right : State) (v : left.visit=right.visit)
    (n : left.neural=right.neural) (p : left.physics=right.physics) (g : left.gates=right.gates) : left=right := by
  cases left;cases right;simp_all
theorem closed_eq_generate (visit : Nat) : closed visit=generate visit := by
  have v := generated_visit visit
  have n := generated_debit visit
  have p := generated_physics visit
  have g := generated_gates visit
  apply state_ext
  · exact v.symm
  · simp only [closed];omega
  · simp only [closed];omega
  · exact g.symm

end FlyCNS.C3Clock
