import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Forgetting.Scalar

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.EffectReading
open InterferenceProgram

structure Sample where
  value : Nat
  leaves : Nat
  nodes : Nat
  deriving Repr

def observe (program : Program) (cap : Nat) (point : Nat → Bool) : Sample :=
  let executed := InterferenceDecision.runCounted point #[] program.code.toList
  let amplitude := executed.1.getD program.weight.val 0 * sign (executed.1.getD program.phase.val 0)
  ⟨if truth amplitude then cap else 1,1,executed.2⟩

theorem observe_value (program : Program) (cap : Nat) (point : Nat → Bool) :
    (observe program cap point).value=(if truth (program.eval point) then cap else 1) := by
  simp only [observe,InterferenceDecision.runCounted_eq,Program.eval,run]
  rfl

theorem observe_nodes (program : Program) (cap : Nat) (point : Nat → Bool) :
    (observe program cap point).nodes=program.code.size*(observe program cap point).leaves := by
  simp [observe,InterferenceDecision.runCounted_eq]

def collect (cap : Nat) : List Nat → ((Nat → Bool) → Sample) → (Nat → Bool) → Sample
  | [],value,point => let source := value point; ⟨min cap source.value,source.leaves,source.nodes⟩
  | i::rest,value,point =>
      let first := collect cap rest value (Function.update point i false)
      if first.value=cap then first else
        let second := collect cap rest value (Function.update point i true)
        ⟨min cap (first.value+second.value),first.leaves+second.leaves,first.nodes+second.nodes⟩

theorem collect_value (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Sample) (point : Nat → Bool) :
    (collect cap indices value point).value=ForgettingScalar.cappedSum cap indices (fun x => (value x).value) point := by
  induction indices generalizing point with
  | nil => rfl
  | cons i rest ih => simp only [collect,ih,ForgettingScalar.cappedSum,ForgettingScalar.capAdd]; split <;> simp_all

theorem collect_nodes (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Sample) (size : Nat)
    (cost : ∀ point, (value point).nodes=size*(value point).leaves) (point : Nat → Bool) :
    (collect cap indices value point).nodes=size*(collect cap indices value point).leaves := by
  induction indices generalizing point with
  | nil => exact cost point
  | cons i rest ih =>
      have left := ih (Function.update point i false)
      have right := ih (Function.update point i true)
      simp only [collect]
      split
      · exact left
      · simp only [Nat.mul_add,left,right]

theorem collect_leaves_pos (cap : Nat) (indices : List Nat) (value : (Nat → Bool) → Sample)
    (positive : ∀ point, 0 < (value point).leaves) (point : Nat → Bool) : 0 < (collect cap indices value point).leaves := by
  induction indices generalizing point with
  | nil => exact positive point
  | cons i rest ih =>
      have left := ih (Function.update point i false)
      simp only [collect]
      split
      · exact left
      · dsimp only; omega

theorem collect_same (cap : Nat) (indices : List Nat) (left right : (Nat → Bool) → Sample)
    (values : ∀ point, (left point).value=(right point).value)
    (leaves : ∀ point, (left point).leaves=(right point).leaves) (point : Nat → Bool) :
    (collect cap indices left point).value=(collect cap indices right point).value ∧
      (collect cap indices left point).leaves=(collect cap indices right point).leaves := by
  induction indices generalizing point with
  | nil => exact ⟨congrArg (min cap) (values point),leaves point⟩
  | cons i rest ih =>
      have first := ih (Function.update point i false)
      have second := ih (Function.update point i true)
      simp only [collect,first.1]
      split <;> simp_all

def sample (program : Program) : Sample := collect (ForgettingScalar.programCapacity program) (FunctionalSubstitution.inputs program.code)
  (observe program (ForgettingScalar.programCapacity program)) InterferenceDecision.zeroEnvironment

theorem sample_value (program : Program) : (sample program).value=ForgettingScalar.programSignal program := by
  simp only [sample,collect_value,observe_value,ForgettingScalar.programSignal]

theorem sample_nodes (program : Program) : (sample program).nodes=program.code.size*(sample program).leaves :=
  collect_nodes _ _ _ _ (observe_nodes _ _) _

theorem sample_leaves_pos (program : Program) : 0 < (sample program).leaves :=
  collect_leaves_pos _ _ _ (fun _ => Nat.zero_lt_one) _

theorem sample_same_leaves (left right : Program)
    (inputs : FunctionalSubstitution.inputs left.code=FunctionalSubstitution.inputs right.code)
    (values : ∀ point, truth (left.eval point)=truth (right.eval point)) : (sample left).leaves=(sample right).leaves := by
  have caps : ForgettingScalar.programCapacity left=ForgettingScalar.programCapacity right := by
    simp only [ForgettingScalar.programCapacity,inputs]
  simp only [sample,caps,inputs]
  exact (collect_same (ForgettingScalar.programCapacity right) (FunctionalSubstitution.inputs right.code)
    (observe left (ForgettingScalar.programCapacity right)) (observe right (ForgettingScalar.programCapacity right))
    (fun point => by rw [observe_value,observe_value,values point]) (fun _ => rfl) InterferenceDecision.zeroEnvironment).2

theorem sample_fewer_nodes (left right : Program)
    (inputs : FunctionalSubstitution.inputs left.code=FunctionalSubstitution.inputs right.code)
    (values : ∀ point, truth (left.eval point)=truth (right.eval point)) (size : right.code.size < left.code.size) :
    (sample right).nodes < (sample left).nodes := by
  rw [sample_nodes,sample_nodes,sample_same_leaves left right inputs values]
  exact Nat.mul_lt_mul_of_pos_right size (sample_leaves_pos right)

def read (program : Program) : Bool :=
  let source := sample program
  let bucket := 4*source.value/ForgettingScalar.programCapacity program
  ForgettingScalar.adcRead ⟨bucket,by
    have bound := ForgettingScalar.programBucket_bound program
    change 4*(sample program).value/ForgettingScalar.programCapacity program < 5
    rw [sample_value]
    exact Nat.lt_succ_of_le bound⟩

theorem read_value (program : Program) : read program=ForgettingScalar.programRead program := by
  simp only [read,sample_value,ForgettingScalar.programRead,ForgettingScalar.programBucket]

end SaturationMonoid.ComplexityProjection.SATSource.EffectReading
