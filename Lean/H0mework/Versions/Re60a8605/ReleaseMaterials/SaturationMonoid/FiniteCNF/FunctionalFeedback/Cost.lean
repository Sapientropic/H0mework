import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalFeedback
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.SharedFunctional

/-! Source-record visits include cached occurrence scans, the fallback, candidate
filtering and complete returned payload copies. Address bits and counter arithmetic
retain their separate classical machine obligations. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalFeedback.Cost
open InterferenceProgram
open FunctionalSubstitution (Instruction)
open FunctionalSchedule (Entry storage)
open FunctionalSchedule.Cost (Counted inputSize instructionSize choiceSize storage_pos storage_length
  storage_sublist size_member storage_nil storage_cons inputSize_nil inputSize_cons)

def choose (pool : List Entry) : Counted (Option Entry) :=
  let preferred := FunctionalSchedule.Cost.pick pool
  let result := match preferred.value with | some item => some item | none => pool.head?
  ⟨result,preferred.visits+2*choiceSize result+4⟩

theorem choose_value (pool : List Entry) : (choose pool).value=FunctionalFeedback.choose pool := by
  simp only [choose,FunctionalFeedback.choose,FunctionalSchedule.Cost.pick_value]
  cases FunctionalSchedule.pick pool <;> rfl

theorem choose_storage (pool : List Entry) : choiceSize (choose pool).value ≤ storage pool+2 := by
  rw [choose_value]
  cases found : FunctionalFeedback.choose pool with
  | none => simp only [choiceSize]; omega
  | some item =>
      have first := size_member pool item (FunctionalFeedback.choose_member found)
      simp only [choiceSize]
      omega

def chooseBudget (size : Nat) : Nat := FunctionalSchedule.Cost.pickBudget size+2*size+8

theorem choose_visits (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (choose pool).visits ≤ chooseBudget size := by
  have first := FunctionalSchedule.Cost.pick_visits pool size bounded
  have returned := choose_storage pool
  change (FunctionalSchedule.Cost.pick pool).visits+2*choiceSize (choose pool).value+4 ≤ _
  unfold chooseBudget
  omega

def avoid (address : Nat) : List Entry → Counted (List Entry)
  | [] => ⟨[],1⟩
  | item::rest =>
      let tail := avoid address rest
      let found := AffineClauseProduct.Cost.member address item.dependencies
      ⟨if found.value then tail.value else item::tail.value,
        tail.visits+found.visits+2*(item.size+storage tail.value)+5⟩

theorem avoid_value (address : Nat) (pool : List Entry) :
    (avoid address pool).value=pool.filter (fun item => decide (address ∉ item.dependencies)) := by
  induction pool with
  | nil => rfl
  | cons item rest ih =>
      simp only [avoid,List.filter_cons,AffineClauseProduct.Cost.member_value,ih]
      split <;> simp_all

theorem avoid_storage (address : Nat) (pool : List Entry) :
    storage (avoid address pool).value ≤ storage pool := by
  rw [avoid_value]
  exact storage_sublist List.filter_sublist

theorem avoid_visits_aux (address : Nat) (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (avoid address pool).visits ≤ pool.length*(6*size+8)+1 := by
  induction pool with
  | nil => simp [avoid]
  | cons item rest ih =>
      have total : item.size+storage rest ≤ size := by simpa only [storage_cons] using bounded
      have tail := ih (by omega)
      have scanned := AffineClauseProduct.Cost.member_visits address item.dependencies
      have returned := avoid_storage address rest
      have terms : item.dependencies.length ≤ item.size := by unfold Entry.size; omega
      simp only [avoid,List.length_cons]
      nlinarith

theorem avoid_visits (address : Nat) (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (avoid address pool).visits ≤ FunctionalSchedule.Cost.eligibleBudget size := by
  have output := avoid_visits_aux address pool size bounded
  have count := storage_length pool
  unfold FunctionalSchedule.Cost.eligibleBudget
  nlinarith

def retain (address : Nat) (pool : List Entry) : Counted (List Entry) :=
  let removed := FunctionalSchedule.Cost.remove address pool
  let remaining := avoid address removed.value
  ⟨remaining.value,removed.visits+remaining.visits+
    2*(storage pool+storage removed.value+storage remaining.value)+5⟩

theorem retain_value (address : Nat) (pool : List Entry) :
    (retain address pool).value=FunctionalFeedback.retain address pool := by
  simp only [retain,avoid_value,FunctionalSchedule.Cost.remove_value,FunctionalFeedback.retain]

theorem retain_storage (address : Nat) (pool : List Entry) : storage (retain address pool).value ≤ storage pool := by
  rw [retain_value]
  exact storage_sublist (FunctionalFeedback.retain_sublist _ _)

def retainBudget (size : Nat) : Nat :=
  FunctionalSchedule.Cost.removeBudget size+FunctionalSchedule.Cost.eligibleBudget size+6*size+5

theorem retain_visits (address : Nat) (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (retain address pool).visits ≤ retainBudget size := by
  have removed := FunctionalSchedule.Cost.remove_visits address pool size bounded
  have firstSize := FunctionalSchedule.Cost.remove_storage address pool
  have remaining := avoid_visits address (FunctionalSchedule.Cost.remove address pool).value size (by omega)
  have returned := avoid_storage address (FunctionalSchedule.Cost.remove address pool).value
  simp only [retain,retainBudget]
  omega

def arrange : Nat → List Entry → Counted (List Entry)
  | 0,_ => ⟨[],1⟩
  | fuel+1,pool =>
      let selected := choose pool
      match selected.value with
      | none => ⟨[],selected.visits+3⟩
      | some item =>
          let kept := retain item.instruction.address pool
          let tail := arrange fuel kept.value
          ⟨item::tail.value,selected.visits+kept.visits+tail.visits+
            2*(item.size+storage kept.value+storage tail.value)+7⟩

theorem arrange_value (fuel : Nat) (pool : List Entry) :
    (arrange fuel pool).value=FunctionalFeedback.arrange fuel pool := by
  induction fuel generalizing pool with
  | zero => rfl
  | succ fuel ih =>
      simp only [arrange,FunctionalFeedback.arrange,choose_value]
      split <;> simp_all [retain_value]

theorem arrange_storage (fuel : Nat) (pool : List Entry) : storage (arrange fuel pool).value ≤ fuel*storage pool+1 := by
  induction fuel generalizing pool with
  | zero => simp [arrange]
  | succ fuel ih =>
      simp only [arrange]
      split
      · simp
      · rename_i item found
        have member := FunctionalFeedback.choose_member ((choose_value pool).symm.trans found)
        have first := size_member pool item member
        have rest := retain_storage item.instruction.address pool
        have tail := ih (retain item.instruction.address pool).value
        simp only [storage_cons]
        nlinarith

def stepBudget (rounds size : Nat) : Nat :=
  chooseBudget size+retainBudget size+2*(rounds+3)*(size+1)+12

theorem arrange_visits_aux (fuel rounds size : Nat) (pool : List Entry)
    (roundBound : fuel ≤ rounds) (bounded : storage pool ≤ size) :
    (arrange fuel pool).visits ≤ fuel*stepBudget rounds size+1 := by
  induction fuel generalizing pool with
  | zero => simp [arrange]
  | succ fuel ih =>
      have selected := choose_visits pool size bounded
      simp only [arrange]
      split
      · simp only
        have first : (choose pool).visits+3 ≤ stepBudget rounds size := by unfold stepBudget; omega
        have repeated := Nat.mul_le_mul_right (stepBudget rounds size) (show 1 ≤ fuel+1 by omega)
        simp only [Nat.one_mul] at repeated
        omega
      · rename_i item found
        have member := FunctionalFeedback.choose_member ((choose_value pool).symm.trans found)
        have first := size_member pool item member
        have kept := retain_storage item.instruction.address pool
        have removed := retain_visits item.instruction.address pool size bounded
        have tail := ih (retain item.instruction.address pool).value (by omega) (by omega)
        have returned := arrange_storage fuel (retain item.instruction.address pool).value
        have future : fuel*storage (retain item.instruction.address pool).value ≤ rounds*size :=
          Nat.mul_le_mul (by omega) (by omega)
        simp only
        unfold stepBudget at *
        nlinarith

theorem arrange_visits (fuel : Nat) (pool : List Entry) :
    (arrange fuel pool).visits ≤ fuel*stepBudget fuel (storage pool)+1 :=
  arrange_visits_aux fuel fuel (storage pool) pool (by omega) (by omega)

def generate (source : List Instruction) : Counted (List Instruction) :=
  let cached := FunctionalSchedule.Cost.entries source
  let active := FunctionalSchedule.Cost.eligible cached.value
  let arranged := arrange source.length active.value
  let output := FunctionalSchedule.Cost.instructions arranged.value
  ⟨output.value,cached.visits+active.visits+arranged.visits+output.visits+
    2*(inputSize source+storage cached.value+storage active.value+storage arranged.value+inputSize output.value)+
    2*source.length+20⟩

theorem generate_value (source : List Instruction) : (generate source).value=FunctionalFeedback.generate source := by
  simp only [generate,FunctionalSchedule.Cost.instructions_value,arrange_value,
    FunctionalSchedule.Cost.eligible_value,FunctionalSchedule.Cost.entries_value,
    FunctionalFeedback.generate,FunctionalSchedule.eligible]

theorem generate_storage (source : List Instruction) :
    inputSize (generate source).value ≤ 2*source.length*inputSize source+1 := by
  have cached := FunctionalSchedule.Cost.entries_storage source
  have active := FunctionalSchedule.Cost.eligible_storage (FunctionalSchedule.Cost.entries source).value
  have arranged := arrange_storage source.length
    (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value
  have output := FunctionalSchedule.Cost.instructions_storage
    (arrange source.length (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value).value
  simp only [generate]
  nlinarith

def generateBudget (count size : Nat) : Nat :=
  FunctionalSchedule.Cost.entriesBudget count size+FunctionalSchedule.Cost.eligibleBudget (2*size)+
    count*stepBudget count (2*size)+1+count*(4*(2*count*size+1)+10)+1+
    2*(5*size+2*(2*count*size+1))+2*count+20

theorem generateBudget_eq (count size : Nat) :
    generateBudget count size=82*count*size^2+12*count^2*size+24*size^2+
      192*count*size+2*count^2+133*count+38*size+36 := by
  unfold generateBudget stepBudget chooseBudget retainBudget
    FunctionalSchedule.Cost.entriesBudget FunctionalSchedule.Cost.entryBudget
    FunctionalSchedule.Cost.pickBudget FunctionalSchedule.Cost.removeBudget FunctionalSchedule.Cost.eligibleBudget
  ring

theorem generate_visits (source : List Instruction) :
    (generate source).visits ≤ generateBudget source.length (inputSize source) := by
  have cached := FunctionalSchedule.Cost.entries_visits source (inputSize source) (by omega)
  have cachedSize := FunctionalSchedule.Cost.entries_storage source
  have active := FunctionalSchedule.Cost.eligible_visits (FunctionalSchedule.Cost.entries source).value
    (2*inputSize source) cachedSize
  have activeSize := FunctionalSchedule.Cost.eligible_storage (FunctionalSchedule.Cost.entries source).value
  have arranged := arrange_visits_aux source.length source.length (2*inputSize source)
    (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value (by omega) (by omega)
  have arrangedSize := arrange_storage source.length
    (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value
  have outputSize := FunctionalSchedule.Cost.instructions_storage
    (arrange source.length (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value).value
  have total : storage (arrange source.length
      (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value).value ≤
      2*source.length*inputSize source+1 := by nlinarith
  have output := FunctionalSchedule.Cost.instructions_visits
    (arrange source.length (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value).value
    (2*source.length*inputSize source+1) total
  have count : (arrange source.length
      (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value).value.length ≤ source.length := by
    rw [arrange_value]
    exact FunctionalFeedback.arrange_length _ _
  have outputBound : (FunctionalSchedule.Cost.instructions
      (arrange source.length (FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value).value).visits ≤
      source.length*(4*(2*source.length*inputSize source+1)+10)+1 := by nlinarith
  simp only [generate,generateBudget]
  omega

theorem bodyTerms_le_inputSize (source : List Instruction) :
    (source.map (fun i => i.body.code.size)).sum ≤ inputSize source := by
  induction source with
  | nil => simp
  | cons item rest ih => simp only [inputSize_cons,List.map_cons,List.sum_cons,instructionSize]; omega

def prepare (source : List Instruction) (program : Program) : Counted Program :=
  let instructions := generate source
  let executed := SharedFunctional.execute instructions.value program
  ⟨executed.value,instructions.visits+executed.visits+
    2*(inputSize source+program.code.size+executed.value.code.size)+9⟩

theorem prepare_value (source : List Instruction) (program : Program) :
    (prepare source program).value=FunctionalFeedback.prepare source program := by
  simp only [prepare,SharedFunctional.execute_value,generate_value,FunctionalFeedback.prepare]

def prepareBudget (count size nodes : Nat) : Nat :=
  let output := nodes+2*count*size+1
  generateBudget count size+(count+1)*(40*output+13)+2*(size+nodes+output)+9

theorem prepare_visits (source : List Instruction) (program : Program) :
    (prepare source program).visits ≤ prepareBudget source.length (inputSize source) program.code.size := by
  have generated := generate_visits source
  have stored := generate_storage source
  have terms := bodyTerms_le_inputSize (generate source).value
  have count : (generate source).value.length ≤ source.length := by
    rw [generate_value]
    exact FunctionalFeedback.generate_length source
  have executed := SharedFunctional.execute_cells (generate source).value program
  have output := SharedFunctional.execute_size (generate source).value program
  have outputBound : (SharedFunctional.execute (generate source).value program).value.code.size ≤
      program.code.size+2*source.length*inputSize source+1 := by omega
  rw [← SharedFunctional.execute_size] at executed
  have steps : (SharedFunctional.execute (generate source).value program).visits ≤
      (source.length+1)*(40*(program.code.size+2*source.length*inputSize source+1)+13) :=
    executed.trans (by gcongr)
  simp only [prepare,prepareBudget]
  omega

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalFeedback.Cost
