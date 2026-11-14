import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalSchedule

/-! Actual occurrence extraction and dependency scheduling with source-record
    scan and complete returned-payload copy allowances. Input lists are shared
    while read-only. Address bits, node scalar bits and counter arithmetic have
    separate machine costs. No dependency deduplication occurs in this program. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalSchedule.Cost

open InterferenceProgram
open FunctionalSubstitution (Instruction)
open FunctionalSchedule (Entry storage)
abbrev Counted := AffineProduct.Cost.Counted

def instructionSize (instruction : Instruction) : Nat := instruction.body.code.size+8
def inputSize (instructions : List Instruction) : Nat := (instructions.map instructionSize).sum+1

@[simp] theorem inputSize_nil : inputSize []=1 := rfl
@[simp] theorem inputSize_cons (head : Instruction) (rest : List Instruction) :
    inputSize (head::rest)=instructionSize head+inputSize rest := by simp [inputSize]; omega
@[simp] theorem storage_nil : storage []=1 := rfl
@[simp] theorem storage_cons (head : Entry) (rest : List Entry) :
    storage (head::rest)=head.size+storage rest := by simp [storage]; omega

theorem storage_pos (pool : List Entry) : 1 ≤ storage pool := by unfold storage; omega
theorem inputSize_pos (instructions : List Instruction) : 1 ≤ inputSize instructions := by unfold inputSize; omega

theorem storage_length (pool : List Entry) : pool.length ≤ storage pool := by
  induction pool with
  | nil => simp
  | cons head rest ih => simp only [List.length_cons,storage_cons]; unfold Entry.size; omega

theorem size_member (pool : List Entry) (item : Entry) (member : item ∈ pool) : item.size ≤ storage pool := by
  induction pool with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [storage_cons]; omega
      · have := ih member; simp only [storage_cons]; omega

theorem storage_sublist {left right : List Entry} (part : left.Sublist right) : storage left ≤ storage right := by
  unfold storage
  exact Nat.add_le_add_right ((part.map Entry.size).sum_le_sum (fun value _ => Nat.zero_le value)) 1

def occurrences : List Node → Counted (List Nat)
  | [] => ⟨[],1⟩
  | node::rest =>
      let tail := occurrences rest
      let found := FunctionalSubstitution.inputOf node
      ⟨match found with | none => tail.value | some i => i::tail.value,
        tail.visits+2*tail.value.length+10⟩

theorem occurrences_value (code : List Node) :
    (occurrences code).value=code.filterMap FunctionalSubstitution.inputOf := by
  induction code with
  | nil => rfl
  | cons node rest ih => simp only [occurrences,List.filterMap_cons,ih]; split <;> simp_all

theorem occurrences_length (code : List Node) : (occurrences code).value.length ≤ code.length := by
  rw [occurrences_value]
  exact List.length_filterMap_le _ _

theorem occurrences_visits (code : List Node) :
    (occurrences code).visits ≤ code.length*(2*code.length+10)+1 := by
  induction code with
  | nil => simp [occurrences]
  | cons node rest ih =>
      have shorter := occurrences_length rest
      simp only [occurrences,List.length_cons]
      nlinarith

def entry (instruction : Instruction) : Counted Entry :=
  let found := occurrences instruction.body.code.toList
  ⟨⟨instruction,found.value⟩,
    found.visits+4*instruction.body.code.size+2*found.value.length+20⟩

theorem entry_value (instruction : Instruction) : (entry instruction).value=FunctionalSchedule.entry instruction := by
  simp only [entry,FunctionalSchedule.entry,occurrences_value]

theorem entry_size (instruction : Instruction) : (entry instruction).value.size ≤ 2*instructionSize instruction := by
  have count := occurrences_length instruction.body.code.toList
  simp only [Array.length_toList] at count
  simp only [entry,Entry.size,instructionSize]
  omega

def entryBudget (size : Nat) : Nat := (size+1)*(2*size+40)

theorem entry_visits (instruction : Instruction) (size : Nat) (bounded : instructionSize instruction ≤ size) :
    (entry instruction).visits ≤ entryBudget size := by
  have count := occurrences_length instruction.body.code.toList
  have scanned := occurrences_visits instruction.body.code.toList
  simp only [Array.length_toList] at count scanned
  have body : instruction.body.code.size ≤ size := by unfold instructionSize at bounded; omega
  have square : instruction.body.code.size*instruction.body.code.size ≤ size*size := Nat.mul_self_le_mul_self body
  simp only [entry,entryBudget]
  nlinarith

def entries : List Instruction → Counted (List Entry)
  | [] => ⟨[],1⟩
  | instruction::rest =>
      let first := entry instruction
      let tail := entries rest
      ⟨first.value::tail.value,
        first.visits+tail.visits+2*(first.value.size+storage tail.value)+6⟩

theorem entries_value (instructions : List Instruction) :
    (entries instructions).value=instructions.map FunctionalSchedule.entry := by
  induction instructions <;> simp_all [entries,entry_value]

theorem entries_storage (instructions : List Instruction) : storage (entries instructions).value ≤ 2*inputSize instructions := by
  induction instructions with
  | nil => simp [entries]
  | cons instruction rest ih =>
      have first := entry_size instruction
      simp only [entries,storage_cons,inputSize_cons]
      omega

def entriesBudget (count size : Nat) : Nat := count*(entryBudget size+8*size+10)+1

theorem entries_visits (instructions : List Instruction) (size : Nat) (bounded : inputSize instructions ≤ size) :
    (entries instructions).visits ≤ entriesBudget instructions.length size := by
  induction instructions with
  | nil => simp [entries,entriesBudget]
  | cons instruction rest ih =>
      have total : instructionSize instruction+inputSize rest ≤ size := by simpa only [inputSize_cons] using bounded
      have first := entry_visits instruction size (by omega)
      have firstSize := entry_size instruction
      have tail := ih (by omega)
      have tailSize := entries_storage rest
      simp only [entries,List.length_cons,entriesBudget] at *
      nlinarith

def eligible : List Entry → Counted (List Entry)
  | [] => ⟨[],1⟩
  | item::rest =>
      let tail := eligible rest
      let self := AffineClauseProduct.Cost.member item.instruction.address item.dependencies
      ⟨if self.value then tail.value else item::tail.value,
        tail.visits+self.visits+2*(item.size+storage tail.value)+5⟩

theorem eligible_value (pool : List Entry) :
    (eligible pool).value=pool.filter (fun item => decide (item.instruction.address ∉ item.dependencies)) := by
  induction pool with
  | nil => rfl
  | cons item rest ih =>
      simp only [eligible,List.filter_cons,AffineClauseProduct.Cost.member_value,ih]
      split <;> simp_all

theorem eligible_storage (pool : List Entry) : storage (eligible pool).value ≤ storage pool := by
  rw [eligible_value]
  exact storage_sublist List.filter_sublist

def eligibleBudget (size : Nat) : Nat := (size+1)*(6*size+8)+1

theorem eligible_visits_aux (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (eligible pool).visits ≤ pool.length*(6*size+8)+1 := by
  induction pool with
  | nil => simp [eligible]
  | cons item rest ih =>
      have total : item.size+storage rest ≤ size := by simpa only [storage_cons] using bounded
      have tail := ih (by omega)
      have self := AffineClauseProduct.Cost.member_visits item.instruction.address item.dependencies
      have returned := eligible_storage rest
      have terms : item.dependencies.length ≤ item.size := by unfold Entry.size; omega
      simp only [eligible,List.length_cons]
      nlinarith

theorem eligible_visits (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (eligible pool).visits ≤ eligibleBudget size := by
  have output := eligible_visits_aux pool size bounded
  have count := storage_length pool
  unfold eligibleBudget
  nlinarith

def compatible (address : Nat) (item : Entry) : Counted Bool :=
  if item.instruction.address == address then ⟨true,4⟩ else
    let found := AffineClauseProduct.Cost.member address item.dependencies
    ⟨!found.value,found.visits+4⟩

theorem compatible_value (address : Nat) (item : Entry) :
    (compatible address item).value=
      (item.instruction.address == address || decide (address ∉ item.dependencies)) := by
  simp only [compatible,AffineClauseProduct.Cost.member_value]
  split <;> simp_all

theorem compatible_visits (address : Nat) (item : Entry) :
    (compatible address item).visits ≤ 2*item.dependencies.length+5 := by
  have found := AffineClauseProduct.Cost.member_visits address item.dependencies
  simp only [compatible]
  split <;> simp only <;> omega

def all (address : Nat) : List Entry → Counted Bool
  | [] => ⟨true,1⟩
  | item::rest =>
      let first := compatible address item
      if first.value then
        let tail := all address rest
        ⟨tail.value,first.visits+tail.visits+3⟩
      else ⟨false,first.visits+3⟩

theorem all_value (address : Nat) (pool : List Entry) :
    (all address pool).value=pool.all (fun item =>
      item.instruction.address == address || decide (address ∉ item.dependencies)) := by
  induction pool with
  | nil => rfl
  | cons item rest ih => simp only [all,List.all_cons,compatible_value]; split <;> simp_all

theorem all_visits (address : Nat) (pool : List Entry) : (all address pool).visits ≤ 4*storage pool := by
  induction pool with
  | nil => simp [all]
  | cons item rest ih =>
      have first := compatible_visits address item
      simp only [all,storage_cons]
      split <;> simp only <;> unfold Entry.size <;> omega

def admissible (pool : List Entry) (item : Entry) : Counted Bool :=
  let self := AffineClauseProduct.Cost.member item.instruction.address item.dependencies
  if self.value then ⟨false,self.visits+3⟩ else
    let others := all item.instruction.address pool
    ⟨others.value,self.visits+others.visits+3⟩

theorem admissible_value (pool : List Entry) (item : Entry) :
    (admissible pool item).value=FunctionalSchedule.admissible pool item := by
  simp only [admissible,FunctionalSchedule.admissible,AffineClauseProduct.Cost.member_value,all_value]
  split <;> simp_all

theorem admissible_visits (pool : List Entry) (item : Entry) :
    (admissible pool item).visits ≤ 4*storage pool+2*item.size+4 := by
  have self := AffineClauseProduct.Cost.member_visits item.instruction.address item.dependencies
  have others := all_visits item.instruction.address pool
  simp only [admissible]
  split <;> simp only <;> unfold Entry.size <;> omega

def choiceSize : Option Entry → Nat
  | none => 1
  | some item => item.size+2

def scan (pool : List Entry) : List Entry → Counted (Option Entry)
  | [] => ⟨none,1⟩
  | item::rest =>
      let ready := admissible pool item
      if ready.value then ⟨some item,ready.visits+2*item.size+5⟩ else
        let tail := scan pool rest
        ⟨tail.value,ready.visits+tail.visits+2*choiceSize tail.value+5⟩

theorem scan_value (pool candidates : List Entry) :
    (scan pool candidates).value=candidates.find? (FunctionalSchedule.admissible pool) := by
  induction candidates with
  | nil => rfl
  | cons item rest ih => simp only [scan,List.find?_cons,admissible_value]; split <;> simp_all

theorem scan_storage (pool candidates : List Entry) :
    choiceSize (scan pool candidates).value ≤ storage candidates+2 := by
  rw [scan_value]
  cases found : candidates.find? (FunctionalSchedule.admissible pool) with
  | none => have := storage_pos candidates; simp only [choiceSize]; omega
  | some item =>
    have member := List.mem_of_find?_eq_some found
    have := size_member candidates item member
    simp only [choiceSize]; omega

theorem scan_visits (pool candidates : List Entry) (size : Nat)
    (poolBound : storage pool ≤ size) (candidateBound : storage candidates ≤ size) :
    (scan pool candidates).visits ≤ candidates.length*(10*size+20)+1 := by
  induction candidates with
  | nil => simp [scan]
  | cons item rest ih =>
      have sizeBound : item.size+storage rest ≤ size := by simpa only [storage_cons] using candidateBound
      have ready := admissible_visits pool item
      have tail := ih (by omega)
      have returned := scan_storage pool rest
      simp only [scan,List.length_cons]
      split <;> simp only <;> nlinarith

def pick (pool : List Entry) : Counted (Option Entry) := scan pool pool
theorem pick_value (pool : List Entry) : (pick pool).value=FunctionalSchedule.pick pool := scan_value _ _
def pickBudget (size : Nat) : Nat := (size+1)*(10*size+20)+1

theorem pick_visits (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (pick pool).visits ≤ pickBudget size := by
  have scanned := scan_visits pool pool size bounded bounded
  have count := storage_length pool
  unfold pick pickBudget
  nlinarith

def remove (address : Nat) : List Entry → Counted (List Entry)
  | [] => ⟨[],1⟩
  | item::rest =>
      let tail := remove address rest
      ⟨if item.instruction.address != address then item::tail.value else tail.value,
        tail.visits+2*(item.size+storage tail.value)+5⟩

theorem remove_value (address : Nat) (pool : List Entry) :
    (remove address pool).value=FunctionalSchedule.remove address pool := by
  induction pool with
  | nil => rfl
  | cons item rest ih => simp only [remove,FunctionalSchedule.remove,List.filter_cons,ih]

theorem remove_storage (address : Nat) (pool : List Entry) :
    storage (remove address pool).value ≤ storage pool := by
  rw [remove_value]
  exact storage_sublist (FunctionalSchedule.remove_sublist _ _)

def removeBudget (size : Nat) : Nat := (size+1)*(4*size+5)+1

theorem remove_visits_aux (address : Nat) (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (remove address pool).visits ≤ pool.length*(4*size+5)+1 := by
  induction pool with
  | nil => simp [remove]
  | cons item rest ih =>
      have sizeBound : item.size+storage rest ≤ size := by simpa only [storage_cons] using bounded
      have tail := ih (by omega)
      have returned := remove_storage address rest
      simp only [remove,List.length_cons]
      nlinarith

theorem remove_visits (address : Nat) (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (remove address pool).visits ≤ removeBudget size := by
  have result := remove_visits_aux address pool size bounded
  have count := storage_length pool
  unfold removeBudget
  nlinarith

def schedule : Nat → List Entry → Counted (List Entry)
  | 0,_ => ⟨[],1⟩
  | fuel+1,pool =>
      let selected := pick pool
      match selected.value with
      | none => ⟨[],selected.visits+3⟩
      | some item =>
          let retained := remove item.instruction.address pool
          let tail := schedule fuel retained.value
          ⟨item::tail.value,selected.visits+retained.visits+tail.visits+
            2*(item.size+storage retained.value+storage tail.value)+7⟩

theorem schedule_value (fuel : Nat) (pool : List Entry) :
    (schedule fuel pool).value=FunctionalSchedule.schedule fuel pool := by
  induction fuel generalizing pool with
  | zero => rfl
  | succ fuel ih => simp only [schedule,FunctionalSchedule.schedule,pick_value]; split <;> simp_all [remove_value]

theorem schedule_storage (fuel : Nat) (pool : List Entry) :
    storage (schedule fuel pool).value ≤ fuel*storage pool+1 := by
  induction fuel generalizing pool with
  | zero => simp [schedule]
  | succ fuel ih =>
      simp only [schedule]
      split
      · simp
      · rename_i item found
        have member := FunctionalSchedule.pick_member ((pick_value pool).symm.trans found)
        have first := size_member pool item member
        have rest := remove_storage item.instruction.address pool
        have tail := ih (remove item.instruction.address pool).value
        simp only [storage_cons]
        nlinarith

def stepBudget (rounds size : Nat) : Nat :=
  pickBudget size+removeBudget size+2*(rounds+3)*(size+1)+12

theorem schedule_visits_aux (fuel rounds size : Nat) (pool : List Entry)
    (roundBound : fuel ≤ rounds) (bounded : storage pool ≤ size) :
    (schedule fuel pool).visits ≤ fuel*stepBudget rounds size+1 := by
  induction fuel generalizing pool with
  | zero => simp [schedule]
  | succ fuel ih =>
      have selected := pick_visits pool size bounded
      simp only [schedule]
      split
      · simp only
        have first : (pick pool).visits+3 ≤ stepBudget rounds size := by unfold stepBudget; omega
        have repeated := Nat.mul_le_mul_right (stepBudget rounds size) (show 1 ≤ fuel+1 by omega)
        simp only [Nat.one_mul] at repeated
        omega
      · rename_i item found
        have member := FunctionalSchedule.pick_member ((pick_value pool).symm.trans found)
        have first := size_member pool item member
        have retained := remove_storage item.instruction.address pool
        have removed := remove_visits item.instruction.address pool size bounded
        have tail := ih (remove item.instruction.address pool).value (by omega) (by omega)
        have returned := schedule_storage fuel (remove item.instruction.address pool).value
        have future : fuel*storage (remove item.instruction.address pool).value ≤ rounds*size := Nat.mul_le_mul (by omega) (by omega)
        simp only
        unfold stepBudget at *
        nlinarith

theorem schedule_visits (fuel : Nat) (pool : List Entry) :
    (schedule fuel pool).visits ≤ fuel*stepBudget fuel (storage pool)+1 :=
  schedule_visits_aux fuel fuel (storage pool) pool (by omega) (by omega)

def instructions : List Entry → Counted (List Instruction)
  | [] => ⟨[],1⟩
  | item::rest =>
      let tail := instructions rest
      ⟨item.instruction::tail.value,
        tail.visits+2*(instructionSize item.instruction+inputSize tail.value)+5⟩

theorem instructions_value (pool : List Entry) : (instructions pool).value=pool.map Entry.instruction := by
  induction pool <;> simp_all [instructions]

theorem instructions_storage (pool : List Entry) : inputSize (instructions pool).value ≤ storage pool := by
  induction pool with
  | nil => simp [instructions]
  | cons item rest ih =>
      simp only [instructions,inputSize_cons,storage_cons]
      unfold instructionSize Entry.size
      omega

theorem instructions_visits (pool : List Entry) (size : Nat) (bounded : storage pool ≤ size) :
    (instructions pool).visits ≤ pool.length*(4*size+10)+1 := by
  induction pool with
  | nil => simp [instructions]
  | cons item rest ih =>
      have sizeBound : item.size+storage rest ≤ size := by simpa only [storage_cons] using bounded
      have tail := ih (by omega)
      have returned := instructions_storage rest
      have first : instructionSize item.instruction ≤ item.size := by unfold instructionSize Entry.size; omega
      simp only [instructions,List.length_cons]
      nlinarith

def generate (source : List Instruction) : Counted (List Instruction) :=
  let prepared := entries source
  let active := eligible prepared.value
  let arranged := schedule source.length active.value
  let output := instructions arranged.value
  ⟨output.value,prepared.visits+active.visits+arranged.visits+output.visits+
    2*(inputSize source+storage prepared.value+storage active.value+storage arranged.value+inputSize output.value)+
    2*source.length+20⟩

theorem generate_value (source : List Instruction) : (generate source).value=FunctionalSchedule.generate source := by
  simp only [generate,instructions_value,schedule_value,eligible_value,entries_value,
    FunctionalSchedule.generate,FunctionalSchedule.eligible]

def generateBudget (count size : Nat) : Nat :=
  entriesBudget count size+eligibleBudget (2*size)+count*stepBudget count (2*size)+1+
    count*(4*(2*count*size+1)+10)+1+
    2*(5*size+2*(2*count*size+1))+2*count+20

theorem generateBudget_eq (count size : Nat) :
    generateBudget count size=58*count*size^2+12*count^2*size+24*size^2+
      148*count*size+2*count^2+111*count+38*size+36 := by
  unfold generateBudget entriesBudget entryBudget eligibleBudget stepBudget pickBudget removeBudget
  ring

theorem generate_visits (source : List Instruction) :
    (generate source).visits ≤ generateBudget source.length (inputSize source) := by
  have prepared := entries_visits source (inputSize source) (by omega)
  have preparedSize := entries_storage source
  have active := eligible_visits (entries source).value (2*inputSize source) preparedSize
  have activeSize := eligible_storage (entries source).value
  have arranged := schedule_visits_aux source.length source.length (2*inputSize source)
    (eligible (entries source).value).value (by omega) (by omega)
  have arrangedSize := schedule_storage source.length (eligible (entries source).value).value
  have outputSize := instructions_storage (schedule source.length (eligible (entries source).value).value).value
  have total : storage (schedule source.length (eligible (entries source).value).value).value ≤
      2*source.length*inputSize source+1 := by nlinarith
  have output := instructions_visits (schedule source.length (eligible (entries source).value).value).value
    (2*source.length*inputSize source+1) total
  have count : (schedule source.length (eligible (entries source).value).value).value.length ≤ source.length := by
    rw [schedule_value]
    exact FunctionalSchedule.schedule_length _ _
  have outputBound : (instructions (schedule source.length (eligible (entries source).value).value).value).visits ≤
      source.length*(4*(2*source.length*inputSize source+1)+10)+1 := by nlinarith
  simp only [generate,generateBudget]
  omega

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalSchedule.Cost
