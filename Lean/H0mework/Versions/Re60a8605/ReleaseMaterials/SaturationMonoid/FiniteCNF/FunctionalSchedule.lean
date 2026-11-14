import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalAffine
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.ProductCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalSchedule

open InterferenceProgram
open FunctionalSubstitution (Instruction Free)

structure Entry where
  instruction : Instruction
  dependencies : List Nat
  deriving Repr

/-- Keep every source input occurrence; dependency membership needs no deduplication. -/
def entry (instruction : Instruction) : Entry :=
  ⟨instruction,instruction.body.code.toList.filterMap FunctionalSubstitution.inputOf⟩

def Entry.Correct (item : Entry) : Prop :=
  ∀ i, i ∈ item.dependencies ↔ i ∈ FunctionalSubstitution.inputs item.instruction.body.code

theorem entry_correct (instruction : Instruction) : (entry instruction).Correct := by
  intro i
  simp [entry,FunctionalSubstitution.inputs]

def Entry.size (item : Entry) : Nat :=
  item.instruction.body.code.size+item.dependencies.length+8

def storage (pool : List Entry) : Nat := (pool.map Entry.size).sum+1

def admissible (pool : List Entry) (item : Entry) : Bool :=
  decide (item.instruction.address ∉ item.dependencies) &&
    pool.all (fun other => other.instruction.address == item.instruction.address ||
      decide (item.instruction.address ∉ other.dependencies))

def pick (pool : List Entry) : Option Entry := pool.find? (admissible pool)

def remove (address : Nat) (pool : List Entry) : List Entry :=
  pool.filter (fun item => item.instruction.address != address)

def schedule : Nat → List Entry → List Entry
  | 0,_ => []
  | fuel+1,pool => match pick pool with
    | none => []
    | some item => item::schedule fuel (remove item.instruction.address pool)

def eligible (instructions : List Instruction) : List Entry :=
  (instructions.map entry).filter (fun item => decide (item.instruction.address ∉ item.dependencies))

theorem eligible_subset (instructions : List Instruction) : eligible instructions ⊆ instructions.map entry :=
  List.filter_sublist.subset

theorem eligible_length (instructions : List Instruction) : (eligible instructions).length ≤ instructions.length := by
  simpa only [eligible,List.length_map] using (List.filter_sublist (l := instructions.map entry)
    (p := fun item => decide (item.instruction.address ∉ item.dependencies))).length_le

def generate (instructions : List Instruction) : List Instruction :=
  (schedule instructions.length (eligible instructions)).map Entry.instruction

theorem pick_member {pool : List Entry} {item : Entry} (found : pick pool=some item) : item ∈ pool :=
  List.mem_of_find?_eq_some found

theorem pick_admissible {pool : List Entry} {item : Entry} (found : pick pool=some item) :
    admissible pool item=true := List.find?_some found

theorem remove_sublist (address : Nat) (pool : List Entry) : (remove address pool).Sublist pool :=
  List.filter_sublist

theorem remove_member (address : Nat) (pool : List Entry) (item : Entry) :
    item ∈ remove address pool ↔ item ∈ pool ∧ item.instruction.address ≠ address := by
  simp [remove]

theorem schedule_member (fuel : Nat) (pool : List Entry) (item : Entry)
    (member : item ∈ schedule fuel pool) : item ∈ pool := by
  induction fuel generalizing pool with
  | zero => simp [schedule] at member
  | succ fuel ih =>
      simp only [schedule] at member
      split at member
      · simp at member
      · rename_i head found
        rcases List.mem_cons.mp member with rfl | later
        · exact pick_member found
        · exact (remove_sublist _ _).subset (ih _ later)

theorem schedule_length (fuel : Nat) (pool : List Entry) : (schedule fuel pool).length ≤ fuel := by
  induction fuel generalizing pool with
  | zero => simp [schedule]
  | succ fuel ih =>
      simp only [schedule]
      split
      · simp
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _)

theorem generate_member (instructions : List Instruction) (instruction : Instruction)
    (member : instruction ∈ generate instructions) : instruction ∈ instructions := by
  change instruction ∈ (schedule instructions.length (eligible instructions)).map Entry.instruction at member
  obtain ⟨item,itemMem,same⟩ := List.mem_map.mp member
  subst instruction
  have poolMem := eligible_subset instructions (schedule_member _ _ _ itemMem)
  obtain ⟨source,sourceMem,same⟩ := List.mem_map.mp poolMem
  subst item
  exact sourceMem

theorem generate_length (instructions : List Instruction) : (generate instructions).length ≤ instructions.length := by
  simpa only [generate,List.length_map] using schedule_length instructions.length (eligible instructions)

theorem pick_free {pool : List Entry} {item : Entry} (correct : ∀ other ∈ pool, other.Correct)
    (found : pick pool=some item) : Free item.instruction.address item.instruction.body.code := by
  have accepted := pick_admissible found
  simp only [admissible,Bool.and_eq_true,decide_eq_true_eq] at accepted
  apply (FunctionalSubstitution.free_iff _ _).mpr
  intro present
  exact accepted.1 ((correct item (pick_member found) _).mpr present)

theorem pick_later {pool : List Entry} {item other : Entry}
    (correct : ∀ value ∈ pool, value.Correct) (found : pick pool=some item)
    (later : other ∈ remove item.instruction.address pool) :
    item.instruction.address ≠ other.instruction.address ∧
      Free item.instruction.address other.instruction.body.code := by
  obtain ⟨member,different⟩ := (remove_member _ _ _).mp later
  have accepted := pick_admissible found
  simp only [admissible,Bool.and_eq_true,decide_eq_true_eq] at accepted
  have relation := List.all_eq_true.mp accepted.2 other member
  have absent : item.instruction.address ∉ other.dependencies := by
    simpa only [beq_eq_false_iff_ne.mpr different,Bool.false_or,decide_eq_true_eq] using relation
  exact ⟨Ne.symm different,(FunctionalSubstitution.free_iff _ _).mpr
    (fun present => absent ((correct other member _).mpr present))⟩

theorem schedule_triangular (fuel : Nat) (pool : List Entry) (correct : ∀ item ∈ pool, item.Correct) :
    FunctionalSubstitution.Triangular ((schedule fuel pool).map Entry.instruction) := by
  induction fuel generalizing pool with
  | zero => simp [schedule,FunctionalSubstitution.Triangular]
  | succ fuel ih =>
      simp only [schedule]
      split
      · simp [FunctionalSubstitution.Triangular]
      · rename_i head found
        have tail := ih (remove head.instruction.address pool)
          (fun item member => correct item ((remove_sublist _ _).subset member))
        simp only [List.map_cons]
        refine ⟨?_,List.pairwise_cons.mpr ⟨?_,tail.2⟩⟩
        · intro instruction member
          rcases List.mem_cons.mp member with rfl | member
          · exact pick_free correct found
          · exact tail.1 instruction member
        · intro instruction member
          obtain ⟨item,itemMem,same⟩ := List.mem_map.mp member
          subst instruction
          exact pick_later correct found (schedule_member _ _ _ itemMem)

theorem generate_triangular (instructions : List Instruction) :
    FunctionalSubstitution.Triangular (generate instructions) :=
  schedule_triangular _ _ (by
    intro item member
    obtain ⟨instruction,_,rfl⟩ := List.mem_map.mp (eligible_subset instructions member)
    exact entry_correct instruction)

/-- A source dependency rank is a theorem hypothesis for complete elimination;
the executable selector computes its own order and never receives this rank. -/
def Ranked (rank : Nat → Nat) (pool : List Entry) : Prop :=
  ∀ item ∈ pool, ∀ other ∈ pool, item.instruction.address ∈ other.dependencies →
    rank other.instruction.address < rank item.instruction.address

private theorem exists_least (rank : Nat → Nat) (pool : List Entry) (nonempty : pool ≠ []) :
    ∃ item ∈ pool, ∀ other ∈ pool, rank item.instruction.address ≤ rank other.instruction.address := by
  induction pool with
  | nil => contradiction
  | cons head rest ih =>
      by_cases empty : rest=[]
      · subst rest
        exact ⟨head,by simp,by simp⟩
      · obtain ⟨least,member,lower⟩ := ih empty
        by_cases first : rank head.instruction.address ≤ rank least.instruction.address
        · refine ⟨head,by simp,?_⟩
          intro other hit
          rcases List.mem_cons.mp hit with rfl | hit
          · exact le_rfl
          · exact first.trans (lower other hit)
        · refine ⟨least,by simp [member],?_⟩
          intro other hit
          rcases List.mem_cons.mp hit with rfl | hit
          · omega
          · exact lower other hit

theorem ranked_admissible (rank : Nat → Nat) (pool : List Entry) (ranked : Ranked rank pool)
    (nonempty : pool ≠ []) : ∃ item ∈ pool, admissible pool item=true := by
  obtain ⟨item,member,least⟩ := exists_least rank pool nonempty
  refine ⟨item,member,?_⟩
  simp only [admissible,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨?_,List.all_eq_true.mpr ?_⟩
  · intro own
    have impossible := ranked item member item member own
    omega
  · intro other hit
    have absent : item.instruction.address ∉ other.dependencies := by
      intro depends
      have smaller := ranked item member other hit depends
      have lower := least other hit
      omega
    simp [absent]

theorem ranked_pick (rank : Nat → Nat) (pool : List Entry) (ranked : Ranked rank pool)
    (nonempty : pool ≠ []) : ∃ item, pick pool=some item := by
  obtain ⟨item,member,accepted⟩ := ranked_admissible rank pool ranked nonempty
  cases found : pick pool with
  | some item => exact ⟨item,rfl⟩
  | none =>
      have rejected : ∀ other ∈ pool, ¬admissible pool other=true := by
        simpa only [pick,List.find?_eq_none] using found
      exact False.elim (rejected item member accepted)

theorem remove_shorter (pool : List Entry) (item : Entry) (member : item ∈ pool) :
    (remove item.instruction.address pool).length < pool.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨item,member,by simp⟩

theorem ranked_all_addresses (fuel : Nat) (pool : List Entry) (rank : Nat → Nat)
    (ranked : Ranked rank pool) (enough : pool.length ≤ fuel) (item : Entry) (member : item ∈ pool) :
    ∃ generated ∈ schedule fuel pool, generated.instruction.address=item.instruction.address := by
  induction fuel generalizing pool with
  | zero => have empty : pool=[] := List.length_eq_zero_iff.mp (by omega); simp [empty] at member
  | succ fuel ih =>
      have nonempty : pool≠[] := fun empty => by simp [empty] at member
      obtain ⟨head,found⟩ := ranked_pick rank pool ranked nonempty
      rw [schedule,found]
      by_cases same : item.instruction.address=head.instruction.address
      · exact ⟨head,by simp,same.symm⟩
      · have tailRanked : Ranked rank (remove head.instruction.address pool) :=
          fun first firstMem other otherMem depends =>
            ranked first ((remove_sublist _ _).subset firstMem)
              other ((remove_sublist _ _).subset otherMem) depends
        have shorter := remove_shorter pool head (pick_member found)
        have tailEnough : (remove head.instruction.address pool).length ≤ fuel := by omega
        obtain ⟨generated,hit,address⟩ := ih _ tailRanked tailEnough
          ((remove_member _ _ _).mpr ⟨member,same⟩)
        exact ⟨generated,by simp [hit],address⟩

theorem generate_all_addresses (instructions : List Instruction) (rank : Nat → Nat)
    (ranked : Ranked rank (instructions.map entry)) (instruction : Instruction) (member : instruction ∈ instructions) :
    ∃ generated ∈ generate instructions, generated.address=instruction.address := by
  have raw : entry instruction ∈ instructions.map entry := List.mem_map.mpr ⟨instruction,member,rfl⟩
  have selfFree : (entry instruction).instruction.address ∉ (entry instruction).dependencies := by
    intro own
    have impossible := ranked (entry instruction) raw (entry instruction) raw own
    omega
  have selected : entry instruction ∈ eligible instructions := List.mem_filter.mpr ⟨raw,by simpa⟩
  have smaller : Ranked rank (eligible instructions) :=
    fun first firstMem other otherMem depends => ranked first (eligible_subset instructions firstMem)
      other (eligible_subset instructions otherMem) depends
  obtain ⟨item,hit,address⟩ := ranked_all_addresses instructions.length (eligible instructions) rank smaller
    (eligible_length instructions) (entry instruction) selected
  exact ⟨item.instruction,List.mem_map.mpr ⟨item,hit,rfl⟩,address⟩

theorem eligible_all_addresses (instructions : List Instruction) (rank : Nat → Nat)
    (ranked : Ranked rank (eligible instructions)) (item : Entry) (member : item ∈ eligible instructions) :
    ∃ generated ∈ generate instructions, generated.address=item.instruction.address := by
  obtain ⟨result,hit,address⟩ := ranked_all_addresses instructions.length (eligible instructions) rank ranked
    (eligible_length instructions) item member
  exact ⟨result.instruction,List.mem_map.mpr ⟨result,hit,rfl⟩,address⟩

def prepare (instructions : List Instruction) (program : Program) : Program :=
  FunctionalSubstitution.execute (generate instructions) program

theorem prepare_eliminates (instructions : List Instruction) (program : Program) (instruction : Instruction)
    (member : instruction ∈ generate instructions) :
    instruction.address ∉ FunctionalSubstitution.inputs (prepare instructions program).code :=
  FunctionalSubstitution.inputs_free _ _ (FunctionalSubstitution.execute_selected_free _
    (generate_triangular instructions) program instruction member)

theorem ranked_eliminates_all (instructions : List Instruction) (program : Program) (rank : Nat → Nat)
    (ranked : Ranked rank (instructions.map entry)) (instruction : Instruction) (member : instruction ∈ instructions) :
    instruction.address ∉ FunctionalSubstitution.inputs (prepare instructions program).code := by
  obtain ⟨generated,hit,address⟩ := generate_all_addresses instructions rank ranked instruction member
  rw [← address]
  exact prepare_eliminates instructions program generated hit

theorem prepare_correct (instructions : List Instruction) (program : Program)
    (entailed : ∀ environment, truth (program.eval environment)=true →
      ∀ instruction ∈ instructions, instruction.bind environment=environment) :
    FunctionalSubstitution.decideProgram (prepare instructions program)=true ↔
      ∃ environment, truth (program.eval environment)=true := by
  rw [FunctionalSubstitution.decideProgram_correct]
  exact FunctionalSubstitution.execute_satisfiable _ _
    (fun environment accepted instruction member =>
      entailed environment accepted instruction (generate_member instructions instruction member))

theorem prepare_read (instructions : List Instruction) (program : Program)
    (entailed : ∀ environment, truth (program.eval environment)=true →
      ∀ instruction ∈ instructions, instruction.bind environment=environment) (environment : Nat → Bool) :
    (FunctionalAffine.legal (generate instructions) environment &&
      truth ((prepare instructions program).eval environment))=truth (program.eval environment) := by
  by_cases legal : FunctionalAffine.legal (generate instructions) environment=true
  · rw [prepare,FunctionalSubstitution.eval_execute,
      FunctionalAffine.legal_fixed _ _ legal,legal,Bool.true_and]
  · have rejected : truth (program.eval environment)=false := by
      apply Bool.eq_false_iff.mpr
      intro accepted
      apply legal
      exact FunctionalAffine.legal_of_fixed _ _ (fun instruction member =>
        entailed environment accepted instruction (generate_member instructions instruction member))
    simp [legal,rejected]

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalSchedule
