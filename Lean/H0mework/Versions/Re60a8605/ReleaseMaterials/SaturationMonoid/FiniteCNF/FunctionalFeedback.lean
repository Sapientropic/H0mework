import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalSchedule.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalPivot

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalFeedback
open InterferenceProgram
open FunctionalSubstitution (Instruction Free)
open FunctionalSchedule (Entry)

def Safe (pool : List Entry) : Prop :=
  ∀ item ∈ pool, item.Correct ∧ item.instruction.address ∉ item.dependencies

theorem eligible_safe (source : List Instruction) : Safe (FunctionalSchedule.eligible source) := by
  intro item member
  change item ∈ (source.map FunctionalSchedule.entry).filter _ at member
  obtain ⟨member,free⟩ := List.mem_filter.mp member
  obtain ⟨instruction,_,rfl⟩ := List.mem_map.mp member
  exact ⟨FunctionalSchedule.entry_correct instruction,of_decide_eq_true free⟩

/-- A cyclic dependency pool supplies its own next source instruction. -/
def choose (pool : List Entry) : Option Entry :=
  match FunctionalSchedule.pick pool with
  | some item => some item
  | none => pool.head?

theorem choose_prefers {pool : List Entry} {item : Entry}
    (found : FunctionalSchedule.pick pool=some item) : choose pool=some item := by
  simp [choose,found]

theorem choose_member {pool : List Entry} {item : Entry} (found : choose pool=some item) : item ∈ pool := by
  unfold choose at found
  cases picked : FunctionalSchedule.pick pool with
  | some candidate =>
      simp only [picked,Option.some.injEq] at found
      subst item
      exact FunctionalSchedule.pick_member picked
  | none =>
      simp only [picked] at found
      cases pool with
      | nil => simp at found
      | cons head rest =>
          simp only [List.head?_cons,Option.some.injEq] at found
          subst item
          exact List.mem_cons_self

theorem choose_none_iff (pool : List Entry) : choose pool=none ↔ pool=[] := by
  constructor
  · intro failed
    cases pool with
    | nil => rfl
    | cons head rest =>
        cases picked : FunctionalSchedule.pick (head::rest) <;> simp [choose,picked] at failed
  · rintro rfl
    rfl

theorem choose_next (pool : List Entry) (nonempty : pool≠[]) : ∃ item, choose pool=some item := by
  cases found : choose pool with
  | none => exact False.elim (nonempty ((choose_none_iff pool).mp found))
  | some item => exact ⟨item,rfl⟩

def retain (address : Nat) (pool : List Entry) : List Entry :=
  (FunctionalSchedule.remove address pool).filter (fun item => decide (address ∉ item.dependencies))

theorem retain_sublist (address : Nat) (pool : List Entry) : (retain address pool).Sublist pool :=
  List.filter_sublist.trans (FunctionalSchedule.remove_sublist address pool)

theorem retain_member (address : Nat) (pool : List Entry) (item : Entry) :
    item ∈ retain address pool ↔ item ∈ pool ∧ item.instruction.address ≠ address ∧ address ∉ item.dependencies := by
  simp [retain,FunctionalSchedule.remove_member,and_assoc]

theorem retain_shorter (pool : List Entry) (item : Entry) (member : item ∈ pool) :
    (retain item.instruction.address pool).length < pool.length :=
  List.filter_sublist.length_le.trans_lt (FunctionalSchedule.remove_shorter pool item member)

theorem retain_safe (address : Nat) (pool : List Entry) (safe : Safe pool) : Safe (retain address pool) :=
  fun item member => safe item ((retain_sublist address pool).subset member)

theorem choose_free {pool : List Entry} {item : Entry} (safe : Safe pool)
    (found : choose pool=some item) : Free item.instruction.address item.instruction.body.code := by
  have actual := safe item (choose_member found)
  apply (FunctionalSubstitution.free_iff _ _).mpr
  exact fun member => actual.2 ((actual.1 _).mpr member)

theorem retain_later {pool : List Entry} {item other : Entry} (safe : Safe pool)
    (member : other ∈ retain item.instruction.address pool) :
    item.instruction.address ≠ other.instruction.address ∧
      Free item.instruction.address other.instruction.body.code := by
  obtain ⟨member,different,absent⟩ := (retain_member _ _ _).mp member
  exact ⟨Ne.symm different,(FunctionalSubstitution.free_iff _ _).mpr
    (fun present => absent (((safe other member).1 _).mpr present))⟩

def arrange : Nat → List Entry → List Entry
  | 0,_ => []
  | fuel+1,pool => match choose pool with
    | none => []
    | some item => item::arrange fuel (retain item.instruction.address pool)

theorem arrange_nil (fuel : Nat) : arrange fuel []=[] := by cases fuel <;> rfl

theorem arrange_member (fuel : Nat) (pool : List Entry) (item : Entry)
    (member : item ∈ arrange fuel pool) : item ∈ pool := by
  induction fuel generalizing pool with
  | zero => simp [arrange] at member
  | succ fuel ih =>
      simp only [arrange] at member
      split at member
      · simp at member
      · rename_i head found
        rcases List.mem_cons.mp member with rfl | later
        · exact choose_member found
        · exact (retain_sublist _ _).subset (ih _ later)

theorem arrange_length (fuel : Nat) (pool : List Entry) : (arrange fuel pool).length ≤ fuel := by
  induction fuel generalizing pool with
  | zero => simp [arrange]
  | succ fuel ih =>
      simp only [arrange]
      split
      · simp
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _)

theorem arrange_nonempty (fuel : Nat) (pool : List Entry) (positive : 0<fuel) (nonempty : pool≠[]) :
    arrange fuel pool≠[] := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      obtain ⟨item,found⟩ := choose_next pool nonempty
      simp [arrange,found]

theorem arrange_triangular (fuel : Nat) (pool : List Entry) (safe : Safe pool) :
    FunctionalSubstitution.Triangular ((arrange fuel pool).map Entry.instruction) := by
  induction fuel generalizing pool with
  | zero => simp [arrange,FunctionalSubstitution.Triangular]
  | succ fuel ih =>
      simp only [arrange]
      split
      · simp [FunctionalSubstitution.Triangular]
      · rename_i head found
        have tail := ih _ (retain_safe head.instruction.address pool safe)
        simp only [List.map_cons]
        refine ⟨?_,List.pairwise_cons.mpr ⟨?_,tail.2⟩⟩
        · intro instruction member
          rcases List.mem_cons.mp member with rfl | member
          · exact choose_free safe found
          · exact tail.1 instruction member
        · intro instruction member
          obtain ⟨item,hit,rfl⟩ := List.mem_map.mp member
          exact retain_later safe (arrange_member _ _ _ hit)

def generate (source : List Instruction) : List Instruction :=
  (arrange source.length (FunctionalSchedule.eligible source)).map Entry.instruction

theorem generate_member (source : List Instruction) (instruction : Instruction)
    (member : instruction ∈ generate source) : instruction ∈ source := by
  change instruction ∈ (arrange source.length (FunctionalSchedule.eligible source)).map Entry.instruction at member
  obtain ⟨item,itemMem,same⟩ := List.mem_map.mp member
  subst instruction
  have raw := FunctionalSchedule.eligible_subset source (arrange_member _ _ _ itemMem)
  obtain ⟨original,originalMem,entryEq⟩ := List.mem_map.mp raw
  subst item
  exact originalMem

theorem generate_length (source : List Instruction) : (generate source).length ≤ source.length := by
  simpa only [generate,List.length_map] using arrange_length source.length (FunctionalSchedule.eligible source)

theorem generate_triangular (source : List Instruction) : FunctionalSubstitution.Triangular (generate source) :=
  arrange_triangular _ _ (eligible_safe source)

theorem generate_nonempty (source : List Instruction) (nonempty : FunctionalSchedule.eligible source≠[]) :
    generate source≠[] := by
  have count : 0<source.length := by
    have shorter := FunctionalSchedule.eligible_length source
    have positive := List.length_pos_iff.mpr nonempty
    omega
  have produced := arrange_nonempty source.length (FunctionalSchedule.eligible source) count nonempty
  intro empty
  exact produced (by simpa only [generate,List.map_eq_nil_iff] using empty)

def prepare (source : List Instruction) (program : Program) : Program :=
  FunctionalSubstitution.execute (generate source) program

theorem prepare_eliminates (source : List Instruction) (program : Program) (instruction : Instruction)
    (member : instruction ∈ generate source) : instruction.address ∉ FunctionalSubstitution.inputs (prepare source program).code :=
  FunctionalSubstitution.inputs_free _ _ (FunctionalSubstitution.execute_selected_free _
    (generate_triangular source) program instruction member)

theorem prepare_correct (source : List Instruction) (program : Program)
    (entailed : ∀ environment, truth (program.eval environment)=true →
      ∀ instruction ∈ source, instruction.bind environment=environment) :
    FunctionalSubstitution.decideProgram (prepare source program)=true ↔
      ∃ environment, truth (program.eval environment)=true := by
  rw [FunctionalSubstitution.decideProgram_correct]
  exact FunctionalSubstitution.execute_satisfiable _ _
    (fun environment accepted instruction member =>
      entailed environment accepted instruction (generate_member source instruction member))

theorem prepare_read (source : List Instruction) (program : Program)
    (entailed : ∀ environment, truth (program.eval environment)=true →
      ∀ instruction ∈ source, instruction.bind environment=environment) (environment : Nat → Bool) :
    (FunctionalAffine.legal (generate source) environment &&
      truth ((prepare source program).eval environment))=truth (program.eval environment) := by
  by_cases legal : FunctionalAffine.legal (generate source) environment=true
  · rw [prepare,FunctionalSubstitution.eval_execute,
      FunctionalAffine.legal_fixed _ _ legal,legal,Bool.true_and]
  · have rejected : truth (program.eval environment)=false := by
      apply Bool.eq_false_iff.mpr
      intro accepted
      apply legal
      exact FunctionalAffine.legal_of_fixed _ _ (fun instruction member =>
        entailed environment accepted instruction (generate_member source instruction member))
    simp [legal,rejected]

theorem candidates_read {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (environment : Nat → Bool) :
    (FunctionalAffine.legal (generate (Affine.ConditionalPivot.candidates formula basis)) environment &&
      truth ((prepare (Affine.ConditionalPivot.candidates formula basis)
        (Affine.Acceptance.compile (Affine.Table.coordinates n basis) formula)).eval environment))=
      CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment) := by
  rw [prepare_read _ _ (Affine.ConditionalPivot.candidates_entails formula basis valid.2 valid.1),
    Affine.Acceptance.eval_compile,truth_bit]

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalFeedback
