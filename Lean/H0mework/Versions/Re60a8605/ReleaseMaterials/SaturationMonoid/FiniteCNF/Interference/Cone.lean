import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Shared

/-! The two generated program roots determine a backward dependency cone.
Only original prior references are dependencies of the sequential evaluator.
The public producer first reuses the existing forward sharing constructor, then
copies exactly its marked nodes from an empty array. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram.Cone

def has (index : Nat) : List Nat → Bool
  | [] => false
  | head :: rest => if index = head then true else has index rest

theorem has_true_iff (index : Nat) (indices : List Nat) : has index indices = true ↔ index ∈ indices := by
  induction indices with
  | nil => simp [has]
  | cons head rest ih => by_cases same : index = head <;> simp [has, same, ih]

def addIndex (index : Nat) (indices : List Nat) : List Nat :=
  if has index indices then indices else index :: indices

theorem mem_addIndex (index value : Nat) (indices : List Nat) :
    value ∈ addIndex index indices ↔ value = index ∨ value ∈ indices := by
  unfold addIndex
  split
  · rename_i present
    have member := (has_true_iff index indices).mp present
    constructor
    · exact Or.inr
    · rintro (rfl | same)
      · exact member
      · exact same
  · simp

theorem addIndex_length (index : Nat) (indices : List Nat) :
    (addIndex index indices).length ≤ indices.length + 1 := by
  unfold addIndex
  split <;> simp

def pullRefs (index : Nat) : List Nat → List Nat → List Nat
  | [], needed => needed
  | ref :: refs, needed =>
      pullRefs index refs (if ref < index then addIndex ref needed else needed)

theorem mem_pullRefs (index value : Nat) (refs needed : List Nat) :
    value ∈ pullRefs index refs needed ↔ value ∈ needed ∨ (value ∈ refs ∧ value < index) := by
  induction refs generalizing needed with
  | nil => simp [pullRefs]
  | cons ref refs ih =>
      rw [pullRefs, ih]
      by_cases earlier : ref < index
      · rw [if_pos earlier, mem_addIndex]
        simp only [List.mem_cons]
        by_cases same : value = ref
        · subst value; simp [earlier]
        · simp [same]
      · rw [if_neg earlier]
        simp only [List.mem_cons]
        by_cases same : value = ref
        · subst value; simp [earlier]
        · simp [same]

def pull (index : Nat) (node : Node) (needed : List Nat) : List Nat :=
  if has index needed then pullRefs index node.refs needed else needed

theorem pull_extends (index : Nat) (node : Node) (needed : List Nat) : needed ⊆ pull index node needed := by
  intro value member
  unfold pull
  split
  · exact (mem_pullRefs index value node.refs needed).mpr (Or.inl member)
  · exact member

theorem pull_high (index value : Nat) (node : Node) (needed : List Nat) (high : index ≤ value) :
    value ∈ pull index node needed ↔ value ∈ needed := by
  unfold pull
  split
  · rw [mem_pullRefs]
    have impossible : ¬ value < index := by omega
    simp only [impossible, and_false, or_false]
  · rfl

theorem pull_dependency (index ref : Nat) (node : Node) (needed : List Nat)
    (selected : index ∈ needed) (member : ref ∈ node.refs) (earlier : ref < index) :
    ref ∈ pull index node needed := by
  rw [pull, if_pos ((has_true_iff index needed).mpr selected)]
  exact (mem_pullRefs index ref node.refs needed).mpr (Or.inr ⟨member, earlier⟩)

def markFrom (offset : Nat) : List Node → List Nat → List Nat
  | [], needed => needed
  | node :: rest, needed => pull offset node (markFrom (offset + 1) rest needed)

theorem mark_extends (offset : Nat) (code : List Node) (roots : List Nat) :
    roots ⊆ markFrom offset code roots := by
  induction code generalizing offset with
  | nil => exact List.Subset.refl _
  | cons node rest ih => exact fun _ member => pull_extends offset node _ (ih (offset+1) member)

def ClosedFrom (offset : Nat) (code : List Node) (needed : List Nat) : Prop :=
  ∀ i (bound : i < code.length), offset + i ∈ needed →
    ∀ ref ∈ (code[i]).refs, ref < offset + i → ref ∈ needed

theorem mark_closed (offset : Nat) (code : List Node) (roots : List Nat) :
    ClosedFrom offset code (markFrom offset code roots) := by
  induction code generalizing offset with
  | nil => intro i bound; simp at bound
  | cons node rest ih =>
      intro i bound selected ref member earlier
      cases i with
      | zero =>
          have selected' : offset ∈ markFrom (offset+1) rest roots :=
            (pull_high offset offset node _ (Nat.le_refl _)).mp (by simpa [markFrom] using selected)
          exact pull_dependency offset ref node _ selected' (by simpa using member) (by simpa using earlier)
      | succ i =>
          have tailBound : i < rest.length := by simp only [List.length_cons] at bound; omega
          have selected' : offset+1+i ∈ markFrom (offset+1) rest roots :=
            (pull_high offset (offset+1+i) node _ (by omega)).mp
              (by simpa [markFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selected)
          have tail := ih (offset+1) i tailBound selected' ref (by simpa using member) (by omega)
          exact pull_extends offset node _ tail

theorem mark_minimal (offset : Nat) (code : List Node) (roots target : List Nat)
    (contains : roots ⊆ target) (closed : ClosedFrom offset code target) :
    markFrom offset code roots ⊆ target := by
  induction code generalizing offset with
  | nil => exact contains
  | cons node rest ih =>
      have tailClosed : ClosedFrom (offset+1) rest target := by
        intro i bound selected ref member earlier
        exact closed (i+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ bound)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selected)
          ref (by simpa using member) (by omega)
      have tail := ih (offset+1) tailClosed
      intro value member
      change value ∈ pull offset node (markFrom (offset+1) rest roots) at member
      unfold pull at member
      split at member
      · rename_i selected
        rcases (mem_pullRefs offset value node.refs _).mp member with prior | ⟨ref, earlier⟩
        · exact tail prior
        · exact closed 0 (by simp) (by simpa using tail ((has_true_iff _ _).mp selected))
            value (by simpa using ref) (by simpa using earlier)
      · exact tail member

def roots (program : Program) : List Nat := [program.weight.val, program.phase.val]
def marked (program : Program) : List Nat := markFrom 0 program.code.toList (roots program)

theorem marked_roots (program : Program) : program.weight.val ∈ marked program ∧ program.phase.val ∈ marked program := by
  have included := mark_extends 0 program.code.toList (roots program)
  exact ⟨included (by simp [roots]), included (by simp [roots])⟩

theorem marked_closed (program : Program) : ClosedFrom 0 program.code.toList (marked program) :=
  mark_closed 0 program.code.toList (roots program)

theorem marked_minimal (program : Program) (target : List Nat)
    (contains : roots program ⊆ target) (closed : ClosedFrom 0 program.code.toList target) :
    marked program ⊆ target := mark_minimal 0 program.code.toList (roots program) target contains closed

structure Frame where
  code : Array Node
  mapping : Array Nat
  deriving Repr

def empty : Frame := ⟨#[], #[]⟩

def Represents (needed : List Nat) (frame : Frame) (environment : Nat → Bool) (values : Array ℤ) : Prop :=
  Reduce.Forward frame.code ∧ frame.mapping.size = values.size ∧
    ∀ i, i ∈ needed → i < values.size →
      frame.mapping.getD i 0 < frame.code.size ∧
        (run environment frame.code).getD (frame.mapping.getD i 0) 0 = values.getD i 0

theorem empty_represents (needed : List Nat) (environment : Nat → Bool) :
    Represents needed empty environment #[] := by
  refine ⟨?_, rfl, ?_⟩
  · intro i bound
    simp [empty] at bound
  · intro i _ bound
    simp at bound

def emit (needed : List Nat) (frame : Frame) (node : Node) : Frame :=
  if has frame.mapping.size needed then
    ⟨frame.code.push (node.mapRefs (fun i => frame.mapping.getD i 0)), frame.mapping.push frame.code.size⟩
  else ⟨frame.code, frame.mapping.push 0⟩

theorem emit_mapping_size (needed : List Nat) (frame : Frame) (node : Node) :
    (emit needed frame node).mapping.size = frame.mapping.size + 1 := by
  unfold emit
  split <;> simp

theorem emit_represents (needed : List Nat) (frame : Frame) (environment : Nat → Bool)
    (values : Array ℤ) (represents : Represents needed frame environment values) (node : Node)
    (inside : Reduce.Within values.size node)
    (dependencies : values.size ∈ needed → ∀ ref ∈ node.refs, ref ∈ needed) :
    Represents needed (emit needed frame node) environment (values.push (node.run environment values)) := by
  obtain ⟨forward, size, reads⟩ := represents
  unfold emit
  split
  · rename_i selected
    have selected' : values.size ∈ needed := size ▸ (has_true_iff _ _).mp selected
    have inputs (ref : Nat) (member : ref ∈ node.refs) :=
      reads ref (dependencies selected' ref member) (inside ref member)
    let translated := node.mapRefs (fun i => frame.mapping.getD i 0)
    have bounded : Reduce.Within frame.code.size translated := by
      cases node <;> simp_all [translated, Node.mapRefs, Reduce.Within, Node.refs]
    have source := Reduce.node_mapRefs environment values (run environment frame.code) node
      (fun i => frame.mapping.getD i 0) (fun i member => (inputs i member).2)
    refine ⟨Reduce.append_forward ⟨frame.code, []⟩ forward translated bounded, ?_, ?_⟩
    · simpa only [Array.size_push] using congrArg Nat.succ size
    · intro i member bound
      change (frame.mapping.push frame.code.size).getD i 0 < (frame.code.push translated).size ∧
        (run environment (frame.code.push translated)).getD ((frame.mapping.push frame.code.size).getD i 0) 0 =
          (values.push (node.run environment values)).getD i 0
      rw [Reduce.mapping_push]
      by_cases last : i = frame.mapping.size
      · subst i
        simp only [ite_true, Array.size_push]
        refine ⟨by omega, ?_⟩
        rw [run_push, source, size, getD_push_last]
        have output := getD_push_last (run environment frame.code) (node.run environment values)
        simpa only [run_size] using output
      · have before : i < values.size := by simp only [Array.size_push] at bound; omega
        have old := reads i member before
        simp only [if_neg last, Array.size_push]
        refine ⟨by omega, ?_⟩
        rw [run_push, source, getD_push_old _ _ _ (by simpa only [run_size] using old.1),
          getD_push_old _ _ _ before]
        exact old.2
  · rename_i skipped
    refine ⟨forward, ?_, ?_⟩
    · simpa only [Array.size_push] using congrArg Nat.succ size
    · intro i member bound
      have notLast : i ≠ frame.mapping.size := by
        intro same
        subst i
        exact skipped ((has_true_iff _ _).mpr member)
      have before : i < values.size := by simp only [Array.size_push] at bound; omega
      change (frame.mapping.push 0).getD i 0 < frame.code.size ∧
        (run environment frame.code).getD ((frame.mapping.push 0).getD i 0) 0 =
          (values.push (node.run environment values)).getD i 0
      rw [Reduce.mapping_push, if_neg notLast, getD_push_old _ _ _ before]
      exact reads i member before

def ForwardFrom (offset : Nat) (code : List Node) : Prop :=
  ∀ i (bound : i < code.length), Reduce.Within (offset+i) code[i]

def fold (needed : List Nat) : Frame → List Node → Frame
  | frame, [] => frame
  | frame, node :: rest => fold needed (emit needed frame node) rest

theorem fold_represents (needed : List Nat) (frame : Frame) (environment : Nat → Bool)
    (values : Array ℤ) (represents : Represents needed frame environment values) (code : List Node)
    (forward : ForwardFrom values.size code) (closed : ClosedFrom values.size code needed) :
    Represents needed (fold needed frame code) environment (runCode environment values code) := by
  induction code generalizing frame values with
  | nil => exact represents
  | cons node rest ih =>
      have inside := forward 0 (by simp)
      change Reduce.Within values.size node at inside
      have dependencies : values.size ∈ needed → ∀ ref ∈ node.refs, ref ∈ needed := by
        intro selected ref member
        exact closed 0 (by simp) (by simpa using selected) ref (by simpa using member) (by simpa using inside ref member)
      have next := emit_represents needed frame environment values represents node inside dependencies
      apply ih _ _ next
      · intro i bound
        have tail := forward (i+1) (by simp only [List.length_cons]; omega)
        change Reduce.Within (values.size+(i+1)) rest[i] at tail
        simpa only [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail
      · intro i bound selected ref member earlier
        apply closed (i+1) (by simp only [List.length_cons]; omega)
        · simpa [Array.size_push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using selected
        · simpa using member
        · simp only [Array.size_push] at earlier
          omega

def compact (program : Program) : Frame :=
  let code := program.code.toList
  fold (markFrom 0 code (roots program)) empty code

theorem compact_represents (program : Program) (forward : Reduce.Forward program.code)
    (environment : Nat → Bool) :
    Represents (marked program) (compact program) environment (run environment program.code) := by
  apply fold_represents (marked program) empty environment #[] (empty_represents _ _) program.code.toList
  · intro i bound
    simpa only [Array.size_empty, Nat.zero_add, Array.getElem_toList] using forward i (by simpa using bound)
  · exact marked_closed program

def trim (program : Program) (forward : Reduce.Forward program.code) : Program :=
  let generated := compact program
  let valid := compact_represents program forward (fun _ => false)
  let source := marked_roots program
  ⟨generated.code,
    ⟨generated.mapping.getD program.weight.val 0,
      (valid.2.2 program.weight.val source.1 (by simp)).1⟩,
    ⟨generated.mapping.getD program.phase.val 0,
      (valid.2.2 program.phase.val source.2 (by simp)).1⟩⟩

theorem eval_trim (program : Program) (forward : Reduce.Forward program.code) (environment : Nat → Bool) :
    (trim program forward).eval environment = program.eval environment := by
  have generated := compact_represents program forward environment
  have source := marked_roots program
  have weight := (generated.2.2 program.weight.val source.1 (by simp)).2
  have phase := (generated.2.2 program.phase.val source.2 (by simp)).2
  exact congrArg₂ (fun w p => w * sign p) weight phase

theorem trim_forward (program : Program) (forward : Reduce.Forward program.code) :
    Reduce.Forward (trim program forward).code := (compact_represents program forward (fun _ => false)).1

/-- Sharing generates the forward source consumed by the cone; it is not an input certificate. -/
def pruneCone (program : Program) : Program := trim program.share program.share_forward

theorem eval_pruneCone (program : Program) (environment : Nat → Bool) :
    (pruneCone program).eval environment = program.eval environment :=
  (eval_trim program.share program.share_forward environment).trans (program.eval_share environment)

theorem pruneCone_forward (program : Program) : Reduce.Forward (pruneCone program).code :=
  trim_forward program.share program.share_forward

theorem refs_length (node : Node) : node.refs.length ≤ 3 := by cases node <;> simp [Node.refs]

theorem pullRefs_length (index : Nat) (refs needed : List Nat) :
    (pullRefs index refs needed).length ≤ needed.length + refs.length := by
  induction refs generalizing needed with
  | nil => simp [pullRefs]
  | cons ref refs ih =>
      rw [pullRefs]
      split
      · have bound := addIndex_length ref needed
        have rest := ih (addIndex ref needed)
        simp only [List.length_cons]
        omega
      · have rest := ih needed
        simp only [List.length_cons]
        omega

theorem pull_length (index : Nat) (node : Node) (needed : List Nat) :
    (pull index node needed).length ≤ needed.length + 3 := by
  unfold pull
  split
  · have bound := pullRefs_length index node.refs needed
    have refs := refs_length node
    omega
  · omega

theorem mark_length (offset : Nat) (code : List Node) (roots : List Nat) :
    (markFrom offset code roots).length ≤ roots.length + 3 * code.length := by
  induction code generalizing offset with
  | nil => simp [markFrom]
  | cons node rest ih =>
      have before := ih (offset+1)
      have after := pull_length offset node (markFrom (offset+1) rest roots)
      simp only [markFrom, List.length_cons]
      omega

theorem marked_bound (program : Program) (i : Nat) (member : i ∈ marked program) : i < program.code.size := by
  apply List.mem_range.mp
  apply marked_minimal program (List.range program.code.size) _ _ member
  · intro root source
    simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at source
    rcases source with rfl | rfl <;> simp
  · intro index bound selected ref member earlier
    have selected' := List.mem_range.mp selected
    exact List.mem_range.mpr (by omega)

def kept (needed : List Nat) (offset : Nat) : List Node → Nat
  | [] => 0
  | _ :: rest => (if has offset needed then 1 else 0) + kept needed (offset+1) rest

theorem kept_le (needed : List Nat) (offset : Nat) (code : List Node) : kept needed offset code ≤ code.length := by
  induction code generalizing offset with
  | nil => rfl
  | cons node rest ih =>
      have bound := ih (offset+1)
      simp only [kept, List.length_cons]
      split <;> omega

theorem emit_code_size (needed : List Nat) (frame : Frame) (node : Node) :
    (emit needed frame node).code.size = frame.code.size + if has frame.mapping.size needed then 1 else 0 := by
  unfold emit
  split <;> simp_all

theorem fold_code_size (needed : List Nat) (frame : Frame) (code : List Node) :
    (fold needed frame code).code.size = frame.code.size + kept needed frame.mapping.size code := by
  induction code generalizing frame with
  | nil => simp [fold, kept]
  | cons node rest ih =>
      rw [fold, ih, emit_code_size, emit_mapping_size, kept, Nat.add_assoc]

theorem trim_size (program : Program) (forward : Reduce.Forward program.code) :
    (trim program forward).code.size = kept (marked program) 0 program.code.toList := by
  simp only [trim, compact, fold_code_size, empty, Array.size_empty, Nat.zero_add]
  rfl

theorem trim_size_le (program : Program) (forward : Reduce.Forward program.code) :
    (trim program forward).code.size ≤ program.code.size := by
  rw [trim_size]
  simpa only [Array.length_toList] using kept_le (marked program) 0 program.code.toList

theorem pruneCone_size (program : Program) : (pruneCone program).code.size ≤ program.code.size + 1 :=
  (trim_size_le program.share program.share_forward).trans program.share_size

theorem kept_strict (needed : List Nat) (offset : Nat) (code : List Node) (i : Nat)
    (bound : i < code.length) (dead : has (offset+i) needed = false) : kept needed offset code < code.length := by
  induction code generalizing offset i with
  | nil => simp at bound
  | cons node rest ih =>
      cases i with
      | zero =>
          have tail := kept_le needed (offset+1) rest
          simp only [Nat.add_zero] at dead
          simp only [kept, dead, Bool.false_eq_true, if_false, Nat.zero_add, List.length_cons]
          omega
      | succ i =>
          have tail := ih (offset+1) i (by simp only [List.length_cons] at bound; omega)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dead)
          simp only [kept, List.length_cons]
          split <;> omega

theorem trim_strict (program : Program) (forward : Reduce.Forward program.code)
    (i : Nat) (bound : i < program.code.size) (dead : has i (marked program) = false) :
    (trim program forward).code.size < program.code.size := by
  rw [trim_size]
  simpa only [Array.length_toList, Nat.zero_add] using
    kept_strict (marked program) 0 program.code.toList i (by simpa using bound) (by simpa using dead)

/-- Every failed label comparison is retained in the count. -/
def hasVisits (index : Nat) : List Nat → Nat
  | [] => 0
  | head :: rest => if index = head then 1 else 1 + hasVisits index rest

theorem hasVisits_le (index : Nat) (indices : List Nat) : hasVisits index indices ≤ indices.length := by
  induction indices with
  | nil => rfl
  | cons head rest ih => simp only [hasVisits, List.length_cons]; split <;> omega

def pullVisits (index : Nat) : List Nat → List Nat → Nat
  | [], _ => 0
  | ref :: refs, needed =>
      1 + if ref < index then hasVisits ref needed + pullVisits index refs (addIndex ref needed)
        else pullVisits index refs needed

theorem pullVisits_le (index : Nat) (refs needed : List Nat) :
    pullVisits index refs needed ≤ refs.length * (needed.length + refs.length + 1) := by
  induction refs generalizing needed with
  | nil => simp [pullVisits]
  | cons ref refs ih =>
      simp only [pullVisits, List.length_cons]
      split
      · have lookup := hasVisits_le ref needed
        have growth := addIndex_length ref needed
        have tail := ih (addIndex ref needed)
        have multiplied := Nat.mul_le_mul_left refs.length (Nat.add_le_add_right (Nat.add_le_add_right growth refs.length) 1)
        nlinarith
      · have tail := ih needed
        nlinarith

def markVisits (offset : Nat) : List Node → List Nat → Nat
  | [], _ => 0
  | node :: rest, roots =>
      let needed := markFrom (offset+1) rest roots
      markVisits (offset+1) rest roots + hasVisits offset needed +
        if has offset needed then pullVisits offset node.refs needed else 0

theorem markVisits_le (offset : Nat) (code : List Node) (roots : List Nat) :
    markVisits offset code roots ≤ code.length * (4 * roots.length + 12 * code.length) := by
  induction code generalizing offset with
  | nil => simp [markVisits]
  | cons node rest ih =>
      let needed := markFrom (offset+1) rest roots
      have previous := ih (offset+1)
      have size := mark_length (offset+1) rest roots
      have lookup := hasVisits_le offset needed
      have pulled := pullVisits_le offset node.refs needed
      have refs := refs_length node
      have bound : node.refs.length * (needed.length + node.refs.length + 1) ≤ 3 * (needed.length + 4) := by
        exact Nat.mul_le_mul refs (by omega)
      simp only [markVisits, List.length_cons]
      split <;> change _ ≤ (rest.length+1) * (4*roots.length+12*(rest.length+1))
      all_goals change needed.length ≤ roots.length + 3 * rest.length at size
      all_goals nlinarith

def copyVisits (needed : List Nat) (offset : Nat) : List Node → Nat
  | [] => 0
  | _ :: rest => hasVisits offset needed + copyVisits needed (offset+1) rest

theorem copyVisits_le (needed : List Nat) (offset : Nat) (code : List Node) :
    copyVisits needed offset code ≤ code.length * needed.length := by
  induction code generalizing offset with
  | nil => simp [copyVisits]
  | cons node rest ih =>
      have head := hasVisits_le offset needed
      have tail := ih (offset+1)
      simp only [copyVisits, List.length_cons]
      nlinarith

def markRefs (offset : Nat) : List Node → List Nat → Nat
  | [], _ => 0
  | node :: rest, roots =>
      markRefs (offset+1) rest roots +
        if has offset (markFrom (offset+1) rest roots) then node.refs.length else 0

theorem markRefs_le (offset : Nat) (code : List Node) (roots : List Nat) :
    markRefs offset code roots ≤ 3 * code.length := by
  induction code generalizing offset with
  | nil => simp [markRefs]
  | cons node rest ih =>
      have head := refs_length node
      have tail := ih (offset+1)
      simp only [markRefs, List.length_cons]
      split <;> omega

def copyRefs (needed : List Nat) (offset : Nat) : List Node → Nat
  | [] => 0
  | node :: rest => (if has offset needed then node.refs.length else 0) + copyRefs needed (offset+1) rest

theorem copyRefs_le (needed : List Nat) (offset : Nat) (code : List Node) :
    copyRefs needed offset code ≤ 3 * code.length := by
  induction code generalizing offset with
  | nil => simp [copyRefs]
  | cons node rest ih =>
      have head := refs_length node
      have tail := ih (offset+1)
      simp only [copyRefs, List.length_cons]
      split <;> omega

/-- These counts cover the cone's two source-list passes, label comparisons,
reference fields and final two output remaps. They are not integer or TM2 steps. -/
structure Visits where
  sourceNodes : Nat
  labelComparisons : Nat
  references : Nat
  outputRemaps : Nat
  deriving Repr

def visits (program : Program) : Visits :=
  let code := program.code.toList
  let needed := marked program
  ⟨2 * code.length,
    markVisits 0 code (roots program) + copyVisits needed 0 code,
    markRefs 0 code (roots program) + copyRefs needed 0 code,
    2⟩

theorem visits_bound (program : Program) :
    (visits program).sourceNodes = 2 * program.code.size ∧
    (visits program).labelComparisons ≤ program.code.size * (10 + 15 * program.code.size) ∧
    (visits program).references ≤ 6 * program.code.size ∧
    (visits program).outputRemaps = 2 := by
  have marking := markVisits_le 0 program.code.toList (roots program)
  have copying := copyVisits_le (marked program) 0 program.code.toList
  have size := mark_length 0 program.code.toList (roots program)
  have refsM := markRefs_le 0 program.code.toList (roots program)
  have refsC := copyRefs_le (marked program) 0 program.code.toList
  have multiplied := Nat.mul_le_mul_left program.code.size size
  simp only [roots, List.length_cons, List.length_nil, Array.length_toList] at marking size multiplied refsM
  change markVisits 0 program.code.toList (roots program) ≤ program.code.size * (8 + 12 * program.code.size) at marking
  change markRefs 0 program.code.toList (roots program) ≤ 3 * program.code.size at refsM
  change program.code.size * (marked program).length ≤ program.code.size * (2 + 3 * program.code.size) at multiplied
  change (marked program).length ≤ 2 + 3 * program.code.size at size
  simp only [Array.length_toList] at copying refsC
  refine ⟨rfl, ?_, ?_, rfl⟩
  · change markVisits 0 program.code.toList (roots program) + copyVisits (marked program) 0 program.code.toList ≤ _
    nlinarith
  · change markRefs 0 program.code.toList (roots program) + copyRefs (marked program) 0 program.code.toList ≤ _
    omega

theorem pruneCone_visits_bound (program : Program) :
    (visits program.share).sourceNodes ≤ 2 * (program.code.size + 1) ∧
    (visits program.share).labelComparisons ≤ (program.code.size + 1) * (10 + 15 * (program.code.size + 1)) ∧
    (visits program.share).references ≤ 6 * (program.code.size + 1) ∧
    (visits program.share).outputRemaps = 2 := by
  have counts := visits_bound program.share
  have size := program.share_size
  refine ⟨?_, ?_, ?_, counts.2.2.2⟩
  · rw [counts.1]
    exact Nat.mul_le_mul_left 2 size
  · exact counts.2.1.trans (Nat.mul_le_mul size (by omega))
  · exact counts.2.2.1.trans (Nat.mul_le_mul_left 6 size)

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram.Cone
