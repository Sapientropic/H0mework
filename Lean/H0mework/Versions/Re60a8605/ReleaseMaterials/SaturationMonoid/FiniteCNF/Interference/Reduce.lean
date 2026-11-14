import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Nodes

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram

def Node.mapRefs (rename : Nat → Nat) : Node → Node
  | .constant z => .constant z
  | .input i => .input i
  | .add a b => .add (rename a) (rename b)
  | .mul a b => .mul (rename a) (rename b)
  | .neg a => .neg (rename a)
  | .band a b => .band (rename a) (rename b)
  | .bxor a b => .bxor (rename a) (rename b)
  | .bnot a => .bnot (rename a)
  | .phase a => .phase (rename a)
  | .select c a b => .select (rename c) (rename a) (rename b)

namespace Reduce

def Within (bound : Nat) (node : Node) : Prop :=
  ∀ i ∈ node.refs, i < bound

theorem node_congr (environment : Nat → Bool) (left right : Array ℤ) (node : Node)
    (same : ∀ i ∈ node.refs, left.getD i 0 = right.getD i 0) :
    node.run environment left = node.run environment right := by
  cases node <;> simp_all [Node.refs, Node.run]

theorem node_mapRefs (environment : Nat → Bool) (left right : Array ℤ)
    (node : Node) (rename : Nat → Nat)
    (same : ∀ i ∈ node.refs, right.getD (rename i) 0 = left.getD i 0) :
    (node.mapRefs rename).run environment right = node.run environment left := by
  cases node <;> simp_all [Node.refs, Node.run, Node.mapRefs]

theorem node_push (environment : Nat → Bool) (values : Array ℤ) (node : Node)
    (z : ℤ) (inside : Within values.size node) :
    node.run environment (values.push z) = node.run environment values := by
  apply node_congr
  intro i member
  exact getD_push_old values z i (inside i member)

structure Entry where
  node : Node
  output : Nat
  deriving Repr

structure State where
  code : Array Node
  table : List Entry
  deriving Repr

def Valid (state : State) : Prop :=
  (∀ environment, (run environment state.code).getD 0 0 = 0) ∧
  ∀ entry ∈ state.table,
    entry.output < state.code.size ∧ Within state.code.size entry.node ∧
    ∀ environment,
      (run environment state.code).getD entry.output 0 =
        entry.node.run environment (run environment state.code)

def initial : State := ⟨#[.constant 0], [⟨.constant 0, 0⟩]⟩

theorem initial_valid : Valid initial := by
  simp [Valid, initial, run, runCode, Node.run, Node.refs, Within, Array.getD]

def search (node : Node) : List Entry → Option Nat
  | [] => none
  | entry :: rest => if entry.node = node then some entry.output else search node rest

theorem search_some (node : Node) (table : List Entry) (output : Nat)
    (found : search node table = some output) :
    ∃ entry ∈ table, entry.node = node ∧ entry.output = output := by
  induction table with
  | nil => simp [search] at found
  | cons entry rest ih =>
      simp only [search] at found
      split at found
      · subst node
        exact ⟨entry, by simp, rfl, Option.some.inj found⟩
      · obtain ⟨other, member, equal, out⟩ := ih found
        exact ⟨other, by simp [member], equal, out⟩

def append (state : State) (node : Node) : State :=
  ⟨state.code.push node, ⟨node, state.code.size⟩ :: state.table⟩

theorem append_valid (state : State) (valid : Valid state) (node : Node)
    (inside : Within state.code.size node) (nonempty : 0 < state.code.size) :
    Valid (append state node) := by
  obtain ⟨zero, entries⟩ := valid
  constructor
  · intro environment
    simp only [append, run_push]
    rw [getD_push_old _ _ 0 (by simpa using nonempty)]
    exact zero environment
  · intro entry member
    simp only [append, List.mem_cons] at member
    rcases member with rfl | member
    · refine ⟨by simp [append], ?_, ?_⟩
      · intro i member
        exact Nat.lt_trans (inside i member) (by simp [append])
      · intro environment
        simp only [append, run_push]
        rw [← run_size environment state.code, getD_push_last]
        exact (node_push environment _ node _ (by simpa using inside)).symm
    · obtain ⟨output, bounded, reads⟩ := entries entry member
      refine ⟨by simpa [append] using Nat.lt_succ_of_lt output, ?_, ?_⟩
      · intro i member
        exact Nat.lt_trans (bounded i member) (by simp [append])
      · intro environment
        simp only [append, run_push]
        rw [getD_push_old _ _ _ (by simpa using output), reads]
        exact (node_push environment _ entry.node _ (by simpa using bounded)).symm

def intern (state : State) (node : Node) : State × Nat :=
  match search node state.table with
  | some output => (state, output)
  | none => (append state node, state.code.size)

theorem intern_sound (state : State) (valid : Valid state) (node : Node)
    (inside : Within state.code.size node) (nonempty : 0 < state.code.size) :
    Valid (intern state node).1 ∧
    state.code.size ≤ (intern state node).1.code.size ∧
    (intern state node).1.code.size ≤ state.code.size + 1 ∧
    (intern state node).2 < (intern state node).1.code.size ∧
    (∀ environment,
      run environment (intern state node).1.code = run environment state.code ∨
      run environment (intern state node).1.code =
        (run environment state.code).push (node.run environment (run environment state.code))) ∧
    ∀ environment,
      (run environment (intern state node).1.code).getD (intern state node).2 0 =
        node.run environment (run environment state.code) := by
  cases found : search node state.table with
  | some output =>
      obtain ⟨entry, member, same, out⟩ := search_some node state.table output found
      obtain ⟨bounded, _, reads⟩ := valid.2 entry member
      simp only [intern, found]
      refine ⟨valid, le_rfl, Nat.le_succ _, by simpa [out] using bounded,
        fun _ => Or.inl True.intro, ?_⟩
      intro environment
      simpa only [same, out] using reads environment
  | none =>
      simp only [intern, found]
      refine ⟨append_valid state valid node inside nonempty, ?_, ?_, ?_, ?_, ?_⟩
      · simp [append]
      · simp [append]
      · simp [append]
      · intro environment
        exact Or.inr (run_push environment state.code node)
      · intro environment
        simp only [append, run_push]
        simpa only [run_size] using getD_push_last (run environment state.code)
          (node.run environment (run environment state.code))

theorem intern_preserves (state : State) (valid : Valid state) (node : Node)
    (inside : Within state.code.size node) (nonempty : 0 < state.code.size)
    (environment : Nat → Bool) (i : Nat) (old : i < state.code.size) :
    (run environment (intern state node).1.code).getD i 0 =
      (run environment state.code).getD i 0 := by
  have transition := (intern_sound state valid node inside nonempty).2.2.2.2.1 environment
  rcases transition with same | pushed
  · rw [same]
  · rw [pushed]
    exact getD_push_old _ _ _ (by simpa using old)

structure Frame where
  state : State
  mapping : Array Nat
  deriving Repr

def Represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ) : Prop :=
  Valid frame.state ∧ 0 < frame.state.code.size ∧ frame.mapping.size = values.size ∧
  (∀ i, frame.mapping.getD i 0 < frame.state.code.size) ∧
  ∀ i, (run environment frame.state.code).getD (frame.mapping.getD i 0) 0 = values.getD i 0

def first : Frame := ⟨initial, #[]⟩

theorem first_represents (environment : Nat → Bool) : Represents first environment #[] := by
  refine ⟨initial_valid, by simp [first, initial], rfl, ?_, ?_⟩
  · intro i
    simp [first, initial, Array.getD]
  · intro i
    simpa [first, Array.getD] using initial_valid.1 environment

def emit (frame : Frame) (node : Node) : Frame :=
  let next := intern frame.state (node.mapRefs (fun i => frame.mapping.getD i 0))
  ⟨next.1, frame.mapping.push next.2⟩

theorem mapping_push (mapping : Array Nat) (output i : Nat) :
    (mapping.push output).getD i 0 = if i = mapping.size then output else mapping.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?]
  by_cases same : i = mapping.size <;> simp [Array.getElem?_push, same]

theorem emit_represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Represents frame environment values) (node : Node) :
    Represents (emit frame node) environment (values.push (node.run environment values)) := by
  obtain ⟨valid, nonempty, size, mapped, reads⟩ := represents
  let translated := node.mapRefs (fun i => frame.mapping.getD i 0)
  have inside : Within frame.state.code.size translated := by
    cases node <;> simp_all [translated, Node.mapRefs, Within, Node.refs]
  have next := intern_sound frame.state valid translated inside nonempty
  refine ⟨next.1, lt_of_lt_of_le nonempty next.2.1, ?_, ?_, ?_⟩
  · simpa [emit] using congrArg Nat.succ size
  · intro i
    change (frame.mapping.push (intern frame.state translated).2).getD i 0 <
      (intern frame.state translated).1.code.size
    rw [mapping_push]
    by_cases last : i = frame.mapping.size
    · simpa only [if_pos last] using next.2.2.2.1
    · simpa only [if_neg last] using
        lt_of_lt_of_le (mapped i) next.2.1
  · intro i
    change (run environment (intern frame.state translated).1.code).getD
      ((frame.mapping.push (intern frame.state translated).2).getD i 0) 0 = _
    rw [mapping_push]
    by_cases last : i = frame.mapping.size
    · subst i
      have source := node_mapRefs environment values (run environment frame.state.code)
        node (fun j => frame.mapping.getD j 0) (fun j _ => reads j)
      have output := next.2.2.2.2.2 environment
      simp only [ite_true]
      rw [output, source]
      rw [size]
      exact (getD_push_last values (node.run environment values)).symm
    · have before := intern_preserves frame.state valid translated inside nonempty environment
        (frame.mapping.getD i 0) (mapped i)
      have notLast : i ≠ values.size := by simpa only [← size] using last
      rw [if_neg last, getD_push_any, if_neg notLast]
      exact before.trans (reads i)

def fold : Frame → List Node → Frame
  | frame, [] => frame
  | frame, node :: rest => fold (emit frame node) rest

theorem fold_represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Represents frame environment values) (code : List Node) :
    Represents (fold frame code) environment (runCode environment values code) := by
  induction code generalizing frame values with
  | nil => exact represents
  | cons node rest ih => exact ih _ _ (emit_represents frame environment values represents node)

def compact (code : Array Node) : Frame := fold first code.toList

theorem compact_represents (code : Array Node) (environment : Nat → Bool) :
    Represents (compact code) environment (run environment code) :=
  fold_represents first environment #[] (first_represents environment) code.toList

theorem compact_reads (code : Array Node) (environment : Nat → Bool) (output : Nat) :
    (run environment (compact code).state.code).getD ((compact code).mapping.getD output 0) 0 =
      (run environment code).getD output 0 :=
  (compact_represents code environment).2.2.2.2 output

def searchVisits (node : Node) : List Entry → Nat
  | [] => 0
  | entry :: rest => if entry.node = node then 1 else 1 + searchVisits node rest

theorem searchVisits_le (node : Node) (table : List Entry) :
    searchVisits node table ≤ table.length := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      simp only [searchVisits, List.length_cons]
      split <;> omega

theorem intern_sizes (state : State) (node : Node) :
    (intern state node).1.code.size ≤ state.code.size + 1 ∧
    (intern state node).1.table.length ≤ state.table.length + 1 := by
  unfold intern
  split <;> simp [append]

theorem fold_code_size (frame : Frame) (code : List Node) :
    (fold frame code).state.code.size ≤ frame.state.code.size + code.length := by
  induction code generalizing frame with
  | nil => simp [fold]
  | cons node rest ih =>
      have bounded := (intern_sizes frame.state (node.mapRefs (fun i => frame.mapping.getD i 0))).1
      have later := ih (emit frame node)
      simp only [fold, emit, List.length_cons] at *
      omega

theorem compact_code_size (code : Array Node) :
    (compact code).state.code.size ≤ code.size + 1 := by
  simpa [compact, first, initial, Nat.add_comm] using fold_code_size first code.toList

/-- Counts actual entry comparisons, including every unsuccessful lookup. -/
def visits : Frame → List Node → Nat
  | _, [] => 0
  | frame, node :: rest =>
      searchVisits (node.mapRefs (fun i => frame.mapping.getD i 0)) frame.state.table +
        visits (emit frame node) rest

theorem visits_le (frame : Frame) (code : List Node) :
    visits frame code ≤ code.length * (frame.state.table.length + code.length) := by
  induction code generalizing frame with
  | nil => simp [visits]
  | cons node rest ih =>
      have scanned := searchVisits_le (node.mapRefs (fun i => frame.mapping.getD i 0)) frame.state.table
      have growth := (intern_sizes frame.state (node.mapRefs (fun i => frame.mapping.getD i 0))).2
      have later := ih (emit frame node)
      simp only [emit] at later
      have bound := Nat.mul_le_mul_left rest.length (Nat.add_le_add_right growth rest.length)
      simp only [visits, List.length_cons, emit]
      nlinarith

theorem compact_visits_le (code : Array Node) :
    visits first code.toList ≤ code.size * (code.size + 1) := by
  simpa [first, initial, Nat.add_comm] using visits_le first code.toList

def Forward (code : Array Node) : Prop := ∀ i (hi : i < code.size), Within i code[i]

theorem initial_forward : Forward initial.code := by
  intro i hi
  have zero : i = 0 := by simpa [initial] using hi
  subst i
  simp [initial, Within, Node.refs]

theorem append_forward (state : State) (forward : Forward state.code) (node : Node)
    (inside : Within state.code.size node) : Forward (append state node).code := by
  intro i hi
  by_cases old : i < state.code.size
  · simpa only [append, Array.getElem_push_lt old] using forward i old
  · have last : i = state.code.size := by simp only [append, Array.size_push] at hi; omega
    subst i
    simpa [append] using inside

theorem intern_forward (state : State) (forward : Forward state.code) (node : Node)
    (inside : Within state.code.size node) : Forward (intern state node).1.code := by
  unfold intern
  split
  · exact forward
  · exact append_forward state forward node inside

theorem fold_forward (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Represents frame environment values) (forward : Forward frame.state.code)
    (code : List Node) : Forward (fold frame code).state.code := by
  induction code generalizing frame values with
  | nil => exact forward
  | cons node rest ih =>
      apply ih _ _ (emit_represents frame environment values represents node)
      apply intern_forward _ forward
      have mapped := represents.2.2.2.1
      cases node <;> simp_all [Node.mapRefs, Within, Node.refs]

theorem compact_forward (code : Array Node) : Forward (compact code).state.code :=
  fold_forward first (fun _ => false) #[] (first_represents _) initial_forward code.toList

end Reduce

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram
