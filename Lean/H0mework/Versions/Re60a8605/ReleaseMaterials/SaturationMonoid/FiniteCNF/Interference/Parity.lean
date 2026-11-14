import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Shared

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram.Parity

def eval (read : Nat → Bool) : List Nat → Bool
  | [] => false
  | i :: rest => read i ^^ eval read rest

def toggle (i : Nat) (terms : List Nat) : List Nat :=
  if i ∈ terms then terms.erase i else i :: terms

theorem eval_erase (read : Nat → Bool) (terms : List Nat) (i : Nat) (member : i ∈ terms) :
    eval read terms = (read i ^^ eval read (terms.erase i)) := by
  induction terms with
  | nil => simp at member
  | cons j rest ih =>
      by_cases same : j = i
      · subst j
        simp [eval]
      · have tail : i ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        rw [eval, ih tail]
        simp only [List.erase_cons, beq_iff_eq, if_neg same, eval]
        exact Bool.xor_left_comm _ _ _

theorem eval_toggle (read : Nat → Bool) (terms : List Nat) (i : Nat) :
    eval read (toggle i terms) = (read i ^^ eval read terms) := by
  unfold toggle
  split
  · rename_i member
    rw [eval_erase read terms i member]
    simp
  · rfl

theorem toggle_nodup (terms : List Nat) (i : Nat) (nodup : terms.Nodup) :
    (toggle i terms).Nodup := by
  unfold toggle
  split
  · exact nodup.erase i
  · exact List.nodup_cons.mpr ⟨by assumption, nodup⟩

def merge : List Nat → List Nat → List Nat
  | [], right => right
  | i :: rest, right => merge rest (toggle i right)

theorem eval_merge (read : Nat → Bool) (left right : List Nat) :
    eval read (merge left right) = (eval read left ^^ eval read right) := by
  induction left generalizing right with
  | nil => simp [merge, eval]
  | cons i rest ih =>
      rw [merge, ih, eval_toggle, eval]
      simp [Bool.xor_left_comm]

theorem merge_nodup (left right : List Nat) (nodup : right.Nodup) :
    (merge left right).Nodup := by
  induction left generalizing right with
  | nil => exact nodup
  | cons i rest ih => exact ih _ (toggle_nodup right i nodup)

def Within (bound : Nat) (terms : List Nat) : Prop := ∀ i ∈ terms, i < bound

theorem toggle_within (terms : List Nat) (bound i : Nat)
    (inside : Within bound terms) (index : i < bound) : Within bound (toggle i terms) := by
  intro j member
  unfold toggle at member
  split at member
  · exact inside j (List.mem_of_mem_erase member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact index
    · exact inside j member

theorem merge_within (left right : List Nat) (bound : Nat)
    (leftInside : Within bound left) (rightInside : Within bound right) :
    Within bound (merge left right) := by
  induction left generalizing right with
  | nil => exact rightInside
  | cons i rest ih =>
      exact ih _ (fun j h => leftInside j (by simp [h]))
        (toggle_within right bound i rightInside (leftInside i (by simp)))

theorem eval_congr (left right : Nat → Bool) (terms : List Nat)
    (same : ∀ i ∈ terms, left i = right i) : eval left terms = eval right terms := by
  induction terms with
  | nil => rfl
  | cons i rest ih =>
      simp only [eval, same i (by simp), ih (fun j h => same j (by simp [h]))]

theorem eval_push (values : Array ℤ) (z : ℤ) (terms : List Nat) (inside : Within values.size terms) :
    eval (fun i => truth ((values.push z).getD i 0)) terms =
      eval (fun i => truth (values.getD i 0)) terms := by
  apply eval_congr
  intro i member
  exact congrArg truth (getD_push_old values z i (inside i member))

def nextRow (rows : Array (List Nat)) : Node → List Nat
  | .bxor a b => merge (rows.getD a []) (rows.getD b [])
  | .constant z => if z = 0 then [] else [rows.size]
  | _ => [rows.size]

def Represents (rows : Array (List Nat)) (values : Array ℤ) : Prop :=
  rows.size = values.size ∧
  (∀ i, Within values.size (rows.getD i [])) ∧
  ∀ i, eval (fun j => truth (values.getD j 0)) (rows.getD i []) = truth (values.getD i 0)

theorem nextRow_within (rows : Array (List Nat)) (values : Array ℤ)
    (represents : Represents rows values) (node : Node) :
    Within (values.size + 1) (nextRow rows node) := by
  cases node <;> simp only [nextRow]
  case constant z =>
    split
    · simp [Within]
    · simp [Within, represents.1]
  case bxor a b =>
    have bounded := merge_within _ _ _ (represents.2.1 a) (represents.2.1 b)
    exact fun j member => Nat.lt_succ_of_lt (bounded j member)
  all_goals simp [Within, represents.1]

theorem nextRow_value (rows : Array (List Nat)) (values : Array ℤ)
    (represents : Represents rows values) (node : Node) (environment : Nat → Bool) :
    eval (fun i => truth ((values.push (node.run environment values)).getD i 0)) (nextRow rows node) =
      truth (node.run environment values) := by
  cases node <;> simp only [nextRow]
  case constant z =>
    split
    · rename_i zero
      simp [eval, Node.run, zero, truth]
    · simp only [eval, represents.1, getD_push_last, Bool.xor_false]
  case bxor a b =>
    rw [eval_merge, eval_push _ _ _ (represents.2.1 a), eval_push _ _ _ (represents.2.1 b),
      represents.2.2 a, represents.2.2 b]
    simp only [Node.run, truth_bit]
  all_goals simp only [eval, represents.1, getD_push_last, Bool.xor_false]

theorem rows_push (rows : Array (List Nat)) (row : List Nat) (i : Nat) :
    (rows.push row).getD i [] = if i = rows.size then row else rows.getD i [] := by
  simp only [Array.getD_eq_getD_getElem?]
  by_cases same : i = rows.size <;> simp [Array.getElem?_push, same]

theorem push_represents (rows : Array (List Nat)) (values : Array ℤ)
    (represents : Represents rows values) (node : Node) (environment : Nat → Bool) :
    Represents (rows.push (nextRow rows node)) (values.push (node.run environment values)) := by
  refine ⟨by simpa using represents.1, ?_, ?_⟩
  · intro i
    rw [rows_push]
    split
    · simpa only [Array.size_push] using nextRow_within rows values represents node
    · exact fun j member => by simpa using Nat.lt_succ_of_lt (represents.2.1 i j member)
  · intro i
    rw [rows_push]
    by_cases last : i = rows.size
    · subst i
      rw [if_pos rfl, represents.1, getD_push_last]
      exact nextRow_value rows values represents node environment
    · rw [if_neg last, eval_push _ _ _ (represents.2.1 i), represents.2.2 i,
        getD_push_any, if_neg (by simpa only [← represents.1] using last)]

def rowsFold : Array (List Nat) → List Node → Array (List Nat)
  | rows, [] => rows
  | rows, node :: rest => rowsFold (rows.push (nextRow rows node)) rest

theorem rowsFold_represents (rows : Array (List Nat)) (values : Array ℤ)
    (represents : Represents rows values) (code : List Node) (environment : Nat → Bool) :
    Represents (rowsFold rows code) (runCode environment values code) := by
  induction code generalizing rows values with
  | nil => exact represents
  | cons node rest ih => exact ih _ _ (push_represents rows values represents node environment)

def sourceRows (code : Array Node) : Array (List Nat) := rowsFold #[] code.toList

theorem sourceRows_represents (code : Array Node) (environment : Nat → Bool) :
    Represents (sourceRows code) (run environment code) := by
  apply rowsFold_represents
  simp [Represents, Array.getD, Within, eval, truth]

theorem sourceRows_value (code : Array Node) (environment : Nat → Bool) (output : Nat) :
    eval (fun i => truth ((run environment code).getD i 0)) ((sourceRows code).getD output []) =
      truth ((run environment code).getD output 0) :=
  (sourceRows_represents code environment).2.2 output

def build : Reduce.State → List Nat → Reduce.State × Nat
  | state, [] => (state, 0)
  | state, i :: rest =>
      let tail := build state rest
      Reduce.smartIntern tail.1 (.bxor i tail.2)

theorem build_sound (state : Reduce.State) (valid : Reduce.Valid state)
    (nonempty : 0 < state.code.size) (terms : List Nat) (inside : Within state.code.size terms) :
    Reduce.Valid (build state terms).1 ∧
    state.code.size ≤ (build state terms).1.code.size ∧
    (build state terms).1.code.size ≤ state.code.size + terms.length ∧
    (build state terms).2 < (build state terms).1.code.size ∧
    (∀ environment i, i < state.code.size →
      (run environment (build state terms).1.code).getD i 0 = (run environment state.code).getD i 0) ∧
    ∀ environment,
      (run environment (build state terms).1.code).getD (build state terms).2 0 =
        bit (eval (fun i => truth ((run environment state.code).getD i 0)) terms) := by
  induction terms with
  | nil =>
      refine ⟨valid, le_rfl, by simp [build], nonempty, fun _ _ _ => rfl, ?_⟩
      intro environment
      exact valid.1 environment
  | cons i rest ih =>
      have tail := ih (fun j member => inside j (by simp [member]))
      have index : i < state.code.size := inside i (by simp)
      have tailNonempty := lt_of_lt_of_le nonempty tail.2.1
      have bounded : Reduce.Within (build state rest).1.code.size (.bxor i (build state rest).2) := by
        simp [Reduce.Within, Node.refs]
        exact ⟨lt_of_lt_of_le index tail.2.1, tail.2.2.2.1⟩
      have next := Reduce.smartIntern_sound (build state rest).1 tail.1 _ bounded tailNonempty
      refine ⟨next.1, tail.2.1.trans next.2.1, ?_, next.2.2.2.1, ?_, ?_⟩
      · have before := tail.2.2.1
        have after := next.2.2.1
        simp only [build, List.length_cons]
        omega
      · intro environment j bound
        exact (Reduce.smartIntern_preserves (build state rest).1 tail.1 _ bounded tailNonempty
          environment j (lt_of_lt_of_le bound tail.2.1)).trans (tail.2.2.2.2.1 environment j bound)
      · intro environment
        rw [build, next.2.2.2.2.2 environment]
        simp only [Node.run, tail.2.2.2.2.2 environment, truth_bit, eval,
          tail.2.2.2.2.1 environment i index]

theorem build_forward (state : Reduce.State) (valid : Reduce.Valid state)
    (nonempty : 0 < state.code.size) (forward : Reduce.Forward state.code)
    (terms : List Nat) (inside : Within state.code.size terms) : Reduce.Forward (build state terms).1.code := by
  induction terms with
  | nil => exact forward
  | cons i rest ih =>
      have restInside : Within state.code.size rest := fun j member => inside j (by simp [member])
      have tail := build_sound state valid nonempty rest restInside
      have nextForward := ih restInside
      apply Reduce.intern_forward _ nextForward
      apply Reduce.foldNode_within
      simp [Reduce.Within, Node.refs]
      exact ⟨lt_of_lt_of_le (inside i (by simp)) tail.2.1, tail.2.2.2.1⟩

theorem eval_map (read : Nat → Bool) (rename : Nat → Nat) (terms : List Nat) :
    eval read (terms.map rename) = eval (fun i => read (rename i)) terms := by
  induction terms with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, eval, ih]

structure Frame where
  source : Reduce.Frame
  rows : Array (List Nat)
  deriving Repr

def Frame.Represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ) : Prop :=
  Reduce.Represents frame.source environment values ∧ Parity.Represents frame.rows values

def first : Frame := ⟨Reduce.first, #[]⟩

theorem first_represents (environment : Nat → Bool) : Frame.Represents first environment #[] := by
  refine ⟨Reduce.first_represents environment, ?_⟩
  simp [first, Represents, Array.getD, Within, eval, truth]

def emitSource (frame : Frame) : Node → Reduce.Frame
  | .bxor a b =>
      let terms := merge (frame.rows.getD a []) (frame.rows.getD b [])
      let generated := build frame.source.state (merge (terms.map (fun i => frame.source.mapping.getD i 0)) [])
      ⟨generated.1, frame.source.mapping.push generated.2⟩
  | node => Reduce.smartEmit frame.source node

def emit (frame : Frame) (node : Node) : Frame :=
  ⟨emitSource frame node, frame.rows.push (nextRow frame.rows node)⟩

theorem emit_represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Frame.Represents frame environment values) (node : Node) :
    Frame.Represents (emit frame node) environment (values.push (node.run environment values)) := by
  refine ⟨?_, push_represents frame.rows values represents.2 node environment⟩
  cases node
  case constant z => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.constant z)
  case input i => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.input i)
  case add a b => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.add a b)
  case mul a b => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.mul a b)
  case neg a => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.neg a)
  case band a b => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.band a b)
  case bnot a => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.bnot a)
  case phase a => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.phase a)
  case select c a b => exact Reduce.smartEmit_represents frame.source environment values represents.1 (.select c a b)
  case bxor a b =>
    obtain ⟨valid, nonempty, size, mapped, reads⟩ := represents.1
    let terms := merge (frame.rows.getD a []) (frame.rows.getD b [])
    let mappedTerms := merge (terms.map (fun i => frame.source.mapping.getD i 0)) []
    have inside : Within frame.source.state.code.size mappedTerms := by
      apply merge_within
      · intro i member
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
        exact mapped j
      · simp [Within]
    have generated := build_sound frame.source.state valid nonempty mappedTerms inside
    have outputValue : (run environment (build frame.source.state mappedTerms).1.code).getD
        (build frame.source.state mappedTerms).2 0 = (Node.bxor a b).run environment values := by
      rw [generated.2.2.2.2.2 environment, eval_merge, eval_map]
      simp only [eval, Bool.xor_false]
      have same : eval (fun i => truth ((run environment frame.source.state.code).getD
          (frame.source.mapping.getD i 0) 0)) terms =
          eval (fun i => truth (values.getD i 0)) terms :=
        eval_congr _ _ terms (fun i _ => congrArg truth (reads i))
      rw [same, eval_merge, represents.2.2.2 a, represents.2.2.2 b]
      rfl
    refine ⟨generated.1, lt_of_lt_of_le nonempty generated.2.1, ?_, ?_, ?_⟩
    · simpa [emit, emitSource] using congrArg Nat.succ size
    · intro i
      change (frame.source.mapping.push (build frame.source.state mappedTerms).2).getD i 0 <
        (build frame.source.state mappedTerms).1.code.size
      rw [Reduce.mapping_push]
      split
      · exact generated.2.2.2.1
      · exact lt_of_lt_of_le (mapped i) generated.2.1
    · intro i
      change (run environment (build frame.source.state mappedTerms).1.code).getD
        ((frame.source.mapping.push (build frame.source.state mappedTerms).2).getD i 0) 0 = _
      rw [Reduce.mapping_push]
      by_cases last : i = frame.source.mapping.size
      · subst i
        rw [if_pos rfl, outputValue, size, getD_push_last]
      · rw [if_neg last, generated.2.2.2.2.1 environment _ (mapped i), reads,
          getD_push_any, if_neg (by simpa only [← size] using last)]

def fold : Frame → List Node → Frame
  | frame, [] => frame
  | frame, node :: rest => fold (emit frame node) rest

theorem fold_represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Frame.Represents frame environment values) (code : List Node) :
    Frame.Represents (fold frame code) environment (runCode environment values code) := by
  induction code generalizing frame values with
  | nil => exact represents
  | cons node rest ih => exact ih _ _ (emit_represents frame environment values represents node)

def compileCode (code : Array Node) : Frame := fold first code.toList

theorem compileCode_represents (code : Array Node) (environment : Nat → Bool) :
    Frame.Represents (compileCode code) environment (run environment code) :=
  fold_represents first environment #[] (first_represents environment) code.toList

theorem compileCode_reads (code : Array Node) (environment : Nat → Bool) (output : Nat) :
    (run environment (compileCode code).source.state.code).getD
        ((compileCode code).source.mapping.getD output 0) 0 =
      (run environment code).getD output 0 :=
  (compileCode_represents code environment).1.2.2.2.2 output

def rewrite (program : Program) : Program :=
  let generated := compileCode program.code
  let bounded := (compileCode_represents program.code (fun _ => false)).1.2.2.2.1
  ⟨generated.source.state.code,
    ⟨generated.source.mapping.getD program.weight.val 0, bounded program.weight.val⟩,
    ⟨generated.source.mapping.getD program.phase.val 0, bounded program.phase.val⟩⟩

theorem rewrite_eval (program : Program) (environment : Nat → Bool) :
    (rewrite program).eval environment = program.eval environment := by
  simp only [rewrite, Program.eval, compileCode_reads]

def RowsNodup (rows : Array (List Nat)) : Prop := ∀ i, (rows.getD i []).Nodup

theorem nextRow_nodup (rows : Array (List Nat)) (nodup : RowsNodup rows) (node : Node) :
    (nextRow rows node).Nodup := by
  cases node <;> simp only [nextRow]
  case bxor a b => exact merge_nodup _ _ (nodup b)
  case constant z => split <;> simp
  all_goals simp

theorem push_rowsNodup (rows : Array (List Nat)) (nodup : RowsNodup rows) (node : Node) :
    RowsNodup (rows.push (nextRow rows node)) := by
  intro i
  rw [rows_push]
  split
  · exact nextRow_nodup rows nodup node
  · exact nodup i

theorem length_le_of_within (terms : List Nat) (bound : Nat) (nodup : terms.Nodup)
    (inside : Within bound terms) : terms.length ≤ bound := by
  have contained : terms.toFinset ⊆ Finset.range bound := by
    intro i member
    exact Finset.mem_range.mpr (inside i (List.mem_toFinset.mp member))
  simpa only [List.toFinset_card_of_nodup nodup, Finset.card_range] using Finset.card_le_card contained

theorem toggle_length (terms : List Nat) (i : Nat) : (toggle i terms).length ≤ terms.length + 1 := by
  unfold toggle
  split
  · exact (List.length_erase_le).trans (Nat.le_succ _)
  · simp

theorem merge_length (left right : List Nat) : (merge left right).length ≤ left.length + right.length := by
  induction left generalizing right with
  | nil => simp [merge]
  | cons i rest ih =>
      have later := ih (toggle i right)
      have now := toggle_length right i
      simp only [merge, List.length_cons]
      omega

theorem emit_code_size (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Frame.Represents frame environment values) (nodup : RowsNodup frame.rows) (node : Node) :
    (emit frame node).source.state.code.size ≤ frame.source.state.code.size + frame.rows.size + 1 := by
  cases node
  case bxor a b =>
    let terms := merge (frame.rows.getD a []) (frame.rows.getD b [])
    let mapped := merge (terms.map (fun i => frame.source.mapping.getD i 0)) []
    have inside : Within frame.source.state.code.size mapped := by
      apply merge_within
      · intro i member
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
        exact represents.1.2.2.2.1 j
      · simp [Within]
    have generated := build_sound frame.source.state represents.1.1 represents.1.2.1 mapped inside
    have termsBound : terms.length ≤ values.size := length_le_of_within terms values.size
      (merge_nodup _ _ (nodup b))
      (merge_within _ _ _ (represents.2.2.1 a) (represents.2.2.1 b))
    have mappedBound : mapped.length ≤ terms.length := by
      simpa only [List.length_map, List.length_nil, Nat.add_zero] using
        merge_length (terms.map (fun i => frame.source.mapping.getD i 0)) []
    change (build frame.source.state mapped).1.code.size ≤ _
    have bound := generated.2.2.1
    have size := represents.2.1
    omega
  all_goals
    simp only [emit, emitSource, Reduce.smartEmit]
    exact (Reduce.smartIntern_sizes _ _).1.trans (by omega)

theorem fold_code_size (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Frame.Represents frame environment values) (nodup : RowsNodup frame.rows) (code : List Node) :
    (fold frame code).source.state.code.size ≤
      frame.source.state.code.size + code.length * (frame.rows.size + code.length + 1) := by
  induction code generalizing frame values with
  | nil => simp [fold]
  | cons node rest ih =>
      have emitted := emit_code_size frame environment values represents nodup node
      have later := ih (emit frame node) _ (emit_represents frame environment values represents node)
        (push_rowsNodup frame.rows nodup node)
      have rowSize : (emit frame node).rows.size = frame.rows.size + 1 := by simp [emit]
      rw [rowSize] at later
      change (fold (emit frame node) rest).source.state.code.size ≤ _
      simp only [List.length_cons]
      nlinarith

theorem compileCode_size (code : Array Node) :
    (compileCode code).source.state.code.size ≤ 1 + code.size * (code.size + 1) := by
  have nodup : RowsNodup first.rows := by intro i; simp [first, Array.getD]
  simpa [compileCode, first, Reduce.first, Reduce.initial] using
    fold_code_size first (fun _ => false) #[] (first_represents _) nodup code.toList

theorem emit_forward (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Frame.Represents frame environment values)
    (forward : Reduce.Forward frame.source.state.code) (node : Node) :
    Reduce.Forward (emit frame node).source.state.code := by
  cases node
  case bxor a b =>
    apply build_forward _ represents.1.1 represents.1.2.1 forward
    apply merge_within
    · intro i member
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp member
      exact represents.1.2.2.2.1 j
    · simp [Within]
  all_goals
    simp only [emit, emitSource]
    exact Reduce.smartFold_forward _ _ _ represents.1 forward [_]

theorem fold_forward (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Frame.Represents frame environment values)
    (forward : Reduce.Forward frame.source.state.code) (code : List Node) :
    Reduce.Forward (fold frame code).source.state.code := by
  induction code generalizing frame values with
  | nil => exact forward
  | cons node rest ih =>
      exact ih _ _ (emit_represents frame environment values represents node)
        (emit_forward frame environment values represents forward node)

theorem compileCode_forward (code : Array Node) : Reduce.Forward (compileCode code).source.state.code :=
  fold_forward first (fun _ => false) #[] (first_represents _) Reduce.initial_forward code.toList

theorem rewrite_forward (program : Program) : Reduce.Forward (rewrite program).code :=
  compileCode_forward program.code

theorem rewrite_size (program : Program) :
    (rewrite program).code.size ≤ 1 + program.code.size * (program.code.size + 1) :=
  compileCode_size program.code

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram.Parity
