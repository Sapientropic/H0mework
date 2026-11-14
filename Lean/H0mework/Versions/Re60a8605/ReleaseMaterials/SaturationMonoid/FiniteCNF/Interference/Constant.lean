import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Reduce

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram.Reduce

def known (output : Nat) : List Entry → Option ℤ
  | [] => none
  | entry :: rest =>
      match entry.node with
      | .constant z => if entry.output = output then some z else known output rest
      | _ => known output rest

theorem known_source (output : Nat) (table : List Entry) (value : ℤ)
    (found : known output table = some value) :
    ∃ entry ∈ table, entry.output = output ∧ entry.node = .constant value := by
  induction table with
  | nil => simp [known] at found
  | cons entry rest ih =>
      cases shape : entry.node <;> simp only [known, shape] at found
      all_goals first
        | (split at found
           · cases Option.some.inj found
             exact ⟨entry, by simp, by assumption, shape⟩
           · obtain ⟨other, member, output, node⟩ := ih found
             exact ⟨other, by simp [member], output, node⟩)
        | (obtain ⟨other, member, output, node⟩ := ih found
           exact ⟨other, by simp [member], output, node⟩)

theorem known_sound (state : State) (valid : Valid state) (environment : Nat → Bool)
    (output : Nat) (value : ℤ) (found : known output state.table = some value) :
    (run environment state.code).getD output 0 = value := by
  obtain ⟨entry, member, out, shape⟩ := known_source output state.table value found
  have reads := (valid.2 entry member).2.2 environment
  simpa only [out, shape, Node.run] using reads

def liftOne (f : ℤ → ℤ) (a : Option ℤ) : Option ℤ := a.map f

def liftTwo (f : ℤ → ℤ → ℤ) (a b : Option ℤ) : Option ℤ := do
  return f (← a) (← b)

def liftThree (f : ℤ → ℤ → ℤ → ℤ) (a b c : Option ℤ) : Option ℤ := do
  return f (← a) (← b) (← c)

def constantValue (read : Nat → Option ℤ) : Node → Option ℤ
  | .constant z => some z
  | .input _ => none
  | .add a b => liftTwo (· + ·) (read a) (read b)
  | .mul a b =>
      if read a = some 0 ∨ read b = some 0 then some 0
      else liftTwo (· * ·) (read a) (read b)
  | .neg a => liftOne Neg.neg (read a)
  | .band a b =>
      if read a = some 0 ∨ read b = some 0 then some 0
      else liftTwo (fun x y => bit (truth x && truth y)) (read a) (read b)
  | .bxor a b =>
      if a = b then some 0 else liftTwo (fun x y => bit (truth x ^^ truth y)) (read a) (read b)
  | .bnot a => liftOne (fun x => bit (!truth x)) (read a)
  | .phase a => liftOne sign (read a)
  | .select c a b => liftThree (fun z x y => if z = 0 then x else y) (read c) (read a) (read b)

theorem liftOne_sound (read : Nat → Option ℤ) (values : Array ℤ)
    (reads : ∀ i z, read i = some z → values.getD i 0 = z)
    (f : ℤ → ℤ) (a : Nat) (value : ℤ) (found : liftOne f (read a) = some value) :
    f (values.getD a 0) = value := by
  cases ha : read a <;> simp only [liftOne, ha, Option.map_none, Option.map_some] at found
  · cases found
  · simpa only [reads _ _ ha] using Option.some.inj found

theorem liftTwo_sound (read : Nat → Option ℤ) (values : Array ℤ)
    (reads : ∀ i z, read i = some z → values.getD i 0 = z)
    (f : ℤ → ℤ → ℤ) (a b : Nat) (value : ℤ)
    (found : liftTwo f (read a) (read b) = some value) :
    f (values.getD a 0) (values.getD b 0) = value := by
  cases ha : read a <;> cases hb : read b <;> simp [liftTwo, ha, hb] at found
  simpa only [reads _ _ ha, reads _ _ hb] using found

theorem liftThree_sound (read : Nat → Option ℤ) (values : Array ℤ)
    (reads : ∀ i z, read i = some z → values.getD i 0 = z)
    (f : ℤ → ℤ → ℤ → ℤ) (a b c : Nat) (value : ℤ)
    (found : liftThree f (read a) (read b) (read c) = some value) :
    f (values.getD a 0) (values.getD b 0) (values.getD c 0) = value := by
  cases ha : read a <;> cases hb : read b <;> cases hc : read c <;>
    simp [liftThree, ha, hb, hc] at found
  simpa only [reads _ _ ha, reads _ _ hb, reads _ _ hc] using found

theorem constantValue_sound (read : Nat → Option ℤ) (values : Array ℤ)
    (reads : ∀ i z, read i = some z → values.getD i 0 = z)
    (environment : Nat → Bool) (node : Node) (value : ℤ)
    (found : constantValue read node = some value) : node.run environment values = value := by
  cases node with
  | constant z => exact Option.some.inj found
  | input i => cases found
  | add a b => exact liftTwo_sound read values reads (· + ·) a b value found
  | neg a => exact liftOne_sound read values reads Neg.neg a value found
  | bnot a => exact liftOne_sound read values reads (fun x => bit (!truth x)) a value found
  | phase a => exact liftOne_sound read values reads sign a value found
  | select c a b =>
      exact liftThree_sound read values reads (fun z x y => if z = 0 then x else y) c a b value found
  | mul a b =>
      simp only [constantValue] at found
      split at found
      · rename_i zero
        have result := Option.some.inj found
        rcases zero with zero | zero <;> simp [Node.run, reads _ _ zero, ← result]
      · exact liftTwo_sound read values reads (· * ·) a b value found
  | band a b =>
      simp only [constantValue] at found
      split at found
      · rename_i zero
        have result := Option.some.inj found
        rcases zero with zero | zero <;> simp [Node.run, reads _ _ zero, ← result, truth, bit]
      · exact liftTwo_sound read values reads (fun x y => bit (truth x && truth y)) a b value found
  | bxor a b =>
      simp only [constantValue] at found
      split at found
      · rename_i same
        have result := Option.some.inj found
        simp [Node.run, same, ← result, bit]
      · exact liftTwo_sound read values reads (fun x y => bit (truth x ^^ truth y)) a b value found

def foldNode (state : State) (node : Node) : Node :=
  match constantValue (fun i => known i state.table) node with
  | some value => .constant value
  | none => node

theorem foldNode_sound (state : State) (valid : Valid state) (node : Node)
    (environment : Nat → Bool) :
    (foldNode state node).run environment (run environment state.code) =
      node.run environment (run environment state.code) := by
  unfold foldNode
  split
  · rename_i value found
    exact (constantValue_sound _ _ (known_sound state valid environment) environment node value found).symm
  · rfl

theorem foldNode_within (state : State) (node : Node) (inside : Within state.code.size node) :
    Within state.code.size (foldNode state node) := by
  unfold foldNode
  split
  · simp [Within, Node.refs]
  · exact inside

def smartIntern (state : State) (node : Node) : State × Nat := intern state (foldNode state node)

theorem smartIntern_sound (state : State) (valid : Valid state) (node : Node)
    (inside : Within state.code.size node) (nonempty : 0 < state.code.size) :
    Valid (smartIntern state node).1 ∧
    state.code.size ≤ (smartIntern state node).1.code.size ∧
    (smartIntern state node).1.code.size ≤ state.code.size + 1 ∧
    (smartIntern state node).2 < (smartIntern state node).1.code.size ∧
    (∀ environment,
      run environment (smartIntern state node).1.code = run environment state.code ∨
      run environment (smartIntern state node).1.code =
        (run environment state.code).push (node.run environment (run environment state.code))) ∧
    ∀ environment,
      (run environment (smartIntern state node).1.code).getD (smartIntern state node).2 0 =
        node.run environment (run environment state.code) := by
  have result := intern_sound state valid (foldNode state node) (foldNode_within state node inside) nonempty
  simpa only [smartIntern, foldNode_sound state valid] using result

theorem smartIntern_preserves (state : State) (valid : Valid state) (node : Node)
    (inside : Within state.code.size node) (nonempty : 0 < state.code.size)
    (environment : Nat → Bool) (i : Nat) (old : i < state.code.size) :
    (run environment (smartIntern state node).1.code).getD i 0 =
      (run environment state.code).getD i 0 := by
  have transition := (smartIntern_sound state valid node inside nonempty).2.2.2.2.1 environment
  rcases transition with same | pushed
  · rw [same]
  · rw [pushed]
    exact getD_push_old _ _ _ (by simpa using old)

def smartEmit (frame : Frame) (node : Node) : Frame :=
  let next := smartIntern frame.state (node.mapRefs (fun i => frame.mapping.getD i 0))
  ⟨next.1, frame.mapping.push next.2⟩

theorem smartEmit_represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Represents frame environment values) (node : Node) :
    Represents (smartEmit frame node) environment (values.push (node.run environment values)) := by
  obtain ⟨valid, nonempty, size, mapped, reads⟩ := represents
  let translated := node.mapRefs (fun i => frame.mapping.getD i 0)
  have inside : Within frame.state.code.size translated := by
    cases node <;> simp_all [translated, Node.mapRefs, Within, Node.refs]
  have next := smartIntern_sound frame.state valid translated inside nonempty
  refine ⟨next.1, lt_of_lt_of_le nonempty next.2.1, ?_, ?_, ?_⟩
  · simpa [smartEmit] using congrArg Nat.succ size
  · intro i
    change (frame.mapping.push (smartIntern frame.state translated).2).getD i 0 <
      (smartIntern frame.state translated).1.code.size
    rw [mapping_push]
    by_cases last : i = frame.mapping.size
    · simpa only [if_pos last] using next.2.2.2.1
    · simpa only [if_neg last] using
        lt_of_lt_of_le (mapped i) next.2.1
  · intro i
    change (run environment (smartIntern frame.state translated).1.code).getD
      ((frame.mapping.push (smartIntern frame.state translated).2).getD i 0) 0 = _
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
    · have before := smartIntern_preserves frame.state valid translated inside nonempty environment
        (frame.mapping.getD i 0) (mapped i)
      have notLast : i ≠ values.size := by simpa only [← size] using last
      rw [if_neg last, getD_push_any, if_neg notLast]
      exact before.trans (reads i)

def smartFold : Frame → List Node → Frame
  | frame, [] => frame
  | frame, node :: rest => smartFold (smartEmit frame node) rest

theorem smartFold_represents (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Represents frame environment values) (code : List Node) :
    Represents (smartFold frame code) environment (runCode environment values code) := by
  induction code generalizing frame values with
  | nil => exact represents
  | cons node rest ih => exact ih _ _ (smartEmit_represents frame environment values represents node)

def smartCompact (code : Array Node) : Frame := smartFold first code.toList

theorem smartCompact_represents (code : Array Node) (environment : Nat → Bool) :
    Represents (smartCompact code) environment (run environment code) :=
  smartFold_represents first environment #[] (first_represents environment) code.toList

theorem smartCompact_reads (code : Array Node) (environment : Nat → Bool) (output : Nat) :
    (run environment (smartCompact code).state.code).getD ((smartCompact code).mapping.getD output 0) 0 =
      (run environment code).getD output 0 :=
  (smartCompact_represents code environment).2.2.2.2 output

theorem smartIntern_sizes (state : State) (node : Node) :
    (smartIntern state node).1.code.size ≤ state.code.size + 1 ∧
    (smartIntern state node).1.table.length ≤ state.table.length + 1 :=
  intern_sizes state (foldNode state node)

theorem smartFold_code_size (frame : Frame) (code : List Node) :
    (smartFold frame code).state.code.size ≤ frame.state.code.size + code.length := by
  induction code generalizing frame with
  | nil => simp [smartFold]
  | cons node rest ih =>
      have bounded := (smartIntern_sizes frame.state (node.mapRefs (fun i => frame.mapping.getD i 0))).1
      have later := ih (smartEmit frame node)
      simp only [smartFold, smartEmit, List.length_cons] at *
      omega

theorem smartCompact_code_size (code : Array Node) :
    (smartCompact code).state.code.size ≤ code.size + 1 := by
  simpa [smartCompact, first, initial, Nat.add_comm] using smartFold_code_size first code.toList

theorem smartFold_forward (frame : Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Represents frame environment values) (forward : Forward frame.state.code)
    (code : List Node) : Forward (smartFold frame code).state.code := by
  induction code generalizing frame values with
  | nil => exact forward
  | cons node rest ih =>
      apply ih _ _ (smartEmit_represents frame environment values represents node)
      apply intern_forward _ forward
      apply foldNode_within
      have mapped := represents.2.2.2.1
      cases node <;> simp_all [Node.mapRefs, Within, Node.refs]

theorem smartCompact_forward (code : Array Node) : Forward (smartCompact code).state.code :=
  smartFold_forward first (fun _ => false) #[] (first_represents _) initial_forward code.toList

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram.Reduce
