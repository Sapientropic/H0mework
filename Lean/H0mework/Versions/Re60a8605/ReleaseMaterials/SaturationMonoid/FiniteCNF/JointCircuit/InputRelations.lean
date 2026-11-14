import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Cost
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ForgetCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointInputRelations
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

def input (state : ArenaSource.State) (i : Nat) : Bool :=
  match state.arena.code.getD i (.constant 0) with | .input _ => true | _ => false

def address (state : ArenaSource.State) (i : Nat) : Nat :=
  match state.arena.code.getD i (.constant 0) with | .input a => a | _ => 0

def keep (state : ArenaSource.State) : List Nat := (List.range state.arena.code.size).filter (input state)

theorem keep_length (state : ArenaSource.State) : (keep state).length ≤ state.arena.code.size := by
  simpa only [keep,List.length_range] using List.length_filter_le (input state) (List.range state.arena.code.size)

theorem kept_input (state : ArenaSource.State) (i : Nat) (retained : i ∈ keep state) :
    i < state.arena.code.size ∧ state.arena.code.getD i (.constant 0)=.input (address state i) := by
  simp only [keep,List.mem_filter,List.mem_range] at retained
  refine ⟨retained.1,?_⟩
  have valid := retained.2
  cases shape : state.arena.code.getD i (.constant 0) <;> simp only [input,shape,Bool.false_eq_true] at valid
  all_goals try cases valid
  simp only [address,shape]

theorem kept_value (state : ArenaSource.State) (i : Nat) (retained : i ∈ keep state) (point : Nat → Bool) :
    JointCircuit.lift state point i=point (address state i) := by
  obtain ⟨inside,node⟩ := kept_input state i retained
  have law := ArenaAction.run_equation state.arena.code state.arena.forward point i inside
  simp only [JointCircuit.lift,law,node,Node.run,truth_bit]

theorem kept_present (state : ArenaSource.State) (i : Nat) (retained : i ∈ keep state) :
    address state i ∈ FunctionalSubstitution.inputs state.arena.code := by
  obtain ⟨inside,node⟩ := kept_input state i retained
  apply (FunctionalSubstitution.input_member _ _).mpr
  have slot := Array.getElem_mem_toList inside
  have actual : state.arena.code[i]=.input (address state i) := by simpa [Array.getD,inside] using node
  rwa [actual] at slot

def mapped (state : ArenaSource.State) (row : Row) : Row := ⟨row.vars.map (address state),row.rhs⟩

theorem parity_map (state : ArenaSource.State) (vars : List Nat)
    (retained : ∀ i ∈ vars, i ∈ keep state) (point : Nat → Bool) :
    Parity.eval point (vars.map (address state))=Parity.eval (JointCircuit.lift state point) vars := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.map_cons,Parity.eval,kept_value state i (retained i (by simp)) point,
        ih (fun j member => retained j (by simp [member]))]

theorem mapped_holds (state : ArenaSource.State) (row : Row)
    (retained : ∀ i ∈ row.vars, i ∈ keep state) (point : Nat → Bool) :
    (mapped state row).holds point=row.holds (JointCircuit.lift state point) := by
  simp only [mapped,Row.holds,Row.eval,parity_map state row.vars retained point]

def rawRows (state : ArenaSource.State) (basis : List Row) : List Row :=
  let source := AffineForget.Cost.generate state.arena.code.size (keep state) basis
  let erased := AffineForget.Cost.eraseRows (keep state) source.value.image.kernel
  erased.value

theorem rawRows_value (state : ArenaSource.State) (basis : List Row) :
    rawRows state basis=(AtomImage.generate (AffineForget.source state.arena.code.size (keep state) basis)).kernel.map (AffineForget.erase (keep state)) := by
  simp only [rawRows,AffineForget.Cost.generate_value,AffineForget.Cost.eraseRows_value,AffineForget.generate]

theorem rawRows_kept (state : ArenaSource.State) (basis : List Row) (row : Row) (member : row ∈ rawRows state basis) :
    ∀ i ∈ row.vars, i ∈ keep state := by
  rw [rawRows_value] at member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  intro i present
  exact of_decide_eq_true (List.mem_filter.mp present).2

theorem project_held (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) (accepted : holds basis point=true) :
    (AffineForget.generate n keep basis).value.holds point=true := by
  have finite := (AtomSource.holds_restrict n basis valid.2 point).trans accepted
  have projected := (AffineForget.generate_image n keep basis valid (fun i => point i.val)).mpr
    ⟨fun i => point i.val,finite,by intro i _; rfl⟩
  have inside := (AffineForget.generate_valid n keep basis).2
  cases shape : (AffineForget.generate n keep basis).value with
  | contradiction => simpa only [shape,Result.holds] using projected
  | basis rows =>
      rw [shape] at projected inside
      exact (AtomSource.holds_restrict n rows inside point).symm.trans projected

theorem rawRows_holds (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis point=true) : holds (rawRows state basis) point=true := by
  have held := project_held state.arena.code.size (keep state) basis valid point accepted
  simpa only [AffineForget.generate,EliminateCost.run_result,eliminate_holds,rawRows_value] using held

def rows (state : ArenaSource.State) (basis : List Row) : List Row :=
  (rawRows state basis).map (fun row => (CapacityMatching.RowCost.normalize (mapped state row)).value)

theorem rows_holds (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift state point)=true) : holds (rows state basis) point=true := by
  have raw := rawRows_holds state basis valid (JointCircuit.lift state point) accepted
  simp only [rows,holds,List.all_map]
  apply List.all_eq_true.mpr
  intro row member
  change (mapped state row).normalize.holds point=true
  rw [Row.normalize_holds,mapped_holds state row (rawRows_kept state basis row member)]
  exact List.all_eq_true.mp raw row member


theorem merge_support (allowed : Nat → Prop) (left right : List Nat)
    (a : ∀ i ∈ left, allowed i) (b : ∀ i ∈ right, allowed i) :
    ∀ i ∈ Parity.merge left right, allowed i := by
  induction left generalizing right with
  | nil => exact b
  | cons head rest ih =>
      apply ih _ (fun i member => a i (by simp [member]))
      intro i member
      unfold Parity.toggle at member
      split at member
      · exact b i (List.mem_of_mem_erase member)
      · rcases List.mem_cons.mp member with rfl | member
        · exact a i (by simp)
        · exact b i member

theorem rows_nodup (state : ArenaSource.State) (basis : List Row) (row : Row) (member : row ∈ rows state basis) : row.vars.Nodup := by
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact Row.normalize_nodup _

theorem rows_present (state : ArenaSource.State) (basis : List Row) (row : Row) (member : row ∈ rows state basis) :
    ∀ i ∈ row.vars, i ∈ FunctionalSubstitution.inputs state.arena.code := by
  obtain ⟨original,retained,rfl⟩ := List.mem_map.mp member
  apply merge_support (fun i => i ∈ FunctionalSubstitution.inputs state.arena.code) _ []
  · intro i present
    obtain ⟨slot,source,rfl⟩ := List.mem_map.mp present
    exact kept_present state slot (rawRows_kept state basis original retained slot source)
  · simp

theorem rows_length (state : ArenaSource.State) (basis : List Row) (row : Row) (member : row ∈ rows state basis) :
    row.vars.length ≤ (FunctionalSubstitution.inputs state.arena.code).length := by
  have subset : row.vars.toFinset ⊆ (FunctionalSubstitution.inputs state.arena.code).toFinset := by
    intro i present
    exact List.mem_toFinset.mpr (rows_present state basis row member i (List.mem_toFinset.mp present))
  have size := Finset.card_le_card subset
  have distinct : (FunctionalSubstitution.inputs state.arena.code).Nodup := List.nodup_dedup _
  rw [List.toFinset_card_of_nodup (rows_nodup state basis row member),
    List.toFinset_card_of_nodup distinct] at size
  exact size

open FunctionalSubstitution (Free)

theorem shift_free (i offset : Nat) (node : Node) (free : FunctionalSubstitution.Node.Free i node) :
    FunctionalSubstitution.Node.Free i (node.shift offset) := by cases node <;> exact free

theorem xor_free (i : Nat) (left right : Fragment) (a : Free i left.code) (b : Free i right.code) :
    Free i (left.xor right).code := by
  intro node member
  simp only [Fragment.xor,Fragment.binary,Array.toList_push,Array.toList_append,Array.toList_map,
    List.mem_append,List.mem_map,List.mem_singleton] at member
  rcases member with (member | ⟨original,member,rfl⟩) | rfl
  · exact a node member
  · exact shift_free i left.code.size original (b original member)
  · trivial

theorem terms_free (i : Nat) (terms : List Nat) (initial : Fragment)
    (missing : i ∉ terms) (free : Free i initial.code) : Free i (Gates.compileTerms terms initial).code := by
  induction terms generalizing initial with
  | nil => exact free
  | cons head rest ih =>
      apply ih _ (fun hit => missing (by simp [hit]))
      apply xor_free i initial (Fragment.input head) free
      intro node member
      simp [Fragment.input] at member
      subst node
      exact fun same => missing (by simp [same])

theorem row_free (i : Nat) (row : Row) (missing : i ∉ row.vars) : Free i (Gates.compileRow row).code := by
  apply terms_free i row.vars _ missing
  intro node member
  simp [Fragment.constant] at member
  subst node
  trivial

def instruction (row : Row) : Option FunctionalSubstitution.Instruction :=
  match row.vars with
  | [] => none
  | address::rest => some ⟨address,Gates.compileRow ⟨rest,row.rhs⟩⟩

theorem instruction_fixes (row : Row) (call : FunctionalSubstitution.Instruction)
    (found : instruction row=some call) (point : Nat → Bool) (accepted : row.holds point=true) : call.bind point=point := by
  cases row with
  | mk vars rhs =>
      cases vars with
      | nil => cases found
      | cons address rest =>
          simp only [instruction,Option.some.injEq] at found
          subst call
          apply FunctionalSubstitution.bind_fixes
          rw [Gates.eval_compileRow,truth_bit]
          simp only [Row.holds,Row.eval,Parity.eval,beq_iff_eq] at accepted
          simp only [Gates.value,Row.eval]
          cases a : point address <;> cases b : Parity.eval point rest <;> cases rhs <;> simp_all

theorem instruction_free (row : Row) (nodup : row.vars.Nodup) (call : FunctionalSubstitution.Instruction)
    (found : instruction row=some call) : Free call.address call.body.code := by
  cases row with
  | mk vars rhs =>
      cases vars with
      | nil => cases found
      | cons address rest =>
          simp only [instruction,Option.some.injEq] at found
          subst call
          exact row_free address ⟨rest,rhs⟩ (List.nodup_cons.mp nodup).1

def calls (state : ArenaSource.State) (basis : List Row) : List FunctionalSubstitution.Instruction :=
  (rows state basis).filterMap instruction

theorem calls_fixes (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) (point : Nat → Bool)
    (accepted : holds basis (JointCircuit.lift state point)=true) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ calls state basis) : call.bind point=point := by
  obtain ⟨row,present,found⟩ := List.mem_filterMap.mp member
  exact instruction_fixes row call found point ((holds_iff _ _).mp (rows_holds state basis valid point accepted) row present)

theorem calls_free (state : ArenaSource.State) (basis : List Row) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ calls state basis) : Free call.address call.body.code := by
  obtain ⟨row,present,found⟩ := List.mem_filterMap.mp member
  exact instruction_free row (rows_nodup state basis row present) call found



theorem calls_present_size (state : ArenaSource.State) (basis : List Row) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ calls state basis) :
    call.address ∈ FunctionalSubstitution.inputs state.arena.code ∧
      call.body.code.size ≤ 2*(FunctionalSubstitution.inputs state.arena.code).length+1 := by
  obtain ⟨row,present,found⟩ := List.mem_filterMap.mp member
  have support := rows_present state basis row present
  have size := rows_length state basis row present
  cases row with
  | mk vars rhs =>
      cases vars with
      | nil => cases found
      | cons address rest =>
          simp only [instruction,Option.some.injEq] at found
          subst call
          refine ⟨support address (by simp),?_⟩
          simp only [Gates.compileRow_size]
          change rest.length+1 ≤ (FunctionalSubstitution.inputs state.arena.code).length at size
          omega

def generate (state : ArenaSource.State) : List FunctionalSubstitution.Instruction :=
  if JointCircuit.noAdd state.arena.code then
    match (JointCircuitCost.analyzed state).value with
    | .contradiction => []
    | .basis basis => calls state basis
  else []

theorem generate_fixes (state : ArenaSource.State) (point : Nat → Bool) (accepted : JointCircuit.read state point=true)
    (call : FunctionalSubstitution.Instruction) (member : call ∈ generate state) : call.bind point=point := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases source : (JointCircuitCost.analyzed state).value with
    | contradiction => simp [generate,checked,source] at member
    | basis basis =>
        have valid := JointCircuitCost.analyzed_valid state
        have held := JointCircuit.generated_holds state checked point accepted
        rw [← JointCircuit.analyzed_value,← JointCircuitCost.analyzed_value,source] at held
        exact calls_fixes state basis (by simpa only [source,Result.triangular,Result.within] using valid)
          point held call (by simpa only [generate,checked,if_true,source] using member)
  · simp [generate,checked] at member

theorem generate_free (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ generate state) : Free call.address call.body.code := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases source : (JointCircuitCost.analyzed state).value with
    | contradiction => simp [generate,checked,source] at member
    | basis basis => exact calls_free state basis call (by simpa only [generate,checked,if_true,source] using member)
  · simp [generate,checked] at member

theorem generate_present_size (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ generate state) :
    call.address ∈ FunctionalSubstitution.inputs state.arena.code ∧
      call.body.code.size ≤ 2*(FunctionalSubstitution.inputs state.arena.code).length+1 := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases source : (JointCircuitCost.analyzed state).value with
    | contradiction => simp [generate,checked,source] at member
    | basis basis => exact calls_present_size state basis call (by simpa only [generate,checked,if_true,source] using member)
  · simp [generate,checked] at member



theorem calls_inputs (state : ArenaSource.State) (basis : List Row) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ calls state basis) :
    FunctionalSubstitution.inputs call.body.code ⊆ FunctionalSubstitution.inputs state.arena.code := by
  obtain ⟨row,present,found⟩ := List.mem_filterMap.mp member
  have support := rows_present state basis row present
  cases row with
  | mk vars rhs =>
      cases vars with
      | nil => cases found
      | cons address rest =>
          simp only [instruction,Option.some.injEq] at found
          subst call
          intro i member
          by_contra absent
          have free := row_free i ⟨rest,rhs⟩ (by intro hit; exact absent (support i (by simp [hit])))
          exact FunctionalSubstitution.inputs_free _ i free member

theorem generate_inputs (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction)
    (member : call ∈ generate state) :
    FunctionalSubstitution.inputs call.body.code ⊆ FunctionalSubstitution.inputs state.arena.code := by
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases source : (JointCircuitCost.analyzed state).value with
    | contradiction => simp [generate,checked,source] at member
    | basis basis => exact calls_inputs state basis call (by simpa only [generate,checked,if_true,source] using member)
  · simp [generate,checked] at member


end SaturationMonoid.ComplexityProjection.SATSource.JointInputRelations
