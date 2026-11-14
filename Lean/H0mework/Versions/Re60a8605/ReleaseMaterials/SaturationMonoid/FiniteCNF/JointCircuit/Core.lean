import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Gates

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointCircuit
open InterferenceProgram

def node (state : ArenaSource.State) (i : Fin state.arena.code.size) : Node := state.arena.code[i]

def slot (state : ArenaSource.State) (i : Nat) : Fin state.arena.code.size :=
  if inside : i < state.arena.code.size then ⟨i,inside⟩ else state.program.weight

theorem slot_val (state : ArenaSource.State) (i : Nat) (inside : i < state.arena.code.size) : (slot state i).val=i := by
  simp [slot,inside]

def gates (state : ArenaSource.State) : CNFFormula state.arena.code.size :=
  (List.finRange state.arena.code.size).flatMap (fun i => gate i (slot state) (node state i))

def sameInput (state : ArenaSource.State) (i j : Fin state.arena.code.size) : Bool :=
  match node state i,node state j with
  | .input a,.input b => a==b
  | _,_ => false

def aliases (state : ArenaSource.State) : CNFFormula state.arena.code.size :=
  (List.finRange state.arena.code.size).flatMap (fun i =>
    (List.finRange state.arena.code.size).flatMap (fun j => if sameInput state i j then equal i j else []))

def relations (state : ArenaSource.State) : CNFFormula state.arena.code.size :=
  state.relations.flatMap (fun item => equal item.relation.left item.relation.right)

def formula (state : ArenaSource.State) : CNFFormula state.arena.code.size :=
  gates state++aliases state++relations state++unit state.program.weight true

def lift (state : ArenaSource.State) (environment : Nat → Bool) : Nat → Bool :=
  fun i => truth ((run environment state.arena.code).getD i 0)

def read (state : ArenaSource.State) (environment : Nat → Bool) : Bool :=
  truth (state.program.program.eval environment) && ArenaSource.readRelations state environment

theorem flatMap_eval {α : Type} {n : Nat} (items : List α) (block : α → CNFFormula n) (point : Nat → Bool) :
    CNFFormula.eval (items.flatMap block) point=items.all (fun item => CNFFormula.eval (block item) point) := by
  simp only [CNFFormula.eval,List.all_flatMap]

theorem append_eval {n : Nat} (left right : CNFFormula n) (point : Nat → Bool) :
    CNFFormula.eval (left++right) point=(CNFFormula.eval left point && CNFFormula.eval right point) := by
  simp only [CNFFormula.eval,List.all_append]

theorem equation_congr (value : Bool) (node : Node) (left right : Nat → Bool)
    (same : ∀ i ∈ node.refs, left i=right i) : equation left value node=equation right value node := by
  cases node <;> simp_all [equation,Node.refs]

theorem allowed_node (state : ArenaSource.State) (checked : noAdd state.arena.code=true) (i : Fin state.arena.code.size) :
    allowed (node state i)=true :=
  List.all_eq_true.mp checked (node state i) (by simp [node])

theorem node_read (state : ArenaSource.State) (environment : Nat → Bool) (i : Fin state.arena.code.size) :
    (run environment state.arena.code).getD i.val 0=(node state i).run environment (run environment state.arena.code) := by
  have law := ArenaAction.run_equation state.arena.code state.arena.forward environment i.val i.isLt
  simpa [Array.getD,i.isLt,node] using law

theorem gates_lift (state : ArenaSource.State) (checked : noAdd state.arena.code=true) (environment : Nat → Bool) :
    CNFFormula.eval (gates state) (lift state environment)=true := by
  rw [gates,flatMap_eval]
  apply List.all_eq_true.mpr
  intro i member
  rw [gate_eval]
  have source := equation_run (node state i) (allowed_node state checked i) environment (run environment state.arena.code)
  rw [← node_read state environment i] at source
  change equation (fun j => lift state environment j) (lift state environment i.val) (node state i)=true at source
  rw [equation_congr (lift state environment i.val) (node state i)
    (fun j => lift state environment (slot state j).val) (lift state environment) ?_]
  · exact source
  · intro j present
    have before : j < i.val := state.arena.forward i.val i.isLt j present
    rw [slot_val state j (before.trans i.isLt)]

theorem sameInput_lift (state : ArenaSource.State) (i j : Fin state.arena.code.size)
    (same : sameInput state i j=true) (environment : Nat → Bool) : lift state environment i.val=lift state environment j.val := by
  unfold sameInput at same
  cases first : node state i <;> cases second : node state j <;> simp only [first,second,Bool.false_eq_true] at same
  rename_i a b
  have identical := beq_iff_eq.mp same
  simp only [lift,node_read,first,second,Node.run,truth_bit,identical]

theorem aliases_lift (state : ArenaSource.State) (environment : Nat → Bool) :
    CNFFormula.eval (aliases state) (lift state environment)=true := by
  rw [aliases,flatMap_eval]
  apply List.all_eq_true.mpr
  intro i member
  rw [flatMap_eval]
  apply List.all_eq_true.mpr
  intro j present
  split
  · rename_i same
    rw [equal_eval,Bool.xor_false,sameInput_lift state i j same environment]
    simp
  · rfl

theorem relations_lift (state : ArenaSource.State) (environment : Nat → Bool) :
    CNFFormula.eval (relations state) (lift state environment)=ArenaSource.readRelations state environment := by
  rw [relations,flatMap_eval]
  simp only [equal_eval,Bool.xor_false,ArenaSource.readRelations,ArenaAction.Relation.read,lift]

theorem formula_lift (state : ArenaSource.State) (checked : noAdd state.arena.code=true) (environment : Nat → Bool) :
    CNFFormula.eval (formula state) (lift state environment)=read state environment := by
  rw [formula,append_eval,append_eval,append_eval,gates_lift state checked,aliases_lift,
    relations_lift,unit_eval]
  simp only [Bool.true_and,read,truth_program,lift,ArenaAction.View.program]
  cases ArenaSource.readRelations state environment <;>
    cases truth ((run environment state.arena.code).getD state.program.weight.val 0) <;> rfl

theorem gates_reads (state : ArenaSource.State) (point : Nat → Bool)
    (accepted : CNFFormula.eval (gates state) point=true) (i : Fin state.arena.code.size) :
    equation (fun j => point (slot state j).val) (point i.val) (node state i)=true := by
  rw [gates,flatMap_eval] at accepted
  exact gate_eval i (slot state) (node state i) point ▸
    List.all_eq_true.mp accepted i (List.mem_finRange i)

theorem aliases_reads (state : ArenaSource.State) (point : Nat → Bool)
    (accepted : CNFFormula.eval (aliases state) point=true) (i j : Fin state.arena.code.size)
    (same : sameInput state i j=true) : point i.val=point j.val := by
  rw [aliases,flatMap_eval] at accepted
  have first := List.all_eq_true.mp accepted i (List.mem_finRange i)
  rw [flatMap_eval] at first
  have second := List.all_eq_true.mp first j (List.mem_finRange j)
  rw [if_pos same,equal_eval,Bool.xor_false] at second
  exact beq_iff_eq.mp second

def inputIndex (state : ArenaSource.State) (address : Nat) : Option (Fin state.arena.code.size) :=
  (List.finRange state.arena.code.size).find? (fun i => decide (node state i=.input address))

def project (state : ArenaSource.State) (point : Nat → Bool) (address : Nat) : Bool :=
  match inputIndex state address with | none => false | some i => point i.val

theorem project_input (state : ArenaSource.State) (point : Nat → Bool)
    (accepted : CNFFormula.eval (aliases state) point=true) (i : Fin state.arena.code.size)
    (address : Nat) (original : node state i=.input address) : point i.val=project state point address := by
  cases found : inputIndex state address with
  | none =>
      have missing := List.find?_eq_none.mp found
      have absent := missing i (List.mem_finRange i)
      simp [original] at absent
  | some j =>
      have actual : (List.finRange state.arena.code.size).find? (fun i => decide (node state i=.input address))=some j := found
      have truth := List.find?_some actual
      have stored : node state j=.input address := of_decide_eq_true truth
      exact (aliases_reads state point accepted i j (by simp [sameInput,original,stored])).trans (by simp [project,found])

theorem equation_unique (node : Node) (read : Nat → Bool) (left right : Bool)
    (a : equation read left node=true) (b : equation read right node=true)
    (input : ∀ address, node=.input address → left=right) : left=right := by
  cases node with
  | input address => exact input address rfl
  | add x y => cases a
  | constant z | mul x y | neg x | band x y | bxor x y | bnot x | phase x | select x y z =>
      simp only [equation,beq_iff_eq] at a b
      exact a.trans b.symm

theorem recover_gates (state : ArenaSource.State) (checked : noAdd state.arena.code=true) (point : Nat → Bool)
    (accepted : CNFFormula.eval (gates state) point=true) (aliased : CNFFormula.eval (aliases state) point=true) :
    ∀ i, i < state.arena.code.size → point i=lift state (project state point) i := by
  intro index
  induction index using Nat.strong_induction_on with
  | h index earlier =>
      intro inside
      let i : Fin state.arena.code.size := ⟨index,inside⟩
      have original := gates_reads state point accepted i
      have generated := equation_run (node state i) (allowed_node state checked i)
        (project state point) (run (project state point) state.arena.code)
      rw [← node_read state (project state point) i] at generated
      have same : ∀ j ∈ (node state i).refs, lift state (project state point) j=point (slot state j).val := by
        intro j present
        have before : j < index := state.arena.forward index inside j present
        rw [slot_val state j (before.trans inside)]
        exact (earlier j before (before.trans inside)).symm
      change equation (lift state (project state point)) (lift state (project state point) i.val) (node state i)=true at generated
      rw [equation_congr _ _ _ _ same] at generated
      apply equation_unique (node state i) (fun j => point (slot state j).val) _ _ original generated
      intro address source
      change point i.val=truth ((run (project state point) state.arena.code).getD i.val 0)
      rw [node_read,source]
      simp only [Node.run,truth_bit]
      exact project_input state point aliased i address source

theorem finite_eval_congr {n : Nat} (formula : CNFFormula n) (left right : Nat → Bool)
    (same : ∀ i, i < n → left i=right i) : CNFFormula.eval formula left=CNFFormula.eval formula right := by
  unfold CNFFormula.eval
  apply List.all_congr rfl
  intro clause
  unfold CNFClause.eval
  apply List.any_congr rfl
  intro literal
  simp only [CNFLiteral.eval,same literal.var.val literal.var.isLt]

theorem formula_project (state : ArenaSource.State) (checked : noAdd state.arena.code=true) (point : Nat → Bool)
    (accepted : CNFFormula.eval (formula state) point=true) : read state (project state point)=true := by
  have parts := accepted
  simp only [formula,append_eval,Bool.and_eq_true] at parts
  have recovered := recover_gates state checked point parts.1.1.1 parts.1.1.2
  rw [← formula_lift state checked]
  exact (finite_eval_congr (formula state) point (lift state (project state point)) recovered).symm.trans accepted

theorem formula_satisfiable (state : ArenaSource.State) (checked : noAdd state.arena.code=true) :
    CNFSatisfiable (formula state) ↔ ∃ environment, read state environment=true := by
  constructor
  · rintro ⟨point,accepted⟩
    exact ⟨project state point,formula_project state checked point accepted⟩
  · rintro ⟨environment,accepted⟩
    exact ⟨lift state environment,(formula_lift state checked environment).trans accepted⟩

theorem flatMap_length {α β : Type} (source : List α) (block : α → List β) (size : Nat)
    (bounded : ∀ item, (block item).length ≤ size) : (source.flatMap block).length ≤ source.length*size := by
  induction source with
  | nil => simp
  | cons item rest ih =>
      have first := bounded item
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith

theorem gates_length (state : ArenaSource.State) : (gates state).length ≤ 4*state.arena.code.size := by
  have size := flatMap_length (List.finRange state.arena.code.size) (fun i => gate i (slot state) (node state i)) 4
    (fun i => gate_length i (slot state) (node state i))
  simpa only [gates,List.length_finRange,Nat.mul_comm] using size

theorem aliases_length (state : ArenaSource.State) : (aliases state).length ≤ 3*state.arena.code.size*state.arena.code.size := by
  have each : ∀ i : Fin state.arena.code.size,
      ((List.finRange state.arena.code.size).flatMap (fun j => if sameInput state i j then equal i j else [])).length ≤
        state.arena.code.size*3 := by
    intro i
    simpa only [List.length_finRange] using flatMap_length (List.finRange state.arena.code.size)
      (fun j => if sameInput state i j then equal i j else []) 3 (by
        intro j
        split <;> simp [equal,FunctionalRelations.Relation.block])
  have total := flatMap_length (List.finRange state.arena.code.size) _ (state.arena.code.size*3) each
  simp only [List.length_finRange] at total
  change (aliases state).length ≤ _ at total
  nlinarith

theorem relations_length (state : ArenaSource.State) : (relations state).length ≤ 3*state.relations.length := by
  have size := flatMap_length state.relations (fun item => equal item.relation.left item.relation.right) 3
    (by intro item; simp [equal,FunctionalRelations.Relation.block])
  simpa only [relations,Nat.mul_comm] using size

theorem formula_length (state : ArenaSource.State) :
    (formula state).length ≤ 4*state.arena.code.size+3*state.arena.code.size*state.arena.code.size+3*state.relations.length+1 := by
  have a := gates_length state
  have b := aliases_length state
  have c := relations_length state
  simp only [formula,List.length_append,unit,List.length_cons,List.length_nil]
  omega

/-- The original gate occurrence and all relation roots feed the paid joint
iteration directly. An `add` node is handled by the caller's existing reader. -/
def feedback (state : ArenaSource.State) : Option (CapacityMatching.SourceCost.Counted Affine.Result) :=
  if noAdd state.arena.code then
    some (AffineRelationExtractionCost.iterate (formula state) (state.arena.code.size+1) (.basis []))
  else none

theorem feedback_value (state : ArenaSource.State) (checked : noAdd state.arena.code=true) :
    (feedback state).map (·.value)=some (Affine.JointFeedback.generate (formula state) []) := by
  simp only [feedback,checked,if_true,Option.map_some,AffineRelationExtractionCost.iterate_value,Affine.JointFeedback.generate]
  rfl

theorem generated_holds (state : ArenaSource.State) (checked : noAdd state.arena.code=true)
    (environment : Nat → Bool) (accepted : read state environment=true) :
    (Affine.JointFeedback.generate (formula state) []).holds (lift state environment)=true := by
  have source := Affine.JointFeedback.generate_holds (formula state) [] (lift state environment)
  rw [formula_lift state checked environment,accepted] at source
  simpa [Affine.holds] using source

end SaturationMonoid.ComplexityProjection.SATSource.JointCircuit
