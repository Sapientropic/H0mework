import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Boolean
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.IntegerMachine

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.BooleanValues

open InterferenceProgram

def Small (value : ℤ) : Prop := value = -1 ∨ value = 0 ∨ value = 1

theorem small_zero : Small 0 := Or.inr (Or.inl rfl)
theorem small_one : Small 1 := Or.inr (Or.inr rfl)
theorem small_negOne : Small (-1) := Or.inl rfl

theorem small_bit (value : Bool) : Small (bit value) := by
  cases value <;> simp [bit, Small]

theorem small_sign (value : ℤ) : Small (sign value) := by
  unfold sign
  split
  · exact small_one
  · exact small_negOne

theorem small_mul {left right : ℤ} (a : Small left) (b : Small right) : Small (left * right) := by
  rcases a with rfl | rfl | rfl <;> rcases b with rfl | rfl | rfl <;> norm_num [Small]

theorem small_neg {value : ℤ} (bounded : Small value) : Small (-value) := by
  rcases bounded with rfl | rfl | rfl <;> norm_num [Small]

def Values (values : Array ℤ) : Prop := ∀ i, Small (values.getD i 0)

def NodeSmall : Node → Prop
  | .constant value => Small value
  | .add _ _ => False
  | _ => True

def Code (code : Array Node) : Prop := ∀ node ∈ code.toList, NodeSmall node

theorem values_empty : Values #[] := by simp [Values, Array.getD, Small]

theorem values_push (values : Array ℤ) (bounded : Values values) (value : ℤ) (added : Small value) :
    Values (values.push value) := by
  intro i
  rw [getD_push_any]
  split
  · exact added
  · exact bounded i

theorem node_run (node : Node) (allowed : NodeSmall node) (environment : Nat → Bool)
    (values : Array ℤ) (bounded : Values values) : Small (node.run environment values) := by
  cases node with
  | constant value => exact allowed
  | input i => exact small_bit _
  | add a b => exact False.elim allowed
  | mul a b => exact small_mul (bounded a) (bounded b)
  | neg a => exact small_neg (bounded a)
  | band a b => exact small_bit _
  | bxor a b => exact small_bit _
  | bnot a => exact small_bit _
  | phase a => exact small_sign _
  | select c a b =>
      simp only [Node.run]
      split
      · exact bounded a
      · exact bounded b

theorem runCode_values (environment : Nat → Bool) (values : Array ℤ) (bounded : Values values)
    (code : List Node) (allowed : ∀ node ∈ code, NodeSmall node) :
    Values (runCode environment values code) := by
  induction code generalizing values with
  | nil => exact bounded
  | cons node rest ih =>
      apply ih _ (values_push values bounded _ (node_run node (allowed node (by simp)) environment values bounded))
      exact fun other member => allowed other (by simp [member])

theorem run_values (environment : Nat → Bool) (code : Array Node) (allowed : Code code) :
    Values (run environment code) := runCode_values environment #[] values_empty code.toList allowed

theorem code_empty : Code #[] := by simp [Code]

theorem code_singleton (node : Node) (allowed : NodeSmall node) : Code #[node] := by
  simpa [Code] using allowed

theorem code_push (code : Array Node) (allowed : Code code) (node : Node) (added : NodeSmall node) :
    Code (code.push node) := by
  intro other member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact allowed other member
  · exact added

theorem code_append (left right : Array Node) (a : Code left) (b : Code right) : Code (left ++ right) := by
  intro node member
  simp only [Array.toList_append, List.mem_append] at member
  exact member.elim (a node) (b node)

theorem code_map (code : Array Node) (allowed : Code code) (transform : Node → Node)
    (preserves : ∀ node, NodeSmall node → NodeSmall (transform node)) : Code (code.map transform) := by
  intro node member
  simp only [Array.toList_map, List.mem_map] at member
  obtain ⟨original, hit, rfl⟩ := member
  exact preserves original (allowed original hit)

theorem node_shift (node : Node) (allowed : NodeSmall node) (offset : Nat) :
    NodeSmall (node.shift offset) := by cases node <;> exact allowed

theorem node_mapRefs (node : Node) (allowed : NodeSmall node) (rename : Nat → Nat) :
    NodeSmall (node.mapRefs rename) := by cases node <;> exact allowed

theorem node_cofactor (node : Node) (allowed : NodeSmall node) (i : Nat) (value : Bool) :
    NodeSmall (node.cofactor i value) := by
  cases node <;> try exact allowed
  simp only [Node.cofactor]
  split
  · exact small_bit value
  · trivial

theorem fragment_constant (value : ℤ) (bounded : Small value) : Code (Fragment.constant value).code :=
  code_singleton _ bounded

theorem fragment_input (i : Nat) : Code (Fragment.input i).code := code_singleton _ trivial

theorem fragment_unary (fragment : Fragment) (allowed : Code fragment.code) (node : Nat → Node)
    (added : NodeSmall (node fragment.output.val)) : Code (fragment.unary node).code :=
  code_push fragment.code allowed _ added

theorem fragment_binary (left right : Fragment) (a : Code left.code) (b : Code right.code)
    (node : Nat → Nat → Node) (added : NodeSmall (node left.output.val (left.code.size + right.output.val))) :
    Code (left.binary right node).code :=
  code_push _ (code_append _ _ a (code_map right.code b _ (fun item hit => node_shift item hit left.code.size))) _ added

theorem fragment_not (fragment : Fragment) (allowed : Code fragment.code) : Code fragment.not.code :=
  fragment_unary fragment allowed _ trivial

theorem fragment_and (left right : Fragment) (a : Code left.code) (b : Code right.code) :
    Code (left.and right).code := fragment_binary left right a b _ trivial

theorem fragment_xor (left right : Fragment) (a : Code left.code) (b : Code right.code) :
    Code (left.xor right).code := fragment_binary left right a b _ trivial

theorem compile_literal {n : Nat} (literal : CNFLiteral n) : Code (compileLiteral literal).code := by
  unfold compileLiteral
  split
  · exact fragment_not _ (fragment_input _)
  · exact fragment_input _

theorem compile_clause {n : Nat} (clause : CNFClause n) : Code (compileClause clause).code := by
  induction clause with
  | nil => exact fragment_constant 1 small_one
  | cons literal rest ih => exact fragment_and _ _ (compile_literal literal) ih

theorem original {n : Nat} (formula : CNFFormula n) : Code (Affine.Acceptance.original formula).code := by
  induction formula with
  | nil => exact fragment_constant 1 small_one
  | cons clause rest ih => exact fragment_and _ _ (fragment_not _ (compile_clause clause)) ih

theorem compile_terms (terms : List Nat) (initial : Fragment) (allowed : Code initial.code) :
    Code (Affine.Gates.compileTerms terms initial).code := by
  induction terms generalizing initial with
  | nil => exact allowed
  | cons i rest ih => exact ih _ (fragment_xor _ _ allowed (fragment_input i))

theorem compile_row (row : Affine.Row) : Code (Affine.Gates.compileRow row).code :=
  compile_terms _ _ (fragment_constant _ (small_bit row.rhs))

theorem compile_rows (rows : List Affine.Row) : Code (Affine.Gates.compileRows rows).code := by
  induction rows with
  | nil => exact code_singleton _ small_zero
  | cons row rest ih =>
      exact code_append _ _ ih (code_map _ (compile_row row) _ (fun node hit => node_shift node hit _))

theorem node_rewrite (node : Node) (allowed : NodeSmall node) (n width size : Nat) (outputs : List Nat) :
    NodeSmall (Affine.Gates.rewriteNode n width size outputs node) := by
  cases node <;> try exact allowed
  simp only [Affine.Gates.rewriteNode]
  split <;> trivial

theorem fromAmplitude (fragment : Fragment) (allowed : Code fragment.code) :
    Code (InterferenceDecision.fromAmplitude fragment).code := code_push _ allowed _ small_zero

theorem amplitude (program : Program) (allowed : Code program.code) :
    Code (InterferenceDecision.amplitude program).code :=
  code_push _ (code_push program.code allowed (.phase program.phase.val) trivial)
    (.mul program.weight.val program.code.size) trivial

theorem cofactor (program : Program) (allowed : Code program.code) (i : Nat) (value : Bool) :
    Code (program.cofactor i value).code :=
  code_map _ allowed _ (fun node hit => node_cofactor node hit i value)

theorem acceptance {n : Nat} (coordinates : Array Affine.Row) (formula : CNFFormula n) :
    Code (Affine.Acceptance.compile coordinates formula).code :=
  code_append _ _ (compile_rows _) (code_map _ (fromAmplitude _ (original formula)) _
    (fun node hit => node_rewrite node hit n 0 _ _))

theorem foldNode (state : Reduce.State) (valid : Reduce.Valid state) (code : Code state.code)
    (node : Node) (allowed : NodeSmall node) : NodeSmall (Reduce.foldNode state node) := by
  have bounded := node_run node allowed (fun _ => false) (run (fun _ => false) state.code)
    (run_values (fun _ => false) state.code code)
  unfold Reduce.foldNode
  split
  · rename_i value found
    have same := Reduce.constantValue_sound _ _ (Reduce.known_sound state valid (fun _ => false))
      (fun _ => false) node value found
    exact same ▸ bounded
  · exact allowed

theorem intern (state : Reduce.State) (code : Code state.code) (node : Node) (allowed : NodeSmall node) :
    Code (Reduce.intern state node).1.code := by
  unfold Reduce.intern
  split
  · exact code
  · exact code_push _ code _ allowed

theorem smartEmit (frame : Reduce.Frame) (valid : Reduce.Valid frame.state) (code : Code frame.state.code)
    (node : Node) (allowed : NodeSmall node) : Code (Reduce.smartEmit frame node).state.code :=
  intern _ code _ (foldNode _ valid code _ (node_mapRefs node allowed _))

theorem smartFold (frame : Reduce.Frame) (environment : Nat → Bool) (values : Array ℤ)
    (represents : Reduce.Represents frame environment values) (code : Code frame.state.code)
    (nodes : List Node) (allowed : ∀ node ∈ nodes, NodeSmall node) :
    Code (Reduce.smartFold frame nodes).state.code := by
  induction nodes generalizing frame values with
  | nil => exact code
  | cons node rest ih =>
      exact ih _ _ (Reduce.smartEmit_represents frame environment values represents node)
        (smartEmit frame represents.1 code node (allowed node (by simp)))
        (fun other member => allowed other (by simp [member]))

theorem share (program : Program) (allowed : Code program.code) : Code program.share.code :=
  smartFold Reduce.first (fun _ => false) #[] (Reduce.first_represents _) (code_singleton _ small_zero)
    program.code.toList allowed

theorem cone_emit (needed : List Nat) (frame : Cone.Frame) (code : Code frame.code)
    (node : Node) (allowed : NodeSmall node) : Code (Cone.emit needed frame node).code := by
  unfold Cone.emit
  split
  · exact code_push _ code _ (node_mapRefs node allowed _)
  · exact code

theorem cone_fold (needed : List Nat) (frame : Cone.Frame) (code : Code frame.code)
    (nodes : List Node) (allowed : ∀ node ∈ nodes, NodeSmall node) :
    Code (Cone.fold needed frame nodes).code := by
  induction nodes generalizing frame with
  | nil => exact code
  | cons node rest ih =>
      exact ih _ (cone_emit needed frame code node (allowed node (by simp)))
        (fun other member => allowed other (by simp [member]))

theorem pruneCone (program : Program) (allowed : Code program.code) : Code (Cone.pruneCone program).code :=
  cone_fold _ Cone.empty code_empty program.share.code.toList (share program allowed)

theorem boolean_constant (value : Bool) : Code (Affine.Boolean.constant value).code :=
  fromAmplitude _ (fragment_constant _ (small_bit value))

theorem existential (program : Program) (allowed : Code program.code) (i : Nat) :
    Code (Affine.Boolean.existential program i).code :=
  fromAmplitude _ (fragment_not _ (fragment_and _ _
    (fragment_not _ (amplitude _ (cofactor program allowed i false)))
    (fragment_not _ (amplitude _ (cofactor program allowed i true)))))

theorem boolean_fold (indices : List Nat) (program : Program) (allowed : Code program.code) :
    Code (Affine.Boolean.fold indices program).code := by
  induction indices with
  | nil => exact allowed
  | cons i rest ih =>
      simp only [Affine.Boolean.fold]
      split
      · exact boolean_constant _
      · exact pruneCone _ (existential _ (share _ ih) i)

theorem close {n : Nat} (width : Nat) (coordinates : Array Affine.Row) (formula : CNFFormula n) :
    Code (Affine.Boolean.close width coordinates formula).code :=
  boolean_fold _ _ (pruneCone _ (acceptance coordinates formula))

theorem close_values {n : Nat} (width : Nat) (coordinates : Array Affine.Row) (formula : CNFFormula n)
    (environment : Nat → Bool) :
    Values (run environment (Affine.Boolean.close width coordinates formula).code) :=
  run_values _ _ (close width coordinates formula)

/-- The existing signed binary format encodes every generated scalar with two bits. -/
def scalarWord (value : ℤ) : List Bool := [decide (value < 0), truth value]

theorem scalarWord_length (value : ℤ) : (scalarWord value).length = 2 := rfl

theorem scalarWord_value (value : ℤ) (bounded : Small value) :
    IntegerMachine.wordValue (scalarWord value) = some value := by
  rcases bounded with rfl | rfl | rfl <;> decide

theorem close_scalar_word {n : Nat} (width : Nat) (coordinates : Array Affine.Row) (formula : CNFFormula n)
    (environment : Nat → Bool) (i : Nat) :
    IntegerMachine.wordValue (scalarWord
      ((run environment (Affine.Boolean.close width coordinates formula).code).getD i 0)) =
      some ((run environment (Affine.Boolean.close width coordinates formula).code).getD i 0) :=
  scalarWord_value _ (close_values width coordinates formula environment i)

end SaturationMonoid.ComplexityProjection.SATSource.BooleanValues
