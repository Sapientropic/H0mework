import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Source
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ParityBlock

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointCircuit
open InterferenceProgram

def positive {n : Nat} (i : Fin n) : CNFLiteral n := ⟨i,true⟩

def unit {n : Nat} (output : Fin n) (value : Bool) : CNFFormula n := [[⟨output,value⟩]]

theorem unit_eval {n : Nat} (output : Fin n) (value : Bool) (point : Nat → Bool) :
    CNFFormula.eval (unit output value) point=(point output.val==value) := by
  cases value <;> cases h : point output.val <;> simp [unit,CNFFormula.eval,CNFClause.eval,CNFLiteral.eval,h]

def equal {n : Nat} (output input : Fin n) (negate : Bool := false) : CNFFormula n :=
  (FunctionalRelations.Relation.mk (positive output) ⟨input,!negate⟩ ⟨input,!negate⟩).block

theorem equal_eval {n : Nat} (output input : Fin n) (negate : Bool) (point : Nat → Bool) :
    CNFFormula.eval (equal output input negate) point=(point output.val==(point input.val ^^ negate)) := by
  rw [equal,FunctionalRelations.Relation.block_eval]
  simp only [FunctionalRelations.Relation.holds,positive,CNFLiteral.eval]
  cases negate <;> cases point input.val <;> cases point output.val <;> rfl

def andGate {n : Nat} (output left right : Fin n) : CNFFormula n :=
  (FunctionalRelations.Relation.mk (positive output) (positive left) (positive right)).block

theorem andGate_eval {n : Nat} (output left right : Fin n) (point : Nat → Bool) :
    CNFFormula.eval (andGate output left right) point=(point output.val==(point left.val && point right.val)) := by
  rw [andGate,FunctionalRelations.Relation.block_eval]
  rfl

def xorGate {n : Nat} (output left right : Fin n) : CNFFormula n :=
  CouncilParityProbe.relationBlock (positive output) (positive left) (positive right) false

theorem xorGate_eval {n : Nat} (output left right : Fin n) (point : Nat → Bool) :
    CNFFormula.eval (xorGate output left right) point=(point output.val==(point left.val ^^ point right.val)) := by
  apply Bool.eq_iff_iff.mpr
  rw [xorGate,CouncilParityProbe.relationBlock_eval]
  simp only [positive,CNFLiteral.eval,beq_iff_eq]
  cases point output.val <;> cases point left.val <;> cases point right.val <;> decide

def selectGate {n : Nat} (output condition left right : Fin n) : CNFFormula n :=
  [[positive condition,⟨left,false⟩,positive output],
   [positive condition,positive left,⟨output,false⟩],
   [⟨condition,false⟩,⟨right,false⟩,positive output],
   [⟨condition,false⟩,positive right,⟨output,false⟩]]

theorem selectGate_eval {n : Nat} (output condition left right : Fin n) (point : Nat → Bool) :
    CNFFormula.eval (selectGate output condition left right) point=
      (point output.val==(if point condition.val then point right.val else point left.val)) := by
  cases o : point output.val <;> cases c : point condition.val <;> cases a : point left.val <;> cases b : point right.val <;>
    simp [selectGate,positive,CNFFormula.eval,CNFClause.eval,CNFLiteral.eval,o,c,a,b]

def allowed : Node → Bool | .add _ _ => false | _ => true
def noAdd (code : Array Node) : Bool := code.toList.all allowed

def equation (read : Nat → Bool) (output : Bool) : Node → Bool
  | .constant z => output==truth z
  | .input _ => true
  | .add _ _ => false
  | .mul a b | .band a b => output==(read a && read b)
  | .neg a => output==read a
  | .bxor a b => output==(read a ^^ read b)
  | .bnot a => output==(!read a)
  | .phase _ => output==true
  | .select c a b => output==(if read c then read b else read a)

def gate {n : Nat} (output : Fin n) (ref : Nat → Fin n) : Node → CNFFormula n
  | .constant z => unit output (truth z)
  | .input _ => []
  | .add _ _ => [[]]
  | .mul a b | .band a b => andGate output (ref a) (ref b)
  | .neg a => equal output (ref a)
  | .bxor a b => xorGate output (ref a) (ref b)
  | .bnot a => equal output (ref a) true
  | .phase _ => unit output true
  | .select c a b => selectGate output (ref c) (ref a) (ref b)

theorem gate_eval {n : Nat} (output : Fin n) (ref : Nat → Fin n) (node : Node) (point : Nat → Bool) :
    CNFFormula.eval (gate output ref node) point=equation (fun i => point (ref i).val) (point output.val) node := by
  cases node <;> simp only [gate,equation,unit_eval,equal_eval,andGate_eval,xorGate_eval,selectGate_eval,Bool.xor_false,Bool.xor_true] <;> rfl

theorem truth_mul (left right : ℤ) : truth (left*right)=(truth left && truth right) := by
  apply Bool.eq_iff_iff.mpr
  simp [truth]

theorem truth_neg (value : ℤ) : truth (-value)=truth value := by
  apply Bool.eq_iff_iff.mpr
  simp [truth]

theorem truth_sign (value : ℤ) : truth (sign value)=true := by unfold sign; split <;> decide

theorem equation_run (node : Node) (accepted : allowed node=true) (environment : Nat → Bool) (values : Array ℤ) :
    equation (fun i => truth (values.getD i 0)) (truth (node.run environment values)) node=true := by
  cases node with
  | input i => rfl
  | add a b => cases accepted
  | constant z => simp [equation,Node.run]
  | mul a b => simp [equation,Node.run,truth_mul]
  | neg a => simp [equation,Node.run,truth_neg]
  | band a b => simp [equation,Node.run,truth_bit]
  | bxor a b => simp [equation,Node.run,truth_bit]
  | bnot a => simp [equation,Node.run,truth_bit]
  | phase a => simp [equation,Node.run,truth_sign]
  | select c a b =>
      by_cases zero : values.getD c 0=0
      · have flag : truth (values.getD c 0)=false := by simp [truth,zero]
        simp only [equation,Node.run,if_pos zero,flag,Bool.false_eq_true,if_false,beq_self_eq_true]
      · have flag : truth (values.getD c 0)=true := by exact bne_iff_ne.mpr zero
        simp only [equation,Node.run,if_neg zero,flag,if_true,beq_self_eq_true]

theorem truth_program (program : Program) (environment : Nat → Bool) :
    truth (program.eval environment)=truth ((run environment program.code).getD program.weight.val 0) := by
  rw [Program.eval,truth_mul,truth_sign,Bool.and_true]

theorem gate_length {n : Nat} (output : Fin n) (ref : Nat → Fin n) (node : Node) :
    (gate output ref node).length ≤ 4 := by
  cases node <;> simp [gate,unit,equal,andGate,xorGate,selectGate,FunctionalRelations.Relation.block,
    CouncilParityProbe.relationBlock,CouncilParityProbe.parityBlock]

theorem gate_clause {n : Nat} (output : Fin n) (ref : Nat → Fin n) (node : Node)
    (clause : CNFClause n) (member : clause ∈ gate output ref node) : clause.length ≤ 3 := by
  cases node <;> simp only [gate,unit,equal,andGate,xorGate,selectGate,FunctionalRelations.Relation.block,
    CouncilParityProbe.relationBlock,CouncilParityProbe.parityBlock] at member
  all_goals simp_all
  all_goals aesop

end SaturationMonoid.ComplexityProjection.SATSource.JointCircuit
