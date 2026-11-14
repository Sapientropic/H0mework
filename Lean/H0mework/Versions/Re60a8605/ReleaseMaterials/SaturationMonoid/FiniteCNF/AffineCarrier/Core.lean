import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.BinaryRelations
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.EliminateCost

/-!
A positive carrier of generated affine relation cells. A cell denotes its whole
parameterized solution family. The clause action first tests the joint violation
intersection; an empty intersection retains the whole cell. Otherwise its ordered
literal cuts produce a disjoint positive union. The terminal reads the generated
carrier's emptiness and does not invoke a SAT terminal.

The paired ledger includes the existing Gaussian source visits and complete
carrier copying. Counter evaluation and classical bit-level implementation are
separate from these source units.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineCarrier

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram

abbrev Cells := List (List Row)

def read (cells : Cells) (assignment : Nat → Bool) : Bool :=
  cells.any (fun basis => holds basis assignment)

def Valid (n : Nat) (cells : Cells) : Prop :=
  ∀ basis ∈ cells, Triangular basis ∧ RowsWithin n basis

def cellSize (basis : List Row) : Nat := CapacityMatching.RowCost.rowsCells basis+1
def storage (cells : Cells) : Nat := (cells.map cellSize).sum
def resultSize : Result → Nat
  | .contradiction => 1
  | .basis basis => cellSize basis+1

structure Execution where
  value : Cells
  inserts : Nat
  xors : Nat
  visits : Nat
  deriving Repr

def pack (result : Result) : Execution :=
  ⟨match result with | .contradiction => [] | .basis basis => [basis],
    0,0,2*resultSize result+3⟩

def append (left right : Execution) : Execution :=
  ⟨left.value++right.value,left.inserts+right.inserts,left.xors+right.xors,
    left.visits+right.visits+2*storage left.value+2*storage right.value+5⟩

@[simp] theorem read_nil (assignment : Nat → Bool) : read [] assignment = false := rfl
@[simp] theorem read_append (left right : Cells) (assignment : Nat → Bool) :
    read (left++right) assignment = (read left assignment || read right assignment) := by simp [read]

theorem read_pack (result : Result) (assignment : Nat → Bool) :
    read (pack result).value assignment = result.holds assignment := by cases result <;> simp [pack,read,Result.holds]

theorem pack_valid (n : Nat) (result : Result) (triangular : result.triangular) (inside : result.within n) :
    Valid n (pack result).value := by
  cases result with
  | contradiction => simp [pack,Valid]
  | basis basis =>
      intro row member
      have same : row=basis := List.mem_singleton.mp member
      simpa only [same,Result.triangular,Result.within] using And.intro triangular inside

theorem valid_append {n : Nat} (left right : Cells) (leftValid : Valid n left) (rightValid : Valid n right) :
    Valid n (left++right) := by
  intro basis member
  rcases List.mem_append.mp member with first | last
  · exact leftValid basis first
  · exact rightValid basis last

def trueRow {n : Nat} (literal : CNFLiteral n) : Row := ⟨[literal.var.val],literal.positive⟩

theorem trueRow_holds {n : Nat} (literal : CNFLiteral n) (assignment : Nat → Bool) :
    (trueRow literal).holds assignment = literal.eval assignment := by
  simp only [trueRow,Row.holds,Row.eval,Parity.eval,CNFLiteral.eval,Bool.xor_false]
  cases literal.positive <;> cases assignment literal.var.val <;> rfl

theorem trueRow_within {n : Nat} (literal : CNFLiteral n) : Parity.Within n (trueRow literal).vars := by
  intro i member
  have same : i=literal.var.val := List.mem_singleton.mp member
  exact same ▸ literal.var.isLt

theorem insert_valid (n : Nat) (result : Result) (triangular : result.triangular) (inside : result.within n)
    (row : Row) (rowInside : Parity.Within n row.vars) :
    (EliminateCost.insert result row).result.triangular ∧ (EliminateCost.insert result row).result.within n := by
  rw [EliminateCost.insert_result]
  exact ⟨Result.insert_triangular result triangular row,Result.insert_within n result inside row rowInside⟩

def branches {n : Nat} : CNFClause n → Result → Execution
  | [], _ => ⟨[],0,0,1⟩
  | literal::rest, result =>
      let yes := EliminateCost.insert result (trueRow literal)
      let no := EliminateCost.insert result (Propagation.badLiteral literal)
      let joined := append (pack yes.result) (branches rest no.result)
      ⟨joined.value,joined.inserts+2,joined.xors+yes.xors+no.xors,
        joined.visits+yes.cells+no.cells+2*(resultSize result+resultSize yes.result+resultSize no.result)+16⟩

theorem branches_read {n : Nat} (clause : CNFClause n) (result : Result) (assignment : Nat → Bool) :
    read (branches clause result).value assignment = (result.holds assignment && CNFClause.eval clause assignment) := by
  induction clause generalizing result with
  | nil => simp [branches,CNFClause.eval]
  | cons literal rest ih =>
      simp only [branches,append,read_append,read_pack,ih,EliminateCost.insert_result,Result.insert_holds,
        trueRow_holds,Propagation.badLiteral_holds,CNFClause.eval,List.any_cons]
      cases result.holds assignment <;> cases literal.eval assignment <;> cases rest.any (fun lit => lit.eval assignment) <;> rfl

theorem branches_valid {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) : Valid n (branches clause result).value := by
  induction clause generalizing result with
  | nil => simp [branches,Valid]
  | cons literal rest ih =>
      have yes := insert_valid n result triangular inside (trueRow literal) (trueRow_within literal)
      have no := insert_valid n result triangular inside (Propagation.badLiteral literal) (Propagation.badLiteral_within literal)
      exact valid_append _ _ (pack_valid n _ yes.1 yes.2) (ih _ no.1 no.2)

def cut {n : Nat} (clause : CNFClause n) (result : Result) : Execution :=
  let checked := EliminateCost.runFrom result (clause.map Propagation.badLiteral)
  let output := match checked.result with
    | .contradiction => pack result
    | .basis _ => branches clause result
  ⟨output.value,clause.length+output.inserts,checked.xors+output.xors,
    checked.cells+output.visits+4*clause.length+2*(resultSize result+resultSize checked.result)+5⟩

theorem cut_read {n : Nat} (clause : CNFClause n) (result : Result) (assignment : Nat → Bool) :
    read (cut clause result).value assignment = (result.holds assignment && CNFClause.eval clause assignment) := by
  have intersection := eliminateFrom_holds result (clause.map Propagation.badLiteral) assignment
  rw [← EliminateCost.runFrom_result,BinaryRelations.badRows_value] at intersection
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result with
  | contradiction =>
      simp only [cut,checked,read_pack]
      rw [checked,Result.holds] at intersection
      cases value : result.holds assignment <;> cases accepted : CNFClause.eval clause assignment <;> simp_all
  | basis basis => simpa only [cut,checked] using branches_read clause result assignment

theorem cut_valid {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) : Valid n (cut clause result).value := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result with
  | contradiction => simpa only [cut,checked] using pack_valid n result triangular inside
  | basis basis => simpa only [cut,checked] using branches_valid clause result triangular inside

def clauseAction {n : Nat} (clause : CNFClause n) : Cells → Execution
  | [] => ⟨[],0,0,1⟩
  | basis::rest => append (cut clause (.basis basis)) (clauseAction clause rest)

theorem clauseAction_read {n : Nat} (clause : CNFClause n) (cells : Cells) (assignment : Nat → Bool) :
    read (clauseAction clause cells).value assignment = (read cells assignment && CNFClause.eval clause assignment) := by
  induction cells with
  | nil => simp [clauseAction]
  | cons basis rest ih =>
      change read ((cut clause (.basis basis)).value++(clauseAction clause rest).value) assignment = _
      rw [read_append,cut_read,ih]
      change ((holds basis assignment && CNFClause.eval clause assignment) ||
        (read rest assignment && CNFClause.eval clause assignment)) =
          ((holds basis assignment || read rest assignment) && CNFClause.eval clause assignment)
      cases holds basis assignment <;> cases read rest assignment <;>
        cases CNFClause.eval clause assignment <;> rfl

theorem clauseAction_valid {n : Nat} (clause : CNFClause n) (cells : Cells) (valid : Valid n cells) :
    Valid n (clauseAction clause cells).value := by
  induction cells with
  | nil => simp [clauseAction,Valid]
  | cons basis rest ih =>
      have first := valid basis (by simp)
      exact valid_append _ _ (cut_valid clause (.basis basis) first.1 first.2)
        (ih (fun other member => valid other (by simp [member])))

def run {n : Nat} : CNFFormula n → Cells → Execution
  | [], cells => ⟨cells,0,0,2*storage cells+1⟩
  | clause::rest, cells =>
      let first := clauseAction clause cells
      let next := run rest first.value
      ⟨next.value,first.inserts+next.inserts,first.xors+next.xors,first.visits+next.visits+2⟩

theorem run_read {n : Nat} (formula : CNFFormula n) (cells : Cells) (assignment : Nat → Bool) :
    read (run formula cells).value assignment = (read cells assignment && CNFFormula.eval formula assignment) := by
  induction formula generalizing cells with
  | nil => simp [run,CNFFormula.eval]
  | cons clause rest ih =>
      simp only [run,ih,clauseAction_read,CNFFormula.eval,List.all_cons,Bool.and_assoc]

theorem run_valid {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) :
    Valid n (run formula cells).value := by
  induction formula generalizing cells with
  | nil => exact valid
  | cons clause rest ih => exact ih _ (clauseAction_valid clause cells valid)

def seed {n : Nat} (formula : CNFFormula n) : Execution :=
  let extracted := Extract.run formula
  let original := EliminateCost.run extracted.rows
  let extra := CapacityMatching.RowCost.prepare formula
  let generated := EliminateCost.runFrom original.result extra.value
  let output := pack generated.result
  ⟨output.value,extracted.rows.length+extra.value.length,original.xors+generated.xors,
    extracted.visits+original.cells+extra.cells+generated.cells+output.visits+
      2*(resultSize original.result+resultSize generated.result)+8⟩

theorem seed_result {n : Nat} (formula : CNFFormula n) :
    (seed formula).value = (pack (eliminateFrom (eliminate (Extract.extract formula))
      (CapacityMatching.SourceTight.prepare formula))).value := by
  simp only [seed,EliminateCost.run_result,EliminateCost.runFrom_result,
    CapacityMatching.RowCost.prepare_value]
  rfl

theorem seed_valid {n : Nat} (formula : CNFFormula n) : Valid n (seed formula).value := by
  rw [seed_result]
  apply pack_valid
  · exact eliminateFrom_triangular _ (eliminate_triangular _) _
  · exact eliminateFrom_within n _ (eliminate_within n _ (extract_rowsWithin formula)) _
      (CapacityMatching.SourceTight.prepare_within formula)

theorem seed_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : read (seed formula).value assignment = true := by
  rw [seed_result,read_pack,eliminateFrom_holds,eliminate_holds]
  rw [Extract.extract_entails formula assignment accepted,CapacityMatching.SourceTight.prepare_entails formula assignment accepted]
  rfl

def generate {n : Nat} (formula : CNFFormula n) : Execution :=
  let initial := seed formula
  let final := run formula initial.value
  ⟨final.value,initial.inserts+final.inserts,initial.xors+final.xors,initial.visits+final.visits+2⟩

theorem generate_valid {n : Nat} (formula : CNFFormula n) : Valid n (generate formula).value :=
  run_valid formula _ (seed_valid formula)

theorem generate_read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read (generate formula).value assignment = CNFFormula.eval formula assignment := by
  change read (run formula (seed formula).value).value assignment = _
  rw [run_read]
  by_cases accepted : CNFFormula.eval formula assignment = true
  · rw [seed_entails formula assignment accepted,accepted]
    rfl
  · simp [Bool.eq_false_iff.mpr accepted]

def Separated (cells : Cells) : Prop :=
  cells.Pairwise (fun left right => ∀ assignment, (holds left assignment && holds right assignment) = false)

theorem member_read (cells : Cells) (basis : List Row) (member : basis ∈ cells) (assignment : Nat → Bool)
    (accepted : holds basis assignment = true) : read cells assignment = true :=
  List.any_eq_true.mpr ⟨basis,member,accepted⟩

theorem pack_separated (result : Result) : Separated (pack result).value := by cases result <;> simp [pack,Separated]

theorem separated_append (left right : Cells) (leftSeparated : Separated left) (rightSeparated : Separated right)
    (apart : ∀ assignment, (read left assignment && read right assignment) = false) : Separated (left++right) := by
  apply List.pairwise_append.mpr
  refine ⟨leftSeparated,rightSeparated,?_⟩
  intro first firstMember second secondMember assignment
  by_cases firstTrue : holds first assignment = true
  · by_cases secondTrue : holds second assignment = true
    · have impossible := apart assignment
      rw [member_read left first firstMember assignment firstTrue,
        member_read right second secondMember assignment secondTrue] at impossible
      cases impossible
    · simp [Bool.eq_false_iff.mpr secondTrue]
  · simp [Bool.eq_false_iff.mpr firstTrue]

theorem branches_separated {n : Nat} (clause : CNFClause n) (result : Result) : Separated (branches clause result).value := by
  induction clause generalizing result with
  | nil => simp [branches,Separated]
  | cons literal rest ih =>
      apply separated_append _ _ (pack_separated _) (ih _)
      intro assignment
      rw [read_pack,branches_read,EliminateCost.insert_result,EliminateCost.insert_result,
        Result.insert_holds,Result.insert_holds,trueRow_holds,Propagation.badLiteral_holds]
      cases result.holds assignment <;> cases literal.eval assignment <;> cases CNFClause.eval rest assignment <;> rfl

theorem cut_separated {n : Nat} (clause : CNFClause n) (result : Result) : Separated (cut clause result).value := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result with
  | contradiction => simpa only [cut,checked] using pack_separated result
  | basis basis => simpa only [cut,checked] using branches_separated clause result

theorem separated_cons (basis : List Row) (rest : Cells) (separate : Separated (basis::rest)) (assignment : Nat → Bool) :
    (holds basis assignment && read rest assignment) = false := by
  have pairs := List.pairwise_cons.mp separate
  by_cases first : holds basis assignment = true
  · by_cases tail : read rest assignment = true
    · obtain ⟨other,member,accepted⟩ := List.any_eq_true.mp tail
      have impossible := pairs.1 other member assignment
      simp [first,accepted] at impossible
    · simp [Bool.eq_false_iff.mpr tail]
  · simp [Bool.eq_false_iff.mpr first]

theorem clauseAction_separated {n : Nat} (clause : CNFClause n) (cells : Cells) (separate : Separated cells) :
    Separated (clauseAction clause cells).value := by
  induction cells with
  | nil => simp [clauseAction,Separated]
  | cons basis rest ih =>
      apply separated_append _ _ (cut_separated clause (.basis basis)) (ih (List.pairwise_cons.mp separate).2)
      intro assignment
      have before := separated_cons basis rest separate assignment
      rw [cut_read,clauseAction_read]
      change ((holds basis assignment && CNFClause.eval clause assignment) &&
        (read rest assignment && CNFClause.eval clause assignment)) = false
      cases first : holds basis assignment <;> cases last : read rest assignment <;>
        cases CNFClause.eval clause assignment <;> simp_all

theorem run_separated {n : Nat} (formula : CNFFormula n) (cells : Cells) (separate : Separated cells) :
    Separated (run formula cells).value := by
  induction formula generalizing cells with
  | nil => exact separate
  | cons clause rest ih => exact ih _ (clauseAction_separated clause cells separate)

theorem generate_separated {n : Nat} (formula : CNFFormula n) : Separated (generate formula).value := by
  apply run_separated
  rw [seed_result]
  exact pack_separated _

/-- An alternative strongest currently available row seed; its feedback budget is independent of the paired seed above. -/
def tightSeed {n : Nat} (formula : CNFFormula n) : Result :=
  TightFeedback.generate formula (Extract.extract formula++(CapacityMatching.RowCost.prepare formula).value)

theorem tightSeed_valid {n : Nat} (formula : CNFFormula n) : (tightSeed formula).triangular ∧ (tightSeed formula).within n := by
  have inside : RowsWithin n (Extract.extract formula++(CapacityMatching.RowCost.prepare formula).value) := by
    rw [CapacityMatching.RowCost.prepare_value]
    intro row member
    rcases List.mem_append.mp member with first | second
    · exact extract_rowsWithin formula row first
    · exact CapacityMatching.SourceTight.prepare_within formula row second
  exact (TightFeedback.generate_invariants formula _ inside).symm

theorem tightSeed_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : (tightSeed formula).holds assignment = true := by
  have same := TightFeedback.generate_holds formula
    (Extract.extract formula++(CapacityMatching.RowCost.prepare formula).value) assignment
  rw [CapacityMatching.RowCost.prepare_value] at same
  have original := Extract.extract_entails formula assignment accepted
  have generated := CapacityMatching.SourceTight.prepare_entails formula assignment accepted
  have both : holds (Extract.extract formula++CapacityMatching.SourceTight.prepare formula) assignment = true := by
    simp only [holds,List.all_append] at original generated ⊢
    rw [original,generated]
    rfl
  rw [accepted,Bool.true_and,both] at same
  simpa only [tightSeed,CapacityMatching.RowCost.prepare_value,Bool.true_and] using same

def tightCells {n : Nat} (formula : CNFFormula n) : Cells := (run formula (pack (tightSeed formula)).value).value

theorem tightCells_valid {n : Nat} (formula : CNFFormula n) : Valid n (tightCells formula) :=
  run_valid formula _ (pack_valid n _ (tightSeed_valid formula).1 (tightSeed_valid formula).2)

theorem tightCells_read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read (tightCells formula) assignment = CNFFormula.eval formula assignment := by
  rw [tightCells,run_read,read_pack]
  by_cases accepted : CNFFormula.eval formula assignment = true
  · rw [tightSeed_entails formula assignment accepted,accepted]
    rfl
  · simp [Bool.eq_false_iff.mpr accepted]

def Parameters (n : Nat) (cells : Cells) :=
  (i : Fin cells.length) × Assignment (freeIndices n (cells.get i)).length

def lift (n : Nat) (cells : Cells) (parameter : Parameters n cells) : Assignment n :=
  parameterLift n (cells.get parameter.1) parameter.2

theorem lift_image (n : Nat) (cells : Cells) (valid : Valid n cells) (assignment : Assignment n) :
    (∃ parameter : Parameters n cells, lift n cells parameter = assignment) ↔ read cells (extendAssignment assignment) = true := by
  constructor
  · rintro ⟨⟨i,parameters⟩,rfl⟩
    apply List.any_eq_true.mpr
    refine ⟨cells.get i,List.get_mem _ _,?_⟩
    exact parameterLift_holds n _ (valid _ (List.get_mem _ _)).1 (valid _ (List.get_mem _ _)).2 parameters
  · intro accepted
    obtain ⟨basis,member,satisfied⟩ := List.any_eq_true.mp accepted
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact ⟨⟨i,projectFree n (cells.get i) assignment⟩,
      parameterLift_projectFree n _ (valid _ (List.get_mem _ _)).1 assignment satisfied⟩

theorem generate_image {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    (∃ parameter : Parameters n (generate formula).value,
      lift n (generate formula).value parameter = assignment) ↔ CNFFormula.eval formula (extendAssignment assignment) = true := by
  rw [lift_image n _ (generate_valid formula),generate_read]

theorem nonempty_iff (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (!cells.isEmpty) = true ↔ ∃ assignment : Assignment n, read cells (extendAssignment assignment) = true := by
  cases cells with
  | nil => simp
  | cons basis rest =>
      simp only [List.isEmpty_cons,Bool.not_false,true_iff]
      let parameters : Assignment (freeIndices n basis).length := fun _ => false
      refine ⟨parameterLift n basis parameters,?_⟩
      have satisfied := parameterLift_holds n basis (valid basis (by simp)).1 (valid basis (by simp)).2 parameters
      simp [read,satisfied]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool := !(generate formula).value.isEmpty

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula,nonempty_iff n _ (generate_valid formula)]
  constructor
  · rintro ⟨assignment,accepted⟩
    exact ⟨extendAssignment assignment,(generate_read formula _).symm ▸ accepted⟩
  · rintro ⟨assignment,accepted⟩
    let finite : Assignment n := fun i => assignment i.val
    refine ⟨finite,?_⟩
    rw [generate_read]
    exact (formula_eval_restrict formula assignment).trans accepted

def sourceAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read (generate formula).value (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [zeroProjector_apply,sourceAction,generate_read]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits,Encoding.decideBits,parsed]
  | some input =>
      simp only [decideBits,Encoding.decideBits,parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct,Dense.decideFormula_correct]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original,Encoding.decideBits_iff_rootVerify]

end SaturationMonoid.ComplexityProjection.SATSource.AffineCarrier
