import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Execution read storage resultSize pack append)
open InterferenceProgram

abbrev Clause := List Row
abbrev Formula := List Clause

def clauseRead (clause : Clause) (assignment : Nat → Bool) : Bool := clause.any (fun row => row.holds assignment)
def formulaRead (formula : Formula) (assignment : Nat → Bool) : Bool := formula.all (fun clause => clauseRead clause assignment)
def Within (n : Nat) (formula : Formula) : Prop := ∀ clause ∈ formula, RowsWithin n clause

theorem flip_clause (clause : Clause) (assignment : Nat → Bool) :
    holds (clause.map Propagation.flip) assignment = !clauseRead clause assignment := by
  induction clause with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.map_cons,holds,List.all_cons,Propagation.flip_holds,clauseRead,List.any_cons]
      change (!row.holds assignment && holds (rest.map Propagation.flip) assignment) = _
      rw [ih]
      change (!row.holds assignment && !clauseRead rest assignment) = !(row.holds assignment || clauseRead rest assignment)
      cases row.holds assignment <;> cases clauseRead rest assignment <;> rfl

def branches : Clause → Result → Execution
  | [],_ => ⟨[],0,0,1⟩
  | row::rest,result =>
      let yes := EliminateCost.insert result row
      let no := EliminateCost.insert result (Propagation.flip row)
      let joined := append (pack yes.result) (branches rest no.result)
      ⟨joined.value,joined.inserts+2,joined.xors+yes.xors+no.xors,
        joined.visits+yes.cells+no.cells+2*(resultSize result+resultSize yes.result+resultSize no.result)+16⟩

theorem branches_read (clause : Clause) (result : Result) (assignment : Nat → Bool) :
    read (branches clause result).value assignment = (result.holds assignment && clauseRead clause assignment) := by
  induction clause generalizing result with
  | nil => simp [branches,clauseRead]
  | cons row rest ih =>
      simp only [branches,append,AffineCarrier.read_append,AffineCarrier.read_pack,ih,
        EliminateCost.insert_result,Result.insert_holds,Propagation.flip_holds,clauseRead,List.any_cons]
      cases result.holds assignment <;> cases row.holds assignment <;> cases rest.any (fun r => r.holds assignment) <;> rfl

theorem flip_within (n : Nat) (row : Row) (inside : Parity.Within n row.vars) :
    Parity.Within n (Propagation.flip row).vars := inside

theorem branches_valid (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause)
    (result : Result) (triangular : result.triangular) (inside : result.within n) :
    AffineCarrier.Valid n (branches clause result).value := by
  induction clause generalizing result with
  | nil => simp [branches,AffineCarrier.Valid]
  | cons row rest ih =>
      have first := rowInside row (by simp)
      have tail : RowsWithin n rest := fun r member => rowInside r (by simp [member])
      have yes := AffineCarrier.insert_valid n result triangular inside row first
      have no := AffineCarrier.insert_valid n result triangular inside (Propagation.flip row) first
      exact AffineCarrier.valid_append _ _ (AffineCarrier.pack_valid n _ yes.1 yes.2) (ih tail _ no.1 no.2)

def cut (clause : Clause) (result : Result) : Execution :=
  let checked := EliminateCost.runFrom result (clause.map Propagation.flip)
  let output := match checked.result with
    | .contradiction => pack result
    | .basis _ => branches clause result
  ⟨output.value,clause.length+output.inserts,checked.xors+output.xors,
    checked.cells+output.visits+4*CapacityMatching.RowCost.rowsCells clause+
      2*(resultSize result+resultSize checked.result)+5⟩

theorem cut_read (clause : Clause) (result : Result) (assignment : Nat → Bool) :
    read (cut clause result).value assignment = (result.holds assignment && clauseRead clause assignment) := by
  have intersection := eliminateFrom_holds result (clause.map Propagation.flip) assignment
  rw [← EliminateCost.runFrom_result,flip_clause] at intersection
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result with
  | contradiction =>
      simp only [cut,checked,AffineCarrier.read_pack]
      rw [checked,Result.holds] at intersection
      cases value : result.holds assignment <;> cases accepted : clauseRead clause assignment <;> simp_all
  | basis basis => simpa only [cut,checked] using branches_read clause result assignment

theorem cut_valid (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause)
    (result : Result) (triangular : result.triangular) (inside : result.within n) :
    AffineCarrier.Valid n (cut clause result).value := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result with
  | contradiction => simpa only [cut,checked] using AffineCarrier.pack_valid n result triangular inside
  | basis basis => simpa only [cut,checked] using branches_valid n clause rowInside result triangular inside

def clauseAction (clause : Clause) : Cells → Execution
  | [] => ⟨[],0,0,1⟩
  | basis::rest => append (cut clause (.basis basis)) (clauseAction clause rest)

theorem clauseAction_read (clause : Clause) (cells : Cells) (assignment : Nat → Bool) :
    read (clauseAction clause cells).value assignment = (read cells assignment && clauseRead clause assignment) := by
  induction cells with
  | nil => simp [clauseAction]
  | cons basis rest ih =>
      change read ((cut clause (.basis basis)).value++(clauseAction clause rest).value) assignment = _
      rw [AffineCarrier.read_append,cut_read,ih]
      change ((holds basis assignment && clauseRead clause assignment) ||
        (read rest assignment && clauseRead clause assignment)) =
          ((holds basis assignment || read rest assignment) && clauseRead clause assignment)
      cases holds basis assignment <;> cases read rest assignment <;> cases clauseRead clause assignment <;> rfl

theorem clauseAction_valid (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause)
    (cells : Cells) (valid : AffineCarrier.Valid n cells) : AffineCarrier.Valid n (clauseAction clause cells).value := by
  induction cells with
  | nil => simp [clauseAction,AffineCarrier.Valid]
  | cons basis rest ih =>
      have first := valid basis (by simp)
      exact AffineCarrier.valid_append _ _ (cut_valid n clause rowInside (.basis basis) first.1 first.2)
        (ih (fun other member => valid other (by simp [member])))

def run (n : Nat) : Formula → Cells → AffineCollect.Execution
  | [],cells => ⟨cells,0,0,2*storage cells+1⟩
  | clause::rest,cells =>
      let first := clauseAction clause cells
      let shared := AffineCollect.collect n first.value
      let next := run n rest shared.value
      ⟨next.value,shared.merges+next.merges,shared.attempts+next.attempts,
        first.visits+shared.visits+next.visits+3⟩

theorem run_valid (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : AffineCarrier.Valid n cells) : AffineCarrier.Valid n (run n formula cells).value := by
  induction formula generalizing cells with
  | nil => exact valid
  | cons clause rest ih =>
      have rowInside := inside clause (by simp)
      exact ih (fun c member => inside c (by simp [member])) _
        (AffineCollect.collect_valid n _ (clauseAction_valid n clause rowInside cells valid))

theorem run_read (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : AffineCarrier.Valid n cells) (assignment : Nat → Bool) :
    read (run n formula cells).value assignment = (read cells assignment && formulaRead formula assignment) := by
  induction formula generalizing cells with
  | nil => simp [run,formulaRead]
  | cons clause rest ih =>
      have cutValid := clauseAction_valid n clause (inside clause (by simp)) cells valid
      have nextValid := AffineCollect.collect_valid n _ cutValid
      simp only [run,ih (fun c member => inside c (by simp [member])) _ nextValid,
        AffineCollect.collect_read n _ cutValid,clauseAction_read,formulaRead,List.all_cons,Bool.and_assoc]

def tautology (clause : Clause) : Bool :=
  match (EliminateCost.run (clause.map Propagation.flip)).result with
  | .contradiction => true
  | .basis _ => false

theorem tautology_iff (clause : Clause) : tautology clause = true ↔ ∀ assignment, clauseRead clause assignment = true := by
  have values (assignment : Nat → Bool) :
      (EliminateCost.run (clause.map Propagation.flip)).result.holds assignment = !clauseRead clause assignment := by
    rw [EliminateCost.run_result,eliminate_holds,flip_clause]
  cases generated : (EliminateCost.run (clause.map Propagation.flip)).result with
  | contradiction =>
      simp only [tautology,generated,true_iff]
      intro assignment
      have same := values assignment
      rw [generated] at same
      change false = !clauseRead clause assignment at same
      simpa using same
  | basis basis =>
      have triangular : Triangular basis := by
        have good := eliminate_triangular (clause.map Propagation.flip)
        rw [← EliminateCost.run_result,generated] at good
        exact good
      have hit := values (fill basis (fun _ => false))
      rw [generated] at hit
      change holds basis (fill basis (fun _ => false)) = _ at hit
      rw [fill_holds basis triangular] at hit
      rw [tautology,generated]
      change false = true ↔ _
      constructor
      · intro impossible
        cases impossible
      · intro all
        rw [all] at hit
        cases hit

def clean (formula : Formula) : Formula := formula.filter (fun clause => !tautology clause)

theorem clean_read (formula : Formula) (assignment : Nat → Bool) : formulaRead (clean formula) assignment = formulaRead formula assignment := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      by_cases yes : tautology clause = true
      · have truth := (tautology_iff clause).mp yes assignment
        simp [clean,yes,formulaRead,truth] at ih ⊢
        exact ih
      · simp [clean,Bool.eq_false_iff.mpr yes,formulaRead] at ih ⊢
        rw [ih]

theorem clean_within (n : Nat) (formula : Formula) (inside : Within n formula) : Within n (clean formula) :=
  fun clause member => inside clause (List.mem_filter.mp member).1

def formulaSize (formula : Formula) : Nat := (formula.map CapacityMatching.RowCost.rowsCells).sum+formula.length+1

structure Clean where
  value : Formula
  visits : Nat
  deriving Repr

def cleanRun : Formula → Clean
  | [] => ⟨[],1⟩
  | clause::rest =>
      let checked := EliminateCost.run (clause.map Propagation.flip)
      let tail := cleanRun rest
      let value := match checked.result with
        | .contradiction => tail.value
        | .basis _ => clause::tail.value
      ⟨value,checked.cells+tail.visits+4*CapacityMatching.RowCost.rowsCells clause+
        2*resultSize checked.result+2*formulaSize value+8⟩

theorem cleanRun_value (formula : Formula) : (cleanRun formula).value = clean formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases checked : (EliminateCost.run (clause.map Propagation.flip)).result <;>
        simp [cleanRun,checked,clean,tautology] at ih ⊢ <;> exact ih

def generate (n : Nat) (formula : Formula) : AffineCollect.Execution :=
  let prepared := cleanRun formula
  let output := run n prepared.value [[]]
  ⟨output.value,output.merges,output.attempts,prepared.visits+output.visits+2⟩

theorem generate_valid (n : Nat) (formula : Formula) (inside : Within n formula) :
    AffineCarrier.Valid n (generate n formula).value := by
  change AffineCarrier.Valid n (run n (cleanRun formula).value [[]]).value
  rw [cleanRun_value]
  exact run_valid n (clean formula) (clean_within n formula inside) [[]] (by
    intro basis member
    have same : basis=[] := List.mem_singleton.mp member
    subst basis
    exact ⟨triangular_nil,by simp [RowsWithin]⟩)

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Nat → Bool) :
    read (generate n formula).value assignment = formulaRead formula assignment := by
  change read (run n (cleanRun formula).value [[]]).value assignment = _
  rw [cleanRun_value,run_read n _ (clean_within n formula inside) _ (by
    intro basis member
    have same : basis=[] := List.mem_singleton.mp member
    subst basis
    exact ⟨triangular_nil,by simp [RowsWithin]⟩)]
  simp [AffineCarrier.read,holds,clean_read]

def literalRow {n : Nat} (table : Array Row) (literal : CNFLiteral n) : Row :=
  let source := table.toList.getD literal.var.val Gates.zeroRow
  ⟨source.vars,source.rhs ^^ literal.positive⟩

theorem literalRow_read {n : Nat} (table : Array Row) (literal : CNFLiteral n) (assignment : Nat → Bool) :
    (literalRow table literal).holds assignment = literal.eval (Gates.coordinate table assignment) := by
  simp only [literalRow,Row.holds,Row.eval,CNFLiteral.eval,Gates.coordinate,Gates.value]
  cases (table.toList.getD literal.var.val Gates.zeroRow).rhs <;>
    cases Parity.eval assignment (table.toList.getD literal.var.val Gates.zeroRow).vars <;> cases literal.positive <;> rfl

def compile {n : Nat} (table : Array Row) (formula : CNFFormula n) : Formula :=
  formula.map (fun clause => clause.map (literalRow table))

theorem compile_read {n : Nat} (table : Array Row) (formula : CNFFormula n) (assignment : Nat → Bool) :
    formulaRead (compile table formula) assignment = CNFFormula.eval formula (Gates.coordinate table assignment) := by
  simp [formulaRead,compile,clauseRead,CNFFormula.eval,CNFClause.eval,Function.comp_def,literalRow_read]

theorem compile_within {n : Nat} (width : Nat) (table : Array Row) (valid : Table.Valid width table) (formula : CNFFormula n) :
    Within width (compile table formula) := by
  intro clause member row inClause
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  obtain ⟨literal,_,rfl⟩ := List.mem_map.mp inClause
  intro address hit
  exact Gates.getD_within width table.toList (fun row member => (valid row member).2) literal.var.val address hit

theorem coordinate_read {n : Nat} (formula : CNFFormula n) (basis : List Row) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    read (generate (freeIndices n basis).length (compile (Table.coordinates n basis) formula)).value
      (extendAssignment parameters) = CNFFormula.eval formula (extendAssignment (parameterLift n basis parameters)) := by
  rw [generate_read _ _ (compile_within _ _ (Table.coordinates_valid n basis) formula),compile_read]
  have agree : ∀ i : Fin n, Gates.coordinate (Table.coordinates n basis) (extendAssignment parameters) i.val =
      extendAssignment (parameterLift n basis parameters) i.val := by
    intro i
    simpa [extendAssignment,parameterLift] using
      congrFun (Table.coordinates_value n basis inside (extendAssignment parameters)) i.val
  apply Factor.formula_eval_agree
  intro clause _ literal _
  exact agree literal.var

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses
