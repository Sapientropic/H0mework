import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Future

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineResidual
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula formulaRead clauseRead formulaSize Within)
open CapacityMatching.SourceCost (Counted)
open CapacityMatching.RowCost (rowsCells)
open InterferenceProgram

def rewrite (table : Array Row) : Formula → Counted Formula
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := CapacityMatching.RowCost.decodeRows table clause
      let tail := rewrite table rest
      ⟨first.value::tail.value,first.cells+tail.cells+2*(rowsCells first.value+formulaSize tail.value)+5⟩

theorem rewrite_value (table : Array Row) (formula : Formula) :
    (rewrite table formula).value = formula.map (fun clause => clause.map (fun row => Table.combine table row.vars ⟨[],row.rhs⟩)) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [rewrite,CapacityMatching.RowCost.decodeRows_value,ih,List.map_cons]

theorem combine_holds (table : Array Row) (row : Row) (assignment : Nat → Bool) :
    (Table.combine table row.vars ⟨[],row.rhs⟩).holds assignment = row.holds (Gates.coordinate table assignment) := by
  rw [Atoms.holds_not_value,Atoms.holds_not_value,Table.combine_value]
  simp only [Gates.value,Row.eval,Parity.eval,Bool.xor_false]

theorem rewrite_read (table : Array Row) (formula : Formula) (assignment : Nat → Bool) :
    formulaRead (rewrite table formula).value assignment = formulaRead formula (Gates.coordinate table assignment) := by
  rw [rewrite_value]
  simp only [formulaRead,List.all_map]
  apply List.all_congr rfl
  intro clause
  simp only [Function.comp_apply,clauseRead,List.any_map]
  apply List.any_congr rfl
  intro row
  exact combine_holds table row assignment

theorem rewrite_within (width : Nat) (table : Array Row) (valid : Table.Valid width table) (formula : Formula) :
    Within width (rewrite table formula).value := by
  rw [rewrite_value]
  intro clause member row present
  obtain ⟨source,inFormula,rfl⟩ := List.mem_map.mp member
  obtain ⟨original,inClause,rfl⟩ := List.mem_map.mp present
  exact (Table.combine_valid width table valid original.vars ⟨[],original.rhs⟩
    (by simp [Table.RowValid,Parity.Within])).2

theorem rewrite_length (table : Array Row) (formula : Formula) :
    (rewrite table formula).value.length=formula.length := by simp [rewrite_value]

structure Output where
  table : Array Row
  value : Formula
  cells : Nat
  deriving Repr

def generate (n : Nat) (basis : List Row) (formula : Formula) : Output :=
  let table := Table.coordinates n basis
  let rewritten := rewrite table formula
  let reduced := AffineClauses.cleanRun rewritten.value
  ⟨table,reduced.value,AffineCollect.coordinateWork n basis+rewritten.cells+reduced.visits+
    2*(AffineCollect.tableSize table+formulaSize rewritten.value+formulaSize reduced.value)+9⟩

theorem generate_value (n : Nat) (basis : List Row) (formula : Formula) :
    (generate n basis formula).value = AffineClauses.clean (rewrite (Table.coordinates n basis) formula).value := by
  simp only [generate,AffineClauses.cleanRun_value]

theorem generate_read (n : Nat) (basis : List Row) (formula : Formula) (assignment : Nat → Bool) :
    formulaRead (generate n basis formula).value assignment =
      formulaRead formula (Gates.coordinate (Table.coordinates n basis) assignment) := by
  rw [generate_value,AffineClauses.clean_read,rewrite_read]

theorem generate_within (n : Nat) (basis : List Row) (formula : Formula) :
    Within (freeIndices n basis).length (generate n basis formula).value := by
  rw [generate_value]
  exact AffineClauses.clean_within _ _ (rewrite_within _ _ (Table.coordinates_valid n basis) formula)

theorem generate_length (n : Nat) (basis : List Row) (formula : Formula) :
    (generate n basis formula).value.length ≤ formula.length := by
  rw [generate_value,← rewrite_length (Table.coordinates n basis) formula]
  exact List.length_filter_le _ _

theorem generate_parameter (n : Nat) (basis : List Row) (formula : Formula) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    formulaRead (generate n basis formula).value (extendAssignment parameters) =
      formulaRead formula (extendAssignment (parameterLift n basis parameters)) := by
  rw [generate_read,Table.coordinates_value n basis inside,extend_parameterLift n basis inside]

theorem generate_possible (n : Nat) (basis : List Row) (formula : Formula)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    AffineClauseProduct.Satisfiable (generate n basis formula).value ↔
      ∃ original : Assignment n, holds basis (extendAssignment original)=true ∧
        formulaRead formula (extendAssignment original)=true := by
  constructor
  · rintro ⟨point,accepted⟩
    let parameters : Assignment (freeIndices n basis).length := fun i => point i.val
    have finite := (AffineClauseProduct.formula_restrict _ _ (generate_within n basis formula) point).trans accepted
    rw [generate_parameter n basis formula valid.2 parameters] at finite
    exact ⟨parameterLift n basis parameters,parameterLift_holds n basis valid.1 valid.2 parameters,finite⟩
  · rintro ⟨point,inBasis,accepted⟩
    refine ⟨extendAssignment (projectFree n basis point),?_⟩
    rw [generate_parameter n basis formula valid.2,parameterLift_projectFree n basis valid.1 point inBasis]
    exact accepted

end SaturationMonoid.ComplexityProjection.SATSource.AffineResidual
