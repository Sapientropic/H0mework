import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Cost

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Seed
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowsCells)
open CapacityMatching.SourceCost (Counted)

def rows : Clause → List Row
  | [] => [⟨[],true⟩]
  | [row] => [row]
  | _::_::_ => []

theorem rows_entails (clause : Clause) (assignment : Nat → Bool)
    (accepted : clauseRead clause assignment = true) : holds (rows clause) assignment = true := by
  cases clause with
  | nil => simp [clauseRead] at accepted
  | cons row rest =>
      cases rest with
      | nil => simpa [rows,holds,clauseRead] using accepted
      | cons next tail => simp [rows,holds]

theorem rows_within (n : Nat) (clause : Clause) (inside : RowsWithin n clause) : RowsWithin n (rows clause) := by
  cases clause with
  | nil => simp [rows,RowsWithin,InterferenceProgram.Parity.Within]
  | cons row rest =>
      cases rest with
      | nil => exact inside
      | cons next tail => simp [rows,RowsWithin]

theorem rows_storage (clause : Clause) : rowsCells (rows clause) ≤ rowsCells clause+2 := by
  cases clause with
  | nil => simp [rows,CapacityMatching.RowCost.rowCells]
  | cons row rest => cases rest <;> simp [rows,rowsCells]

def select (clause : Clause) : Counted (List Row) :=
  let value := rows clause
  ⟨value,2*rowsCells clause+2*rowsCells value+5⟩

def extract (formula : Formula) : Counted (List Row) := CapacityMatching.RowCost.gather select formula

theorem extract_value (formula : Formula) : (extract formula).value = formula.flatMap rows :=
  CapacityMatching.RowCost.gather_value select formula

theorem extract_within (n : Nat) (formula : Formula) (inside : Within n formula) : RowsWithin n (extract formula).value := by
  rw [extract_value]
  intro row member
  obtain ⟨clause,present,hit⟩ := List.mem_flatMap.mp member
  exact rows_within n clause (inside clause present) row hit

theorem extract_entails (formula : Formula) (assignment : Nat → Bool) (accepted : formulaRead formula assignment = true) :
    holds (extract formula).value assignment = true := by
  apply (holds_iff _ _).mpr
  intro row member
  rw [extract_value] at member
  obtain ⟨clause,present,hit⟩ := List.mem_flatMap.mp member
  exact (holds_iff _ _).mp (rows_entails clause assignment (List.all_eq_true.mp accepted clause present)) row hit

theorem clause_storage (formula : Formula) (clause : Clause) (member : clause ∈ formula) :
    rowsCells clause ≤ formulaSize formula := by
  have bound := List.le_sum_of_mem (List.mem_map.mpr ⟨clause,member,rfl⟩ : rowsCells clause ∈ formula.map rowsCells)
  unfold formulaSize
  omega

theorem extract_storage (formula : Formula) :
    rowsCells (extract formula).value ≤ formula.length*(formulaSize formula+2) :=
  CapacityMatching.RowCost.gather_storage select formula (formulaSize formula+2)
    (fun clause member => (rows_storage clause).trans (Nat.add_le_add_right (clause_storage formula clause member) 2))

def extractBudget (count size : Nat) : Nat := count*(4*size+9+(count+1)*(size+2)+5)+1

theorem extract_cells (formula : Formula) :
    (extract formula).cells ≤ extractBudget formula.length (formulaSize formula) := by
  apply CapacityMatching.RowCost.gather_cells select formula (4*formulaSize formula+9) (formulaSize formula+2)
  · intro clause member
    have stored := rows_storage clause
    have source := clause_storage formula clause member
    simp only [select]
    omega
  · intro clause member
    exact (rows_storage clause).trans (Nat.add_le_add_right (clause_storage formula clause member) 2)

/-- All single-row relations, including the generated image kernel, constrain the first cell. -/
def generate (formula : Formula) : Counted Result :=
  let input := extract formula
  let reduced := EliminateCost.run input.value
  ⟨reduced.result,input.cells+reduced.cells+2*rowsCells input.value+2*AffineCarrier.resultSize reduced.result+3⟩

theorem generate_valid (n : Nat) (formula : Formula) (inside : Within n formula) :
    (generate formula).value.triangular ∧ (generate formula).value.within n := by
  simp only [generate,EliminateCost.run_result]
  exact ⟨eliminate_triangular _,eliminate_within n _ (extract_within n formula inside)⟩

theorem generate_entails (formula : Formula) (assignment : Nat → Bool) (accepted : formulaRead formula assignment = true) :
    (generate formula).value.holds assignment = true := by
  simp only [generate,EliminateCost.run_result,eliminate_holds]
  exact extract_entails formula assignment accepted

theorem generate_read (formula : Formula) (assignment : Nat → Bool) :
    ((generate formula).value.holds assignment && formulaRead formula assignment) = formulaRead formula assignment := by
  by_cases accepted : formulaRead formula assignment = true
  · rw [generate_entails formula assignment accepted,Bool.true_and]
  · rw [Bool.eq_false_iff.mpr accepted,Bool.and_false]

def generateBudget (n count size : Nat) : Nat :=
  extractBudget count size+count*(size+2)*(2*n+EliminateCost.insertCellBudget n+8)+
    2*(AffineCarrier.Cost.cellBound n+1)+4

theorem generate_cells (n : Nat) (formula : Formula) (inside : Within n formula) :
    (generate formula).cells ≤ generateBudget n formula.length (formulaSize formula) := by
  have extracted := extract_cells formula
  have stored := extract_storage formula
  have measures := AffineCarrier.Cost.row_measures (extract formula).value
  have bounded := extract_within n formula inside
  have reduced := EliminateCost.runFrom_cells n (.basis []) triangular_nil (by simp [Result.within,RowsWithin])
    (extract formula).value bounded
  have total : (EliminateCost.run (extract formula).value).cells ≤
      formula.length*(formulaSize formula+2)*(2*n+EliminateCost.insertCellBudget n+6)+1 := by
    have terms := measures.2.trans stored
    have count := measures.1.trans stored
    apply reduced.trans
    calc
      _ ≤ formula.length*(formulaSize formula+2)*(2*n+5)+
          formula.length*(formulaSize formula+2)*(EliminateCost.insertCellBudget n+1)+1 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_right _ terms) (Nat.mul_le_mul_right _ count)) 1
      _ = _ := by ring
  have good := generate_valid n formula inside
  have output := AffineCarrier.Cost.result_size n _ good.1 good.2
  change AffineCarrier.resultSize (EliminateCost.run (extract formula).value).result ≤ _ at output
  simp only [generate,generateBudget]
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Seed
