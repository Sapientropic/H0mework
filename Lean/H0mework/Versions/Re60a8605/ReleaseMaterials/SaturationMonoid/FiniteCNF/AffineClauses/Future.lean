import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Group
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Forget
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.StrongImage
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.ProductCost

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Future
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid read)

def step (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) : Cells :=
  let acted := clauseAction clause cells
  let projected := AffineForget.cells n (AffineClauseProduct.support remaining) acted.value
  (AffineGroupCover.compact n projected).value

theorem step_valid (n : Nat) (clause : Clause) (remaining : Formula) (cells : Cells) :
    Valid n (step n clause remaining cells) :=
  AffineGroupCover.compact_valid n _ (AffineForget.cells_valid n _ _)

theorem step_future (n : Nat) (clause : Clause) (remaining : Formula) (inside : Within n (clause::remaining))
    (cells : Cells) (valid : Valid n cells) :
    (∃ assignment : Assignment n, read (step n clause remaining cells) (extendAssignment assignment)=true ∧
      formulaRead remaining (extendAssignment assignment)=true) ↔
    (∃ assignment : Assignment n, read cells (extendAssignment assignment)=true ∧
      formulaRead (clause::remaining) (extendAssignment assignment)=true) := by
  have acted := clauseAction_valid n clause (inside clause (by simp)) cells valid
  have future : Within n remaining := fun c member => inside c (by simp [member])
  simp only [step,AffineGroupCover.compact_read n _ (AffineForget.cells_valid n _ _)]
  rw [AffineForget.cells_row_future n remaining future _ acted]
  simp only [clauseAction_read,formulaRead,List.all_cons,Bool.and_eq_true,and_assoc]

def run (n : Nat) : Formula → Cells → Cells
  | [],cells => cells
  | clause::rest,cells => run n rest (step n clause rest cells)

theorem run_valid (n : Nat) (formula : Formula) (cells : Cells) (valid : Valid n cells) : Valid n (run n formula cells) := by
  induction formula generalizing cells with
  | nil => exact valid
  | cons clause rest ih => exact ih _ (step_valid n clause rest cells)

theorem run_possible (n : Nat) (formula : Formula) (inside : Within n formula) (cells : Cells) (valid : Valid n cells) :
    (∃ assignment : Assignment n, read (run n formula cells) (extendAssignment assignment)=true) ↔
      ∃ assignment : Assignment n, read cells (extendAssignment assignment)=true ∧
        formulaRead formula (extendAssignment assignment)=true := by
  induction formula generalizing cells with
  | nil => simp [run,formulaRead]
  | cons clause rest ih =>
      rw [run,ih (fun c member => inside c (by simp [member])) _ (step_valid n clause rest cells)]
      exact step_future n clause rest inside cells valid

def body (formula : Formula) : Formula := formula.filter (fun clause => decide (2 ≤ clause.length))

theorem body_within (n : Nat) (formula : Formula) (inside : Within n formula) : Within n (body formula) :=
  fun clause member => inside clause (List.mem_filter.mp member).1

theorem seed_body_read (formula : Formula) (assignment : Nat → Bool) :
    ((Seed.generate formula).value.holds assignment && formulaRead (body formula) assignment) =
      formulaRead formula assignment := by
  simp only [Seed.generate,EliminateCost.run_result,eliminate_holds,Seed.extract_value]
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases clause with
      | nil => simp [body,Seed.rows,formulaRead,clauseRead,holds,Row.holds,Row.eval,InterferenceProgram.Parity.eval]
      | cons row more =>
          cases more with
          | nil =>
              simpa [body,Seed.rows,formulaRead,clauseRead,holds,Bool.and_assoc] using congrArg (fun value => row.holds assignment && value) ih
          | cons next tail =>
              simpa [body,Seed.rows,formulaRead,holds,Bool.and_assoc,Bool.and_left_comm] using
                congrArg (fun value => clauseRead (row::next::tail) assignment && value) ih

def generate (n : Nat) (formula : Formula) : Cells :=
  let prepared := cleanRun formula
  let initial := Seed.generate prepared.value
  run n (body prepared.value) (AffineCarrier.pack initial.value).value

theorem generate_valid (n : Nat) (formula : Formula) (inside : Within n formula) : Valid n (generate n formula) := by
  have seeded := Seed.generate_valid n (clean formula) (clean_within n formula inside)
  simp only [generate,cleanRun_value]
  exact run_valid n _ _ (AffineCarrier.pack_valid n _ seeded.1 seeded.2)

def decide (n : Nat) (formula : Formula) : Bool := !(generate n formula).isEmpty

theorem decide_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    decide n formula=true ↔ AffineClauseProduct.Satisfiable formula := by
  have seeded := Seed.generate_valid n (clean formula) (clean_within n formula inside)
  rw [decide,AffineCarrier.nonempty_iff n _ (generate_valid n formula inside)]
  simp only [generate,cleanRun_value]
  rw [run_possible n _ (body_within n _ (clean_within n formula inside)) _ (AffineCarrier.pack_valid n _ seeded.1 seeded.2)]
  simp only [AffineCarrier.read_pack,← Bool.and_eq_true]
  simp only [seed_body_read]
  simp only [clean_read]
  constructor
  · rintro ⟨assignment,accepted⟩
    exact ⟨extendAssignment assignment,accepted⟩
  · rintro ⟨assignment,accepted⟩
    exact ⟨(fun i => assignment i.val),(AffineClauseProduct.formula_restrict n formula inside assignment).trans accepted⟩

def components (n : Nat) : Nat → Formula → Bool
  | _,[] => true
  | 0,formula => decide n formula
  | fuel+1,clause::rest =>
      let split := AffineClauseProduct.Cost.grow rest.length [clause] rest
      decide n split.value.1 && components n fuel split.value.2

theorem components_correct (n fuel : Nat) (formula : Formula) (inside : Within n formula) :
    components n fuel formula=true ↔ AffineClauseProduct.Satisfiable formula := by
  induction fuel generalizing formula with
  | zero =>
      cases formula with
      | nil => simp [components,AffineClauseProduct.Satisfiable,formulaRead]
      | cons clause rest => exact decide_correct n (clause::rest) inside
  | succ fuel ih =>
      cases formula with
      | nil => simp [components,AffineClauseProduct.Satisfiable,formulaRead]
      | cons clause rest =>
          have bounds := AffineClauseProduct.grow_within n rest.length [clause] rest inside
          have apart := AffineClauseProduct.grow_apart rest.length [clause] rest (Nat.le_refl _)
          simp only [components,AffineClauseProduct.Cost.grow_value,Bool.and_eq_true]
          rw [decide_correct n _ bounds.1,ih _ bounds.2,← AffineClauseProduct.separated_sat _ _ apart]
          apply exists_congr
          intro assignment
          simp only [formulaRead,List.all_append]
          change (formulaRead (AffineClauseProduct.grow rest.length [clause] rest).1 assignment &&
            formulaRead (AffineClauseProduct.grow rest.length [clause] rest).2 assignment)=true ↔
              formulaRead (clause::rest) assignment=true
          rw [AffineClauseProduct.grow_read]

def decideComponents (n : Nat) (formula : Formula) : Bool := components n formula.length formula

theorem decideComponents_correct (n : Nat) (formula : Formula) (inside : Within n formula) :
    decideComponents n formula=true ↔ AffineClauseProduct.Satisfiable formula := components_correct n _ formula inside

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Future

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineFutureSource
open SaturationMonoid.ComplexityProjection.SATSource.Affine

def solveBasis {n : Nat} (formula : CNFFormula n) (basis : List Row) : Bool :=
  let prepared := AffineClauses.Cost.prepare basis formula
  let image := AtomImage.generate (AffineClauseImage.table prepared.value)
  AffineClauses.Future.decideComponents (AffineClauseImage.width prepared.value) (AffineClauseImage.constraints prepared.value image)

theorem solveBasis_eq_chart {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    solveBasis formula basis = (AffineImageSource.chart formula basis).possible := by
  let prepared := (AffineClauses.Cost.prepare basis formula).value
  have inside := AffineClauses.Cost.prepare_within basis formula
  have bounded := AffineClauseImage.constraints_within (freeIndices n basis).length prepared inside
  apply Bool.eq_iff_iff.mpr
  change AffineClauses.Future.decideComponents _ _ = true ↔ AffineJointImage.possible prepared (AffineJointImage.generate prepared)=true
  rw [AffineClauses.Future.decideComponents_correct _ _ bounded]
  simp only [AffineJointImage.possible,AffineJointImage.generate]
  exact (AffineClauses.Joint.emit_possible _ _ bounded).symm

def decideFormula {n : Nat} (original : CNFFormula n) : Bool :=
  let binary := BinaryRelations.generate original
  match AffineCarrier.tightSeed binary.formula with
  | .contradiction => false
  | .basis basis => solveBasis binary.formula basis

theorem decideFormula_eq_strong {n : Nat} (original : CNFFormula n) :
    decideFormula original = AffineStrongImage.decideFormula original := by
  cases seed : AffineCarrier.tightSeed (BinaryRelations.generate original).formula with
  | contradiction => simp [decideFormula,AffineStrongImage.decideFormula,AffineStrongImage.generate,
      AffineStrongImage.assemble,AffineCarrier.pack,seed]
  | basis basis => simp [decideFormula,AffineStrongImage.decideFormula,AffineStrongImage.generate,
      AffineStrongImage.assemble,AffineCarrier.pack,seed,solveBasis_eq_chart]

theorem decideFormula_correct {n : Nat} (original : CNFFormula n) : decideFormula original=true ↔ CNFSatisfiable original := by
  rw [decideFormula_eq_strong,AffineStrongImage.decideFormula_correct]

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
    decideBits bits=true ↔ ∃ input : Encoding.Input, Encoding.parse bits=some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original,Encoding.decideBits_iff_rootVerify]

end SaturationMonoid.ComplexityProjection.SATSource.AffineFutureSource
