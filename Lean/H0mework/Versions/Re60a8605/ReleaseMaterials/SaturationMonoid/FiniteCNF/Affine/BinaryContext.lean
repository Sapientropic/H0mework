import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Image

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineBinaryContext
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open BinaryRelations (Scan Execution inventory inventory_length inventory_clause pending pending_length pending_progress badRows_value)

def reject {n : Nat} (formula : CNFFormula n) (context : List Row) (clause : CNFClause n) : Bool :=
  match TightFeedback.generate formula (context++clause.map Propagation.badLiteral) with
  | .contradiction => true
  | .basis _ => false

theorem reject_entails {n : Nat} (formula : CNFFormula n) (context : List Row) (clause : CNFClause n)
    (rejected : reject formula context clause=true) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment=true) (allowed : holds context assignment=true) :
    CNFClause.eval clause assignment=true := by
  have same := TightFeedback.generate_holds formula (context++clause.map Propagation.badLiteral) assignment
  cases generated : TightFeedback.generate formula (context++clause.map Propagation.badLiteral) with
  | contradiction =>
      have initial : holds (context++clause.map Propagation.badLiteral) assignment = !CNFClause.eval clause assignment := by
        simp only [holds,List.all_append] at allowed ⊢
        rw [allowed,Bool.true_and]
        exact badRows_value clause assignment
      rw [generated,Result.holds,initial,accepted] at same
      simpa using same.symm
  | basis basis => simp [reject,generated] at rejected

def scan {n : Nat} (formula : CNFFormula n) (context : List Row) : CNFFormula n → Scan n
  | [] => ⟨none,0⟩
  | clause::rest =>
      if clause ∈ formula then scan formula context rest
      else if reject formula context clause then ⟨some clause,1⟩
      else let next := scan formula context rest; ⟨next.answer,next.queries+1⟩

theorem scan_spec {n : Nat} (formula : CNFFormula n) (context : List Row)
    (candidates : CNFFormula n) (clause : CNFClause n)
    (found : (scan formula context candidates).answer=some clause) :
    clause ∈ candidates ∧ clause ∉ formula ∧ reject formula context clause=true := by
  induction candidates with
  | nil => simp [scan] at found
  | cons candidate rest ih =>
      simp only [scan] at found
      split at found
      · exact ⟨List.mem_cons_of_mem _ (ih found).1,(ih found).2⟩
      · rename_i fresh
        split at found
        · rename_i rejected
          have same : candidate=clause := Option.some.inj found
          subst clause
          exact ⟨by simp,fresh,rejected⟩
        · exact ⟨List.mem_cons_of_mem _ (ih found).1,(ih found).2⟩

theorem scan_queries {n : Nat} (formula : CNFFormula n) (context : List Row) (candidates : CNFFormula n) :
    (scan formula context candidates).queries ≤ candidates.length := by
  induction candidates with
  | nil => rfl
  | cons clause rest ih =>
      simp only [scan,List.length_cons]
      split
      · omega
      · split <;> simp only <;> omega

def run {n : Nat} (context : List Row) (candidates : CNFFormula n) : Nat → CNFFormula n → Execution n
  | 0,formula => ⟨formula,0⟩
  | fuel+1,formula =>
      let attempt := scan formula context candidates
      match attempt.answer with
      | none => ⟨formula,attempt.queries⟩
      | some clause =>
          let next := run context candidates fuel (clause::formula)
          ⟨next.formula,attempt.queries+next.queries⟩

theorem run_value {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat)
    (formula : CNFFormula n) (assignment : Nat → Bool) :
    (CNFFormula.eval (run context candidates fuel formula).formula assignment && holds context assignment) =
      (CNFFormula.eval formula assignment && holds context assignment) := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : (scan formula context candidates).answer with
      | none => simp [run,found]
      | some clause =>
          simp only [run,found]
          rw [ih]
          have generated := (scan_spec formula context candidates clause found).2.2
          change ((CNFClause.eval clause assignment && CNFFormula.eval formula assignment) && holds context assignment) = _
          by_cases accepted : CNFFormula.eval formula assignment=true
          · by_cases allowed : holds context assignment=true
            · have added := reject_entails formula context clause generated assignment accepted allowed
              rw [added,Bool.true_and]
            · rw [Bool.eq_false_iff.mpr allowed]
              simp
          · rw [Bool.eq_false_iff.mpr accepted]
            simp

theorem run_queries {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (run context candidates fuel formula).queries ≤ fuel*candidates.length := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      have first := scan_queries formula context candidates
      cases found : (scan formula context candidates).answer with
      | none => simp only [run,found]; nlinarith
      | some clause =>
          have tail := ih (clause::formula)
          simp only [run,found]
          nlinarith

theorem run_length {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (run context candidates fuel formula).formula.length ≤ formula.length+fuel := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      cases found : (scan formula context candidates).answer with
      | none => simp [run,found]
      | some clause =>
          have tail := ih (clause::formula)
          simp only [run,found,List.length_cons] at *
          omega

theorem run_literals {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n)
    (bounded : ∀ clause ∈ candidates, clause.length=2) :
    Extract.literalCount (run context candidates fuel formula).formula ≤ Extract.literalCount formula+2*fuel := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      cases found : (scan formula context candidates).answer with
      | none => simp [run,found]
      | some clause =>
          have tail := ih (clause::formula)
          have size := bounded clause (scan_spec formula context candidates clause found).1
          simp only [Extract.literalCount,List.map_cons,List.sum_cons,size] at tail
          simp only [run,found,Extract.literalCount]
          omega

theorem run_settled {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n)
    (enough : (pending candidates formula).length ≤ fuel) :
    (scan (run context candidates fuel formula).formula context candidates).answer=none := by
  induction fuel generalizing formula with
  | zero =>
      cases found : (scan formula context candidates).answer with
      | none => exact found
      | some clause =>
          have spec := scan_spec formula context candidates clause found
          have present : clause ∈ pending candidates formula := by simp [pending,spec.1,spec.2.1]
          have positive := List.length_pos_of_mem present
          omega
  | succ fuel ih =>
      cases found : (scan formula context candidates).answer with
      | none => simp only [run,found]
      | some clause =>
          have spec := scan_spec formula context candidates clause found
          have smaller := pending_progress candidates formula clause spec.1 spec.2.1
          simpa only [run,found] using ih (clause::formula) (by omega)

def generate {n : Nat} (formula : CNFFormula n) (context : List Row) : Execution n :=
  let candidates := inventory n
  run context candidates candidates.length formula

theorem generate_value {n : Nat} (formula : CNFFormula n) (context : List Row) (assignment : Nat → Bool) :
    (CNFFormula.eval (generate formula context).formula assignment && holds context assignment) =
      (CNFFormula.eval formula assignment && holds context assignment) := run_value _ _ _ _ _

theorem generate_queries {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (generate formula context).queries ≤ 16*n^4 := by
  have bound := run_queries context (inventory n) (inventory n).length formula
  have arithmetic : 4*n*n*(4*n*n)=16*n^4 := by ring
  simpa only [generate,inventory_length,arithmetic] using bound

theorem generate_length {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (generate formula context).formula.length ≤ formula.length+4*n*n := by
  simpa only [generate,inventory_length] using run_length context (inventory n) (inventory n).length formula

theorem generate_literals {n : Nat} (formula : CNFFormula n) (context : List Row) :
    Extract.literalCount (generate formula context).formula ≤ Extract.literalCount formula+8*n*n := by
  have bound := run_literals context (inventory n) (inventory n).length formula (fun _ hit => inventory_clause _ hit)
  simpa only [generate,inventory_length,← Nat.mul_assoc,Nat.reduceMul] using bound

theorem generate_settled {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (scan (generate formula context).formula context (inventory n)).answer=none :=
  run_settled _ _ _ _ (pending_length _ _)

/-- The same fixed context participates in the final strong row generation. -/
def seed {n : Nat} (formula : CNFFormula n) (context : List Row) : Result :=
  let enhanced := generate formula context
  TightFeedback.generate enhanced.formula
    (context++Extract.extract enhanced.formula++(CapacityMatching.RowCost.prepare enhanced.formula).value)

theorem seed_valid {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context) :
    (seed formula context).triangular ∧ (seed formula context).within n := by
  let enhanced := (generate formula context).formula
  have rows : RowsWithin n (context++Extract.extract enhanced++(CapacityMatching.RowCost.prepare enhanced).value) := by
    intro row member
    rcases List.mem_append.mp member with earlier | learned
    · rcases List.mem_append.mp earlier with original | extracted
      · exact inside row original
      · exact extract_rowsWithin enhanced row extracted
    · rw [CapacityMatching.RowCost.prepare_value] at learned
      exact CapacityMatching.SourceTight.prepare_within enhanced row learned
  exact (TightFeedback.generate_invariants enhanced _ rows).symm

theorem seed_entails {n : Nat} (formula : CNFFormula n) (context : List Row) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment=true) (allowed : holds context assignment=true) :
    (seed formula context).holds assignment=true := by
  let enhanced := (generate formula context).formula
  have accepted' : CNFFormula.eval enhanced assignment=true := by
    have same := generate_value formula context assignment
    simpa only [allowed,Bool.and_true,accepted] using same
  have extracted := Extract.extract_entails enhanced assignment accepted'
  have matched : holds (CapacityMatching.RowCost.prepare enhanced).value assignment=true := by
    simpa only [CapacityMatching.RowCost.prepare_value] using
      CapacityMatching.SourceTight.prepare_entails enhanced assignment accepted'
  have initial : holds (context++Extract.extract enhanced++(CapacityMatching.RowCost.prepare enhanced).value) assignment=true := by
    simp only [holds,List.all_append] at allowed extracted matched ⊢
    rw [allowed,extracted,matched]
    rfl
  have same := TightFeedback.generate_holds enhanced
    (context++Extract.extract enhanced++(CapacityMatching.RowCost.prepare enhanced).value) assignment
  simpa only [seed,accepted',initial,Bool.true_and] using same

theorem seed_preserves {n : Nat} (formula : CNFFormula n) (context : List Row) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && holds context assignment && (seed formula context).holds assignment) =
      (CNFFormula.eval formula assignment && holds context assignment) := by
  by_cases accepted : CNFFormula.eval formula assignment=true
  · by_cases allowed : holds context assignment=true
    · rw [seed_entails formula context assignment accepted allowed,Bool.and_true]
    · rw [Bool.eq_false_iff.mpr allowed]
      simp
  · rw [Bool.eq_false_iff.mpr accepted]
    simp

theorem source_entails (formula : AffineClauses.Formula) (clause : CNFClause (AffineClauseImage.width formula))
    (rejected : reject (AffineClauseImage.atomFormula formula)
      (AtomImage.generate (AffineClauseImage.table formula)).kernel clause=true)
    (input : Nat → Bool) (accepted : AffineClauses.formulaRead formula input=true) :
    CNFClause.eval clause (Gates.coordinate (AffineClauseImage.table formula) input)=true :=
  reject_entails _ _ clause rejected _ ((AffineClauseImage.atomFormula_read formula input).trans accepted)
    ((AtomImage.image_iff_kernel _ _).mp ⟨input,fun _ => rfl⟩)

theorem source_value (formula : AffineClauses.Formula) (input : Nat → Bool) :
    CNFFormula.eval (generate (AffineClauseImage.atomFormula formula)
      (AtomImage.generate (AffineClauseImage.table formula)).kernel).formula
      (Gates.coordinate (AffineClauseImage.table formula) input) = AffineClauses.formulaRead formula input := by
  have realized := (AtomImage.image_iff_kernel (AffineClauseImage.table formula) _).mp ⟨input,fun _ => rfl⟩
  have same := generate_value (AffineClauseImage.atomFormula formula)
    (AtomImage.generate (AffineClauseImage.table formula)).kernel (Gates.coordinate (AffineClauseImage.table formula) input)
  simpa only [realized,Bool.and_true,AffineClauseImage.atomFormula_read] using same

theorem source_seed_entails (formula : AffineClauses.Formula) (input : Nat → Bool)
    (accepted : AffineClauses.formulaRead formula input=true) :
    (seed (AffineClauseImage.atomFormula formula) (AtomImage.generate (AffineClauseImage.table formula)).kernel).holds
      (Gates.coordinate (AffineClauseImage.table formula) input)=true :=
  seed_entails _ _ _ ((AffineClauseImage.atomFormula_read formula input).trans accepted)
    ((AtomImage.image_iff_kernel _ _).mp ⟨input,fun _ => rfl⟩)

theorem source_seed_read (formula : AffineClauses.Formula) (input : Nat → Bool) :
    (AffineClauses.formulaRead formula input &&
      (seed (AffineClauseImage.atomFormula formula) (AtomImage.generate (AffineClauseImage.table formula)).kernel).holds
        (Gates.coordinate (AffineClauseImage.table formula) input)) = AffineClauses.formulaRead formula input := by
  by_cases accepted : AffineClauses.formulaRead formula input=true
  · rw [source_seed_entails formula input accepted,Bool.and_true]
  · rw [Bool.eq_false_iff.mpr accepted]
    rfl

end SaturationMonoid.ComplexityProjection.SATSource.AffineBinaryContext
