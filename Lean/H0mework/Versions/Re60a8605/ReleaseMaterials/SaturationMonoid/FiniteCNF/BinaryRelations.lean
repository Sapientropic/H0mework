import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.TightFeedback

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.BinaryRelations

open SaturationMonoid.ComplexityProjection.SATSource.Affine

def reject {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) : Bool :=
  match TightFeedback.generate formula (clause.map Propagation.badLiteral) with
  | .contradiction => true
  | .basis _ => false

theorem badRows_value {n : Nat} (clause : CNFClause n) (assignment : Nat → Bool) :
    holds (clause.map Propagation.badLiteral) assignment = !CNFClause.eval clause assignment := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      simp only [holds,List.map_cons,List.all_cons,CNFClause.eval,List.any_cons,
        Propagation.badLiteral_holds,Bool.not_or] at *
      rw [ih]

theorem reject_entails {n : Nat} (formula : CNFFormula n) (clause : CNFClause n)
    (rejected : reject formula clause = true) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : CNFClause.eval clause assignment = true := by
  have same := TightFeedback.generate_holds formula (clause.map Propagation.badLiteral) assignment
  cases generated : TightFeedback.generate formula (clause.map Propagation.badLiteral) with
  | contradiction =>
      rw [generated,Result.holds,badRows_value,accepted] at same
      simpa using same.symm
  | basis basis => simp [reject,generated] at rejected

structure Scan (n : Nat) where
  answer : Option (CNFClause n)
  queries : Nat
  deriving Repr

def scan {n : Nat} (formula : CNFFormula n) : CNFFormula n → Scan n
  | [] => ⟨none,0⟩
  | clause::rest =>
      if clause ∈ formula then scan formula rest
      else if reject formula clause then ⟨some clause,1⟩
      else let next := scan formula rest; ⟨next.answer,next.queries+1⟩

theorem scan_spec {n : Nat} (formula candidates : CNFFormula n) (clause : CNFClause n)
    (found : (scan formula candidates).answer = some clause) :
    clause ∈ candidates ∧ clause ∉ formula ∧ reject formula clause = true := by
  induction candidates with
  | nil => simp [scan] at found
  | cons candidate rest ih =>
      simp only [scan] at found
      split at found
      · exact ⟨List.mem_cons_of_mem _ (ih found).1,(ih found).2⟩
      · rename_i fresh
        split at found
        · rename_i rejected
          have same : candidate = clause := Option.some.inj found
          subst clause
          exact ⟨by simp,fresh,rejected⟩
        · exact ⟨List.mem_cons_of_mem _ (ih found).1,(ih found).2⟩

theorem scan_queries {n : Nat} (formula candidates : CNFFormula n) :
    (scan formula candidates).queries ≤ candidates.length := by
  induction candidates with
  | nil => rfl
  | cons clause rest ih =>
      simp only [scan,List.length_cons]
      split
      · omega
      · split <;> simp only <;> omega

def literals (n : Nat) : List (CNFLiteral n) :=
  (List.finRange n).flatMap fun i => [⟨i,true⟩,⟨i,false⟩]

theorem literals_length (n : Nat) : (literals n).length = 2*n := by
  simp [literals,List.length_flatMap,Nat.mul_comm]

def inventory (n : Nat) : CNFFormula n :=
  (literals n).flatMap fun a => (literals n).map fun b => [a,b]

theorem inventory_length (n : Nat) : (inventory n).length = 4*n*n := by
  simp [inventory,List.length_flatMap,literals_length]
  ring

theorem inventory_clause {n : Nat} (clause : CNFClause n) (member : clause ∈ inventory n) : clause.length = 2 := by
  obtain ⟨_,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp member
  rfl

def pending {n : Nat} (candidates formula : CNFFormula n) : CNFFormula n :=
  candidates.filter fun clause => decide (clause ∉ formula)

theorem pending_length {n : Nat} (candidates formula : CNFFormula n) :
    (pending candidates formula).length ≤ candidates.length := List.length_filter_le _ _

theorem pending_next {n : Nat} (candidates formula : CNFFormula n) (clause : CNFClause n) :
    pending candidates (clause::formula) = (pending candidates formula).filter (fun other => decide (other ≠ clause)) := by
  simp only [pending,List.filter_filter]
  apply List.filter_congr
  intro other
  simp

theorem pending_progress {n : Nat} (candidates formula : CNFFormula n) (clause : CNFClause n)
    (present : clause ∈ candidates) (fresh : clause ∉ formula) :
    (pending candidates (clause::formula)).length < (pending candidates formula).length := by
  rw [pending_next]
  have sub : ((pending candidates formula).filter (fun other => decide (other ≠ clause))).Sublist
      (pending candidates formula) := List.filter_sublist
  have kept : clause ∈ pending candidates formula := by simp [pending,present,fresh]
  have removed : clause ∉ (pending candidates formula).filter (fun other => decide (other ≠ clause)) := by simp
  by_contra! bound
  have same := sub.eq_of_length_le bound
  exact removed (same.symm ▸ kept)

structure Execution (n : Nat) where
  formula : CNFFormula n
  queries : Nat
  deriving Repr

def run {n : Nat} (candidates : CNFFormula n) : Nat → CNFFormula n → Execution n
  | 0, formula => ⟨formula,0⟩
  | fuel+1, formula =>
      let attempt := scan formula candidates
      match attempt.answer with
      | none => ⟨formula,attempt.queries⟩
      | some clause =>
          let next := run candidates fuel (clause::formula)
          ⟨next.formula,attempt.queries+next.queries⟩

theorem run_value {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n)
    (assignment : Nat → Bool) : CNFFormula.eval (run candidates fuel formula).formula assignment =
      CNFFormula.eval formula assignment := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : (scan formula candidates).answer with
      | none => simp [run,found]
      | some clause =>
          simp only [run,found]
          rw [ih]
          have generated := (scan_spec formula candidates clause found).2.2
          change (CNFClause.eval clause assignment && CNFFormula.eval formula assignment) =
            CNFFormula.eval formula assignment
          by_cases accepted : CNFFormula.eval formula assignment = true
          · have added := reject_entails formula clause generated assignment accepted
            rw [added,Bool.true_and]
          · rw [Bool.eq_false_iff.mpr accepted,Bool.and_false]

theorem run_queries {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (run candidates fuel formula).queries ≤ fuel*candidates.length := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      have first := scan_queries formula candidates
      cases found : (scan formula candidates).answer with
      | none => simp only [run,found]; nlinarith
      | some clause =>
          have tail := ih (clause::formula)
          simp only [run,found]
          nlinarith

theorem run_length {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (run candidates fuel formula).formula.length ≤ formula.length+fuel := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      cases found : (scan formula candidates).answer with
      | none => simp [run,found]
      | some clause =>
          have tail := ih (clause::formula)
          simp only [run,found,List.length_cons] at *
          omega

theorem run_literals {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n)
    (bounded : ∀ clause ∈ candidates, clause.length = 2) :
    Extract.literalCount (run candidates fuel formula).formula ≤ Extract.literalCount formula+2*fuel := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      cases found : (scan formula candidates).answer with
      | none => simp [run,found]
      | some clause =>
          have tail := ih (clause::formula)
          have size := bounded clause (scan_spec formula candidates clause found).1
          simp only [Extract.literalCount,List.map_cons,List.sum_cons,size] at tail
          simp only [run,found,Extract.literalCount]
          omega

theorem run_settled {n : Nat} (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n)
    (enough : (pending candidates formula).length ≤ fuel) :
    (scan (run candidates fuel formula).formula candidates).answer = none := by
  induction fuel generalizing formula with
  | zero =>
      cases found : (scan formula candidates).answer with
      | none => exact found
      | some clause =>
          have spec := scan_spec formula candidates clause found
          have present : clause ∈ pending candidates formula := by simp [pending,spec.1,spec.2.1]
          have positive := List.length_pos_of_mem present
          omega
  | succ fuel ih =>
      cases found : (scan formula candidates).answer with
      | none => simp only [run,found]
      | some clause =>
          have spec := scan_spec formula candidates clause found
          have smaller := pending_progress candidates formula clause spec.1 spec.2.1
          simpa only [run,found] using ih (clause::formula) (by omega)

def generate {n : Nat} (formula : CNFFormula n) : Execution n :=
  let candidates := inventory n
  run candidates candidates.length formula

theorem generate_value {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (generate formula).formula assignment = CNFFormula.eval formula assignment :=
  run_value _ _ _ _

theorem generate_queries {n : Nat} (formula : CNFFormula n) : (generate formula).queries ≤ 16*n^4 := by
  have bound := run_queries (inventory n) (inventory n).length formula
  have arithmetic : 4*n*n*(4*n*n) = 16*n^4 := by ring
  simpa only [generate,inventory_length,arithmetic] using bound

theorem generate_length {n : Nat} (formula : CNFFormula n) :
    (generate formula).formula.length ≤ formula.length+4*n*n := by
  simpa only [generate,inventory_length] using run_length (inventory n) (inventory n).length formula

theorem generate_literals {n : Nat} (formula : CNFFormula n) :
    Extract.literalCount (generate formula).formula ≤ Extract.literalCount formula+8*n*n := by
  have bound := run_literals (inventory n) (inventory n).length formula (fun _ hit => inventory_clause _ hit)
  simpa only [generate,inventory_length,← Nat.mul_assoc,Nat.reduceMul] using bound

theorem generate_settled {n : Nat} (formula : CNFFormula n) :
    (scan (generate formula).formula (inventory n)).answer = none :=
  run_settled _ _ _ (pending_length _ _)

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  TightFeedback.decideFormula (generate formula).formula

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula,TightFeedback.decideFormula_correct]
  exact exists_congr (fun assignment => Iff.of_eq (congrArg (· = true) (generate_value formula assignment)))

def read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) : Bool :=
  TightFeedback.read (generate formula).formula assignment

theorem read_value {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read formula assignment = CNFFormula.eval formula assignment := by
  rw [read,TightFeedback.read_value,generate_value]

def sourceAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read formula (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [zeroProjector_apply,sourceAction,read_value]

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

end SaturationMonoid.ComplexityProjection.SATSource.BinaryRelations
