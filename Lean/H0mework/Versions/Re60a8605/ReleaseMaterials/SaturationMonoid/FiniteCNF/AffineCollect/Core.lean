import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Union
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCarrier.Cost

/-!
An actual collector for the positive affine carrier. Every proposal constructs
both coordinate tables, the common source and its kernel once, then checks that
same generated hull. Conservative complete-record copying is charged alongside
the paid source-operation ledgers. These are source units, not TM microsteps;
evaluating the counters themselves has a separate cost.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineCollect

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated read storage cellSize)
open InterferenceProgram

def tableSize (table : Array Row) : Nat := CapacityMatching.RowCost.rowsCells table.toList+1

def coordinateWork (n : Nat) (basis : List Row) : Nat :=
  Table.coordinatesVisits n basis+
    8*(n+basis.length+Gates.rowTerms basis+1)*(AffineCarrier.Cost.cellBound n+1)+2*cellSize basis+3

def imageWorkspace (n : Nat) : Nat := (2*n+1)*(2*n+3)+n*(n+2)+4*n+4

structure Merge where
  value : Option (List Row)
  checks : Nat
  visits : Nat
  deriving Repr

def merge (n : Nat) (left right : List Row) : Merge :=
  let leftTable := Table.coordinates n left
  let rightTable := Table.coordinates n right
  let source := BranchImage.table n leftTable rightTable
  let image := AtomImage.generate source
  let reduced := EliminateCost.run image.kernel
  let tested := Union.check reduced.result left right
  let value := match reduced.result with
    | .contradiction => none
    | .basis basis => if tested.accepted then some basis else none
  ⟨value,tested.calls,
    coordinateWork n left+coordinateWork n right+
      (n+1)*(8*(tableSize leftTable+tableSize rightTable+tableSize source)+8)+
      (AtomImage.generateVisits source+1)*(8*imageWorkspace n+8)+
      (reduced.cells+tested.cells+2)*(8*AffineCarrier.Cost.cellBound n+8)+
      2*(cellSize left+cellSize right+AffineCarrier.resultSize reduced.result)+12⟩

theorem merge_value (n : Nat) (left right : List Row) : (merge n left right).value = (Union.merge n left right).value := by
  simp only [merge,EliminateCost.run_result,Union.merge,BranchImage.join,BranchImage.common,BranchImage.source]
  rfl

theorem merge_checks (n : Nat) (left right : List Row) : (merge n left right).checks = (Union.merge n left right).calls := by
  simp only [merge,EliminateCost.run_result,Union.merge,BranchImage.join,BranchImage.common,BranchImage.source]

theorem merge_holds (n : Nat) (left right current : List Row)
    (leftValid : Triangular left ∧ RowsWithin n left) (rightValid : Triangular right ∧ RowsWithin n right)
    (found : (merge n left right).value = some current) (assignment : Nat → Bool) :
    holds current assignment = (holds left assignment || holds right assignment) :=
  Union.merge_holds n left right current leftValid.2 leftValid.1 rightValid.2 rightValid.1
    (merge_value n left right ▸ found) assignment

theorem merge_valid (n : Nat) (left right current : List Row)
    (leftValid : Triangular left ∧ RowsWithin n left) (rightValid : Triangular right ∧ RowsWithin n right)
    (found : (merge n left right).value = some current) : Triangular current ∧ RowsWithin n current :=
  (Union.merge_valid n left right current leftValid.2 leftValid.1 rightValid.2 rightValid.1
    (merge_value n left right ▸ found)).symm

@[simp] theorem read_cons (basis : List Row) (rest : Cells) (assignment : Nat → Bool) :
    read (basis::rest) assignment = (holds basis assignment || read rest assignment) := rfl

theorem prepend_valid (n : Nat) (basis : List Row) (rest : Cells)
    (first : Triangular basis ∧ RowsWithin n basis) (tail : Valid n rest) : Valid n (basis::rest) := by
  intro row member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · exact tail row member

theorem prepend_separated (basis : List Row) (rest : Cells) (tail : Separated rest)
    (apart : ∀ assignment, (holds basis assignment && read rest assignment) = false) : Separated (basis::rest) := by
  apply AffineCarrier.separated_append [basis] rest (by simp [Separated]) tail
  intro assignment
  simpa only [read_cons,AffineCarrier.read_nil,Bool.or_false] using apart assignment

theorem swap_separated (first second : List Row) (rest : Cells)
    (separate : Separated (first::second::rest)) : Separated (second::first::rest) := by
  have head := List.pairwise_cons.mp separate
  have tail := List.pairwise_cons.mp head.2
  apply List.pairwise_cons.mpr
  refine ⟨?_,List.pairwise_cons.mpr ⟨?_,tail.2⟩⟩
  · intro other member assignment
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [Bool.and_comm] using head.1 second (by simp) assignment
    · exact tail.1 other member assignment
  · intro other member
    exact head.1 other (by simp [member])

def answerSize : Option Cells → Nat
  | none => 1
  | some cells => storage cells+1

structure Search where
  answer : Option Cells
  attempts : Nat
  visits : Nat
  deriving Repr

def tryLeft (n : Nat) (left : List Row) : Cells → Search
  | [] => ⟨none,0,1⟩
  | right::rest =>
      let tested := merge n left right
      match tested.value with
      | some current => ⟨some (current::rest),1,tested.visits+2*(cellSize current+storage rest)+5⟩
      | none =>
          let next := tryLeft n left rest
          ⟨next.answer.map (right::·),next.attempts+1,
            tested.visits+next.visits+2*cellSize right+2*answerSize next.answer+7⟩

theorem tryLeft_spec (n : Nat) (left : List Row) (rest output : Cells)
    (leftValid : Triangular left ∧ RowsWithin n left) (restValid : Valid n rest)
    (found : (tryLeft n left rest).answer = some output) :
    Valid n output ∧ output.length = rest.length ∧
      (∀ assignment, read output assignment = read (left::rest) assignment) ∧
      (Separated (left::rest) → Separated output) := by
  induction rest generalizing output with
  | nil => simp [tryLeft] at found
  | cons right rest ih =>
      have rightValid := restValid right (by simp)
      have tailValid : Valid n rest := fun other member => restValid other (by simp [member])
      cases tested : (merge n left right).value with
      | some current =>
          have same : current::rest = output := by simpa only [tryLeft,tested,Option.some.injEq] using found
          subst output
          have currentValid := merge_valid n left right current leftValid rightValid tested
          refine ⟨prepend_valid n current rest currentValid tailValid,rfl,?_,?_⟩
          · intro assignment
            simp only [read_cons,merge_holds n left right current leftValid rightValid tested assignment,Bool.or_assoc]
          · intro separate
            have tailSeparated := (List.pairwise_cons.mp (List.pairwise_cons.mp separate).2).2
            apply prepend_separated current rest tailSeparated
            intro assignment
            have first := AffineCarrier.separated_cons left (right::rest) separate assignment
            have second := AffineCarrier.separated_cons right rest (List.pairwise_cons.mp separate).2 assignment
            rw [merge_holds n left right current leftValid rightValid tested assignment]
            simp only [read_cons] at first
            cases a : holds left assignment <;> cases b : holds right assignment <;>
              cases c : read rest assignment <;> simp_all
      | none =>
          cases next : (tryLeft n left rest).answer with
          | none => simp [tryLeft,tested,next] at found
          | some generated =>
              have same : right::generated = output := by simpa only [tryLeft,tested,next,Option.map_some,Option.some.injEq] using found
              subst output
              obtain ⟨valid,length,reads,separated⟩ := ih generated tailValid next
              refine ⟨prepend_valid n right generated rightValid valid,by simp [length],?_,?_⟩
              · intro assignment
                simp only [read_cons,reads]
                exact Bool.or_left_comm _ _ _
              · intro original
                have swapped := swap_separated left right rest original
                apply prepend_separated right generated (separated (List.pairwise_cons.mp swapped).2)
                intro assignment
                rw [reads]
                exact AffineCarrier.separated_cons right (left::rest) swapped assignment

def scan (n : Nat) : Cells → Search
  | [] => ⟨none,0,1⟩
  | left::rest =>
      let first := tryLeft n left rest
      match first.answer with
      | some output => ⟨some output,first.attempts,first.visits+2*storage output+4⟩
      | none =>
          let next := scan n rest
          ⟨next.answer.map (left::·),first.attempts+next.attempts,
            first.visits+next.visits+2*cellSize left+2*answerSize next.answer+7⟩

theorem scan_spec (n : Nat) (cells output : Cells) (valid : Valid n cells) (found : (scan n cells).answer = some output) :
    Valid n output ∧ output.length+1 = cells.length ∧
      (∀ assignment, read output assignment = read cells assignment) ∧ (Separated cells → Separated output) := by
  induction cells generalizing output with
  | nil => simp [scan] at found
  | cons left rest ih =>
      have leftValid := valid left (by simp)
      have restValid : Valid n rest := fun other member => valid other (by simp [member])
      cases first : (tryLeft n left rest).answer with
      | some generated =>
          have same : generated=output := by simpa only [scan,first,Option.some.injEq] using found
          subst output
          obtain ⟨nextValid,length,reads,separated⟩ := tryLeft_spec n left rest generated leftValid restValid first
          exact ⟨nextValid,by simp [length],reads,separated⟩
      | none =>
          cases next : (scan n rest).answer with
          | none => simp [scan,first,next] at found
          | some generated =>
              have same : left::generated=output := by simpa only [scan,first,next,Option.map_some,Option.some.injEq] using found
              subst output
              obtain ⟨nextValid,length,reads,separated⟩ := ih generated restValid next
              refine ⟨prepend_valid n left generated leftValid nextValid,by simp only [List.length_cons]; omega,?_,?_⟩
              · intro assignment
                simp only [read_cons,reads]
              · intro original
                apply prepend_separated left generated (separated (List.pairwise_cons.mp original).2)
                intro assignment
                rw [reads]
                exact AffineCarrier.separated_cons left rest original assignment

structure Execution where
  value : Cells
  merges : Nat
  attempts : Nat
  visits : Nat
  deriving Repr

def iterate (n : Nat) : Nat → Cells → Execution
  | 0,cells => ⟨cells,0,0,2*storage cells+1⟩
  | fuel+1,cells =>
      let first := scan n cells
      match first.answer with
      | none => ⟨cells,0,first.attempts,first.visits+2*storage cells+3⟩
      | some next =>
          let tail := iterate n fuel next
          ⟨tail.value,tail.merges+1,first.attempts+tail.attempts,first.visits+tail.visits+2⟩

theorem iterate_spec (n fuel : Nat) (cells : Cells) (valid : Valid n cells) :
    Valid n (iterate n fuel cells).value ∧ (iterate n fuel cells).value.length ≤ cells.length ∧
      (∀ assignment, read (iterate n fuel cells).value assignment = read cells assignment) ∧
      (Separated cells → Separated (iterate n fuel cells).value) := by
  induction fuel generalizing cells with
  | zero => exact ⟨valid,Nat.le_refl _,fun _ => rfl,id⟩
  | succ fuel ih =>
      cases first : (scan n cells).answer with
      | none =>
          rw [iterate,first]
          exact ⟨valid,Nat.le_refl _,fun _ => rfl,id⟩
      | some next =>
          obtain ⟨nextValid,length,reads,separated⟩ := scan_spec n cells next valid first
          obtain ⟨finalValid,shorter,finalReads,finalSeparated⟩ := ih next nextValid
          simp only [iterate,first]
          exact ⟨finalValid,by omega,fun assignment => (finalReads assignment).trans (reads assignment),finalSeparated ∘ separated⟩

theorem iterate_settled (n fuel : Nat) (cells : Cells) (valid : Valid n cells) (enough : cells.length ≤ fuel) :
    (scan n (iterate n fuel cells).value).answer = none := by
  induction fuel generalizing cells with
  | zero =>
      have empty : cells=[] := List.eq_nil_of_length_eq_zero (by omega)
      subst cells
      rfl
  | succ fuel ih =>
      cases first : (scan n cells).answer with
      | none => simp only [iterate,first]
      | some next =>
          have nextValid := scan_spec n cells next valid first
          simpa only [iterate,first] using ih next nextValid.1 (by omega)

def collect (n : Nat) (cells : Cells) : Execution := iterate n cells.length cells

theorem collect_valid (n : Nat) (cells : Cells) (valid : Valid n cells) : Valid n (collect n cells).value :=
  (iterate_spec n cells.length cells valid).1

theorem collect_length (n : Nat) (cells : Cells) (valid : Valid n cells) : (collect n cells).value.length ≤ cells.length :=
  (iterate_spec n cells.length cells valid).2.1

theorem collect_read (n : Nat) (cells : Cells) (valid : Valid n cells) (assignment : Nat → Bool) :
    read (collect n cells).value assignment = read cells assignment := (iterate_spec n cells.length cells valid).2.2.1 assignment

theorem collect_separated (n : Nat) (cells : Cells) (valid : Valid n cells) (separate : Separated cells) :
    Separated (collect n cells).value := (iterate_spec n cells.length cells valid).2.2.2 separate

theorem collect_settled (n : Nat) (cells : Cells) (valid : Valid n cells) : (scan n (collect n cells).value).answer = none :=
  iterate_settled n cells.length cells valid (Nat.le_refl _)

theorem tryLeft_none (n : Nat) (left : List Row) (rest : Cells) :
    (tryLeft n left rest).answer = none ↔ ∀ right ∈ rest, (merge n left right).value = none := by
  induction rest with
  | nil => simp [tryLeft]
  | cons right rest ih =>
      cases tested : (merge n left right).value <;> simp [tryLeft,tested,ih]

theorem scan_none (n : Nat) (cells : Cells) :
    (scan n cells).answer = none ↔ cells.Pairwise (fun left right => (merge n left right).value = none) := by
  induction cells with
  | nil => simp [scan]
  | cons left rest ih =>
      cases first : (tryLeft n left rest).answer with
      | none =>
          have rejected := (tryLeft_none n left rest).mp first
          simp [scan,first,List.pairwise_cons,ih]
          exact fun _ => rejected
      | some output =>
          have present : ¬ ∀ right ∈ rest, (merge n left right).value = none := by
            intro all
            have absent := (tryLeft_none n left rest).mpr all
            simp [first] at absent
          simp [scan,first,List.pairwise_cons,present]

theorem collect_fixed (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (collect n cells).value.Pairwise (fun left right => (merge n left right).value = none) :=
  (scan_none n _).mp (collect_settled n cells valid)

def run {n : Nat} : CNFFormula n → Cells → Execution
  | [],cells => ⟨cells,0,0,2*storage cells+1⟩
  | clause::rest,cells =>
      let cut := AffineCarrier.clauseAction clause cells
      let shared := collect n cut.value
      let next := run rest shared.value
      ⟨next.value,shared.merges+next.merges,shared.attempts+next.attempts,
        cut.visits+shared.visits+next.visits+3⟩

theorem run_valid {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) :
    Valid n (run formula cells).value := by
  induction formula generalizing cells with
  | nil => exact valid
  | cons clause rest ih => exact ih _ (collect_valid n _ (AffineCarrier.clauseAction_valid clause cells valid))

theorem run_read {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) (assignment : Nat → Bool) :
    read (run formula cells).value assignment = (read cells assignment && CNFFormula.eval formula assignment) := by
  induction formula generalizing cells with
  | nil => simp [run,CNFFormula.eval]
  | cons clause rest ih =>
      have cutValid := AffineCarrier.clauseAction_valid clause cells valid
      simp only [run,ih _ (collect_valid n _ cutValid),collect_read n _ cutValid,
        AffineCarrier.clauseAction_read,CNFFormula.eval,List.all_cons,Bool.and_assoc]

theorem run_separated {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) (separate : Separated cells) :
    Separated (run formula cells).value := by
  induction formula generalizing cells with
  | nil => exact separate
  | cons clause rest ih =>
      have cutValid := AffineCarrier.clauseAction_valid clause cells valid
      have cutSeparated := AffineCarrier.clauseAction_separated clause cells separate
      exact ih _ (collect_valid n _ cutValid) (collect_separated n _ cutValid cutSeparated)

def generate {n : Nat} (formula : CNFFormula n) : Execution :=
  let initial := AffineCarrier.seed formula
  let final := run formula initial.value
  ⟨final.value,final.merges,final.attempts,initial.visits+final.visits+2⟩

theorem generate_valid {n : Nat} (formula : CNFFormula n) : Valid n (generate formula).value :=
  run_valid formula _ (AffineCarrier.seed_valid formula)

theorem generate_read {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read (generate formula).value assignment = CNFFormula.eval formula assignment := by
  change read (run formula (AffineCarrier.seed formula).value).value assignment = _
  rw [run_read formula _ (AffineCarrier.seed_valid formula)]
  by_cases accepted : CNFFormula.eval formula assignment = true
  · rw [AffineCarrier.seed_entails formula assignment accepted,accepted]
    rfl
  · simp [Bool.eq_false_iff.mpr accepted]

theorem generate_separated {n : Nat} (formula : CNFFormula n) : Separated (generate formula).value := by
  apply run_separated formula _ (AffineCarrier.seed_valid formula)
  rw [AffineCarrier.seed_result]
  exact AffineCarrier.pack_separated _

theorem run_fixed {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells)
    (fixed : cells.Pairwise (fun left right => (merge n left right).value = none)) :
    (run formula cells).value.Pairwise (fun left right => (merge n left right).value = none) := by
  induction formula generalizing cells with
  | nil => exact fixed
  | cons clause rest ih =>
      have cutValid := AffineCarrier.clauseAction_valid clause cells valid
      exact ih _ (collect_valid n _ cutValid) (collect_fixed n _ cutValid)

theorem generate_fixed {n : Nat} (formula : CNFFormula n) :
    (generate formula).value.Pairwise (fun left right => (merge n left right).value = none) := by
  apply run_fixed formula _ (AffineCarrier.seed_valid formula)
  rw [AffineCarrier.seed_result]
  cases eliminateFrom (eliminate (Extract.extract formula)) (CapacityMatching.SourceTight.prepare formula) <;>
    simp [AffineCarrier.pack]

theorem generate_image {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    (∃ parameter : AffineCarrier.Parameters n (generate formula).value,
      AffineCarrier.lift n (generate formula).value parameter = assignment) ↔
        CNFFormula.eval formula (extendAssignment assignment) = true := by
  rw [AffineCarrier.lift_image n _ (generate_valid formula),generate_read]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool := !(generate formula).value.isEmpty

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) : decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula,AffineCarrier.nonempty_iff n _ (generate_valid formula)]
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

end SaturationMonoid.ComplexityProjection.SATSource.AffineCollect
