import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Capacity

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.CapacityFeedback

/-- Recompute the capacity rows on the current source forms, then decode the same rows. -/
def learn {n : Nat} (basis : List Row) (formula : CNFFormula n) : List Row :=
  let source := Atoms.data basis formula
  (Capacity.relations (Subsumption.reduce (Atoms.compile source))).map (Atoms.decode source)

theorem learn_entails {n : Nat} (basis : List Row) (formula : CNFFormula n) (assignment : Nat → Bool)
    (relations : holds basis assignment = true) (accepted : CNFFormula.eval formula assignment = true) :
    holds (learn basis formula) assignment = true := by
  have source := (Atoms.ofFormula_value basis formula assignment relations).trans accepted
  have generated := Capacity.relations_entails (Atoms.ofFormula basis formula)
    (Atoms.read (Atoms.data basis formula) assignment) source
  apply (holds_iff _ _).mpr
  intro row member
  obtain ⟨original,hit,rfl⟩ := List.mem_map.mp member
  rw [Atoms.decode_holds]
  exact (holds_iff _ _).mp generated original hit

theorem learn_valid {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    ∀ row ∈ learn basis formula, Table.RowValid n row := by
  intro row member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact Table.combine_valid n (Atoms.table (Atoms.data basis formula))
    (Atoms.table_valid n _ (Atoms.data_valid basis inside formula)) original.vars _
    (by simp [Table.RowValid,InterferenceProgram.Parity.Within])

def advance {n : Nat} (formula : CNFFormula n) : Result → Result
  | .contradiction => .contradiction
  | .basis basis => eliminateFrom (.basis basis) (learn basis formula)

theorem advance_holds {n : Nat} (formula : CNFFormula n) (result : Result) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (advance formula result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  cases result with
  | contradiction => rfl
  | basis basis =>
      rw [advance,eliminateFrom_holds]
      by_cases accepted : CNFFormula.eval formula assignment = true
      · by_cases relations : holds basis assignment = true
        · have generated := learn_entails basis formula assignment relations accepted
          simp [Result.holds,relations,generated]
        · simp [Result.holds,relations]
      · simp [accepted]

theorem advance_invariants {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (advance formula result).within n ∧ (advance formula result).triangular := by
  cases result with
  | contradiction => exact ⟨trivial,trivial⟩
  | basis basis =>
      dsimp only [advance]
      have rowsInside : RowsWithin n (learn basis formula) :=
        fun row member => (learn_valid basis inside formula row member).2
      generalize generated : learn basis formula = rows at *
      constructor
      · exact eliminateFrom_within n (.basis basis) inside rows rowsInside
      · exact eliminateFrom_triangular (.basis basis) triangular rows

theorem advance_progress {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (changed : advance formula result ≠ result) :
    Propagation.remaining n (advance formula result) < Propagation.remaining n result := by
  cases result with
  | contradiction => exact False.elim (changed rfl)
  | basis basis =>
      have rank := basis_length_le n basis triangular inside
      cases next : advance formula (.basis basis) with
      | contradiction => simp only [Propagation.remaining]; omega
      | basis current =>
          have pref := Atoms.eliminateFrom_prefix basis (learn basis formula) current next
          have apart : basis ≠ current := fun same => changed (by simpa only [same] using next)
          have growth : basis.length < current.length := by
            by_contra! absent
            exact apart (pref.eq_of_length_le absent)
          simp only [Propagation.remaining]
          omega

def step {n : Nat} (formula : CNFFormula n) (result : Result) : Result :=
  advance formula (JointFeedback.step formula result)

theorem step_holds {n : Nat} (formula : CNFFormula n) (result : Result) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (step formula result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  rw [step,advance_holds,JointFeedback.step_holds]

theorem step_invariants {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (step formula result).within n ∧ (step formula result).triangular := by
  have first := JointFeedback.step_invariants formula result inside triangular
  exact advance_invariants formula _ first.1 first.2

theorem advance_remaining {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    Propagation.remaining n (advance formula result) ≤ Propagation.remaining n result := by
  by_cases fixed : advance formula result = result
  · rw [fixed]
  · exact (advance_progress formula result inside triangular fixed).le

theorem step_progress {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (changed : step formula result ≠ result) :
    Propagation.remaining n (step formula result) < Propagation.remaining n result := by
  by_cases fixed : JointFeedback.step formula result = result
  · simpa only [step,fixed] using advance_progress formula result inside triangular
      (by simpa only [step,fixed] using changed)
  · have first := JointFeedback.step_progress formula result inside triangular fixed
    have valid := JointFeedback.step_invariants formula result inside triangular
    exact lt_of_le_of_lt (advance_remaining formula _ valid.1 valid.2) first

theorem step_fixed {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    step formula result = result ↔ JointFeedback.step formula result = result ∧ advance formula result = result := by
  constructor
  · intro fixed
    have first : JointFeedback.step formula result = result := by
      by_contra changed
      have strict := JointFeedback.step_progress formula result inside triangular changed
      have valid := JointFeedback.step_invariants formula result inside triangular
      have bound := advance_remaining formula _ valid.1 valid.2
      change Propagation.remaining n (step formula result) ≤ _ at bound
      rw [fixed] at bound
      omega
    exact ⟨first,by simpa only [step,first] using fixed⟩
  · rintro ⟨first,second⟩
    simp only [step,first,second]

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Result
  | 0, result => result
  | fuel+1, result => iterate formula fuel (step formula result)

theorem iterate_invariants {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (iterate formula fuel result).within n ∧ (iterate formula fuel result).triangular := by
  induction fuel generalizing result with
  | zero => exact ⟨inside,triangular⟩
  | succ fuel ih =>
      have valid := step_invariants formula result inside triangular
      exact ih _ valid.1 valid.2

theorem iterate_holds {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (iterate formula fuel result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => exact (ih (step formula result)).trans (step_holds formula result assignment)

theorem iterate_fixed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (fixed : step formula result = result) : iterate formula fuel result = result := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate,fixed] using ih

theorem iterate_settled {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (enough : Propagation.remaining n result ≤ fuel) :
    step formula (iterate formula fuel result) = iterate formula fuel result := by
  induction fuel generalizing result with
  | zero =>
      cases result with
      | contradiction => rfl
      | basis basis =>
          have rank := basis_length_le n basis triangular inside
          simp only [Propagation.remaining] at enough
          omega
  | succ fuel ih =>
      by_cases fixed : step formula result = result
      · rw [iterate_fixed formula (fuel+1) result fixed]
        exact fixed
      · have decrease := step_progress formula result inside triangular fixed
        have valid := step_invariants formula result inside triangular
        exact ih _ valid.1 valid.2 (by omega)

def generate {n : Nat} (formula : CNFFormula n) (rows : List Row) : Result :=
  iterate formula (n+1) (eliminate rows)

theorem generate_invariants {n : Nat} (formula : CNFFormula n) (rows : List Row) (inside : RowsWithin n rows) :
    (generate formula rows).within n ∧ (generate formula rows).triangular :=
  iterate_invariants formula (n+1) _ (eliminate_within n rows inside) (eliminate_triangular rows)

theorem generate_holds {n : Nat} (formula : CNFFormula n) (rows : List Row) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (generate formula rows).holds assignment) =
      (CNFFormula.eval formula assignment && holds rows assignment) := by
  rw [generate,iterate_holds,eliminate_holds]

theorem generate_settled {n : Nat} (formula : CNFFormula n) (rows : List Row) (inside : RowsWithin n rows) :
    Propagation.update formula (generate formula rows) = generate formula rows ∧
      Atoms.advance formula (generate formula rows) = generate formula rows ∧
      advance formula (generate formula rows) = generate formula rows := by
  have valid := generate_invariants formula rows inside
  have fixed : step formula (generate formula rows) = generate formula rows :=
    iterate_settled formula (n+1) _ (eliminate_within n rows inside) (eliminate_triangular rows)
      (by cases eliminate rows <;> simp [Propagation.remaining])
  have phases := (step_fixed formula _ valid.1 valid.2).mp fixed
  have first := (JointFeedback.step_fixed_iff formula _ valid.1 valid.2).mp phases.1
  exact ⟨first.1,first.2,phases.2⟩

def decideRows {n : Nat} (formula : CNFFormula n) (rows : List Row) : Bool :=
  match generate formula rows with
  | .contradiction => false
  | .basis basis => ConditionalPivot.decideRows formula basis

theorem decideRows_correct {n : Nat} (formula : CNFFormula n) (rows : List Row) (inside : RowsWithin n rows) :
    decideRows formula rows = true ↔ ∃ assignment : Assignment n,
      CNFFormula.eval formula (extendAssignment assignment) = true ∧ holds rows (extendAssignment assignment) = true := by
  have valid := generate_invariants formula rows inside
  have initial := generate_holds formula rows
  cases generated : generate formula rows with
  | contradiction =>
      simp only [decideRows,generated,Bool.false_eq_true]
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨assignment,accepted,relations⟩
        have impossible := initial (extendAssignment assignment)
        simp [generated,accepted,relations,Result.holds] at impossible
  | basis basis =>
      have basisWithin : RowsWithin n basis := by simpa only [generated,Result.within] using valid.1
      simp only [decideRows,generated]
      rw [ConditionalPivot.decideRows_eq_original formula _ basisWithin,
        BranchImage.decideRows_correct formula _ basisWithin]
      apply exists_congr
      intro assignment
      have same := initial (extendAssignment assignment)
      simpa only [generated,Result.holds,Bool.and_eq_true] using Iff.of_eq (congrArg (· = true) same)

theorem decideRows_eq_original {n : Nat} (formula : CNFFormula n) (rows : List Row) (inside : RowsWithin n rows) :
    decideRows formula rows = ConditionalPivot.decideRows formula rows := by
  apply Bool.eq_iff_iff.mpr
  rw [decideRows_correct formula rows inside,ConditionalPivot.decideRows_eq_original formula rows inside,
    BranchImage.decideRows_correct formula rows inside]

def decideData (source : List (List Row)) : Bool :=
  let formula := Subsumption.reduce (Atoms.compile source)
  let image := AtomImage.generate (Atoms.table source)
  decideRows formula image.kernel

theorem decideData_eq_original (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) :
    decideData source = ConditionalPivot.decideData source :=
  decideRows_eq_original _ _ (AtomSource.kernel_within n source valid)

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  if Capacity.obstruction formula then false else
    match Atoms.generate formula with
    | .contradiction => false
    | .basis basis => decideData (Atoms.data basis formula)

theorem decideFormula_eq_original {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = ConditionalPivot.decideFormula formula := by
  unfold decideFormula
  split
  · rename_i rejected
    apply Bool.eq_iff_iff.mpr
    simp [ConditionalPivot.decideFormula_correct,Capacity.obstruction_unsatisfiable formula rejected]
  · cases generated : Atoms.generate formula with
    | contradiction => simp [ConditionalPivot.decideFormula,generated]
    | basis basis =>
        simp only [ConditionalPivot.decideFormula,generated]
        exact decideData_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula_eq_original,ConditionalPivot.decideFormula_correct]

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

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original,Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits,invalid]

def readRows {n : Nat} (formula : CNFFormula n) (rows : List Row) (assignment : Nat → Bool) : Bool :=
  match generate formula rows with
  | .contradiction => false
  | .basis basis => ConditionalPivot.readResult formula (BranchImage.generate formula basis) assignment

theorem readRows_value {n : Nat} (formula : CNFFormula n) (rows : List Row) (inside : RowsWithin n rows)
    (assignment : Nat → Bool) :
    readRows formula rows assignment = (CNFFormula.eval formula assignment && holds rows assignment) := by
  have initial := generate_holds formula rows assignment
  have valid := generate_invariants formula rows inside
  cases generated : generate formula rows with
  | contradiction => simpa [readRows,generated,Result.holds] using initial
  | basis basis =>
      have basisWithin : RowsWithin n basis := by simpa only [generated,Result.within] using valid.1
      have final := BranchImage.generate_invariants formula basis basisWithin
      simp only [readRows,generated]
      rw [ConditionalPivot.readResult_value _ _ final.1 final.2,
        BranchImage.generate_holds _ _ basisWithin]
      simpa only [generated,Result.holds] using initial

def jointValue (source : List (List Row)) (target : Nat → Bool) : Bool :=
  let formula := Subsumption.reduce (Atoms.compile source)
  let image := AtomImage.generate (Atoms.table source)
  readRows formula image.kernel target

theorem jointValue_eq_original (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) (target : Nat → Bool) :
    jointValue source target = AtomSource.jointValue source target := by
  rw [jointValue,readRows_value _ _ (AtomSource.kernel_within n source valid),
    AtomSource.jointValue,Bool.and_comm]

def sourceAction {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : Source n) : Source n :=
  fun assignment =>
    let input := extendAssignment assignment
    if holds basis input && jointValue (Atoms.data basis formula) (Atoms.read (Atoms.data basis formula) input)
    then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = sourceAction formula basis source := by
  rw [AtomSource.original_projector formula basis generated source]
  funext assignment
  simp only [AtomSource.sourceAction,sourceAction,
    jointValue_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)]

end SaturationMonoid.ComplexityProjection.SATSource.Affine.CapacityFeedback
