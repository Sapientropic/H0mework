import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.AtomSource

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.JointFeedback

open InterferenceProgram

/-- Both rules consume the same CNF together with the current generated row system. -/
def step {n : Nat} (formula : CNFFormula n) (result : Result) : Result :=
  Atoms.advance formula (Propagation.update formula result)

theorem update_holds {n : Nat} (formula : CNFFormula n) (result : Result)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (Propagation.update formula result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  cases result with
  | contradiction => rfl
  | basis basis =>
      by_cases accepted : CNFFormula.eval formula assignment = true
      · cases found : Propagation.find basis formula with
        | satisfied => simp only [Propagation.update, found]
        | unresolved => simp only [Propagation.update, found]
        | contradiction =>
            have rejected : holds basis assignment = false := by
              apply Bool.eq_false_iff.mpr
              intro relations
              have impossible := Propagation.find_contradiction basis formula found assignment relations
              rw [accepted] at impossible
              exact Bool.noConfusion impossible
            simp [Propagation.update, found, Result.holds, rejected]
        | forced row =>
            rw [Propagation.update, found, Result.insert_holds]
            by_cases relations : holds basis assignment = true
            · have learned := Propagation.find_forced basis formula row found assignment relations accepted
              simp [Result.holds, relations, learned]
            · simp [Result.holds, relations]
      · simp [accepted]

theorem advance_holds {n : Nat} (formula : CNFFormula n) (result : Result)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (Atoms.advance formula result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  cases result with
  | contradiction => rfl
  | basis basis =>
      rw [Atoms.advance, eliminateFrom_holds]
      by_cases accepted : CNFFormula.eval formula assignment = true
      · by_cases relations : holds basis assignment = true
        · have learned := Atoms.learn_entails basis formula assignment relations accepted
          simp [Result.holds, relations, learned]
        · simp [Result.holds, relations]
      · simp [accepted]

theorem step_holds {n : Nat} (formula : CNFFormula n) (result : Result)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (step formula result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  rw [step, advance_holds, update_holds]

theorem step_invariants {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (step formula result).within n ∧ (step formula result).triangular :=
  Atoms.advance_invariants formula _ (Propagation.update_within formula result inside)
    (Propagation.update_triangular formula result triangular)

theorem update_remaining {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    Propagation.remaining n (Propagation.update formula result) ≤ Propagation.remaining n result := by
  by_cases fixed : Propagation.update formula result = result
  · rw [fixed]
  · exact (Propagation.update_progress formula result inside triangular fixed).le

theorem advance_remaining {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    Propagation.remaining n (Atoms.advance formula result) ≤ Propagation.remaining n result := by
  by_cases fixed : Atoms.advance formula result = result
  · rw [fixed]
  · exact (Atoms.advance_progress formula result inside triangular fixed).le

theorem step_progress {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (changed : step formula result ≠ result) :
    Propagation.remaining n (step formula result) < Propagation.remaining n result := by
  by_cases fixed : Propagation.update formula result = result
  · have different : Atoms.advance formula result ≠ result := by simpa only [step, fixed] using changed
    simpa only [step, fixed] using Atoms.advance_progress formula result inside triangular different
  · have first := Propagation.update_progress formula result inside triangular fixed
    have second := advance_remaining formula (Propagation.update formula result)
      (Propagation.update_within formula result inside) (Propagation.update_triangular formula result triangular)
    exact lt_of_le_of_lt second first

theorem step_fixed_iff {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    step formula result = result ↔
      Propagation.update formula result = result ∧ Atoms.advance formula result = result := by
  constructor
  · intro fixed
    have first : Propagation.update formula result = result := by
      by_contra changed
      have strict := Propagation.update_progress formula result inside triangular changed
      have next := advance_remaining formula (Propagation.update formula result)
        (Propagation.update_within formula result inside) (Propagation.update_triangular formula result triangular)
      change Propagation.remaining n (step formula result) ≤ _ at next
      rw [fixed] at next
      omega
    exact ⟨first, by simpa only [step, first] using fixed⟩
  · rintro ⟨first, second⟩
    simp only [step, first, second]

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Result
  | 0, result => result
  | fuel+1, result => iterate formula fuel (step formula result)

theorem iterate_holds {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (iterate formula fuel result).holds assignment) =
      (CNFFormula.eval formula assignment && result.holds assignment) := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => exact (ih (step formula result)).trans (step_holds formula result assignment)

theorem iterate_invariants {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (iterate formula fuel result).within n ∧ (iterate formula fuel result).triangular := by
  induction fuel generalizing result with
  | zero => exact ⟨inside, triangular⟩
  | succ fuel ih =>
      have next := step_invariants formula result inside triangular
      exact ih _ next.1 next.2

theorem iterate_fixed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (fixed : step formula result = result) : iterate formula fuel result = result := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate, fixed] using ih

theorem iterate_settled {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular)
    (enough : Propagation.remaining n result ≤ fuel) :
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
      · have progress := step_progress formula result inside triangular fixed
        have next := step_invariants formula result inside triangular
        exact ih _ next.1 next.2 (by omega)

def generate {n : Nat} (formula : CNFFormula n) (rows : List Row) : Result :=
  iterate formula (n+1) (eliminate rows)

theorem generate_holds {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (generate formula rows).holds assignment) =
      (CNFFormula.eval formula assignment && holds rows assignment) := by
  rw [generate, iterate_holds, eliminate_holds]

theorem generate_invariants {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) :
    (generate formula rows).within n ∧ (generate formula rows).triangular :=
  iterate_invariants formula (n+1) _ (eliminate_within n rows inside) (eliminate_triangular rows)

/-- The two rules are fixed on one and the same final state. -/
theorem generate_settled {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) :
    Propagation.update formula (generate formula rows) = generate formula rows ∧
      Atoms.advance formula (generate formula rows) = generate formula rows := by
  have valid := generate_invariants formula rows inside
  apply (step_fixed_iff formula _ valid.1 valid.2).mp
  apply iterate_settled formula (n+1) _ (eliminate_within n rows inside) (eliminate_triangular rows)
  cases eliminate rows <;> simp only [Propagation.remaining] <;> omega

theorem generated_within {n : Nat} (formula : CNFFormula n) (rows basis : List Row)
    (inside : RowsWithin n rows) (generated : generate formula rows = .basis basis) : RowsWithin n basis := by
  have valid := (generate_invariants formula rows inside).1
  simpa only [generated, Result.within] using valid

theorem generated_triangular {n : Nat} (formula : CNFFormula n) (rows basis : List Row)
    (inside : RowsWithin n rows) (generated : generate formula rows = .basis basis) : Triangular basis := by
  have valid := (generate_invariants formula rows inside).2
  simpa only [generated, Result.triangular] using valid

theorem generated_dimension {n : Nat} (formula : CNFFormula n) (rows basis : List Row)
    (inside : RowsWithin n rows) (generated : generate formula rows = .basis basis) :
    (freeIndices n basis).length + basis.length = n :=
  freeIndices_dimension n basis (generated_triangular formula rows basis inside generated)
    (generated_within formula rows basis inside generated)

theorem generated_no_forced {n : Nat} (formula : CNFFormula n) (rows basis : List Row)
    (inside : RowsWithin n rows) (generated : generate formula rows = .basis basis) (row : Row) :
    Propagation.find basis formula ≠ .forced row := by
  intro found
  have fixed := (generate_settled formula rows inside).1
  rw [generated, Propagation.find_forced_update basis
    (generated_triangular formula rows basis inside generated) formula row found] at fixed
  have lengths := congrArg List.length (Result.basis.inj fixed)
  simp only [List.length_append, List.length_singleton] at lengths
  omega

theorem generated_no_contradiction {n : Nat} (formula : CNFFormula n) (rows basis : List Row)
    (inside : RowsWithin n rows) (generated : generate formula rows = .basis basis) :
    Propagation.find basis formula ≠ .contradiction := by
  intro found
  have fixed := (generate_settled formula rows inside).1
  simp only [generated, Propagation.update, found] at fixed
  exact Result.noConfusion fixed

theorem generated_learn_absorbed {n : Nat} (formula : CNFFormula n) (rows basis : List Row)
    (inside : RowsWithin n rows) (generated : generate formula rows = .basis basis) :
    eliminateFrom (.basis basis) (Atoms.learn basis formula) = .basis basis := by
  have fixed := (generate_settled formula rows inside).2
  simpa only [generated, Atoms.advance] using fixed

/-- Read the generated basis directly; this consumer does not eliminate it a second time. -/
def decideResult {n : Nat} (formula : CNFFormula n) : Result → Bool
  | .contradiction => false
  | .basis basis => FunctionalSubstitution.decideProgram (Cone.pruneCone (FunctionalPivot.compile formula basis))

theorem decideResult_correct {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    decideResult formula result = true ↔ ∃ assignment : Assignment n,
      (CNFFormula.eval formula (extendAssignment assignment) && result.holds (extendAssignment assignment)) = true := by
  cases result with
  | contradiction => simp [decideResult, Result.holds]
  | basis basis =>
      simp only [decideResult, FunctionalSubstitution.decideProgram_correct, Cone.eval_pruneCone]
      rw [FunctionalPivot.compile, FunctionalSubstitution.prepare,
        FunctionalSubstitution.execute_satisfiable _ _ (fun environment accepted instruction member =>
          FunctionalPivot.candidates_entails formula basis environment accepted instruction
            ((FunctionalSubstitution.select_sublist [] _).subset member))]
      simp only [Acceptance.eval_compile, truth_bit, Bool.and_eq_true, Result.holds]
      constructor
      · rintro ⟨environment, accepted⟩
        let assignment : Assignment n := fun i => Gates.coordinate (Table.coordinates n basis) environment i.val
        have relations : holds basis (Gates.coordinate (Table.coordinates n basis) environment) = true := by
          rw [Table.coordinates_value n basis inside]
          exact fill_holds basis triangular _
        refine ⟨assignment, (formula_eval_restrict formula _).trans accepted, ?_⟩
        exact (AtomSource.holds_restrict n basis inside _).trans relations
      · rintro ⟨assignment, accepted, relations⟩
        have recovered := (Decision.table_lift n basis inside (projectFree n basis assignment)).trans
          (parameterLift_projectFree n basis triangular assignment relations)
        refine ⟨extendAssignment (projectFree n basis assignment), ?_⟩
        rw [← formula_eval_restrict formula _]
        exact (congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) recovered).trans accepted

def decideRows {n : Nat} (formula : CNFFormula n) (rows : List Row) : Bool :=
  decideResult formula (generate formula rows)

theorem decideRows_correct {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) :
    decideRows formula rows = true ↔ ∃ assignment : Assignment n,
      CNFFormula.eval formula (extendAssignment assignment) = true ∧ holds rows (extendAssignment assignment) = true := by
  have valid := generate_invariants formula rows inside
  rw [decideRows, decideResult_correct formula _ valid.1 valid.2]
  simp only [generate_holds, Bool.and_eq_true]

theorem decideRows_eq_original {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) : decideRows formula rows = AtomSource.decideRows formula rows := by
  apply Bool.eq_iff_iff.mpr
  rw [decideRows_correct formula rows inside, AtomSource.decideRows_correct formula rows inside]
  simp only [and_comm]

def decideData (source : List (List Row)) : Bool :=
  let image := AtomImage.generate (Atoms.table source)
  let formula := Subsumption.reduce (Atoms.compile source)
  decideRows formula image.kernel

theorem decideData_eq_original (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) :
    decideData source = AtomSource.decideData source :=
  decideRows_eq_original _ _ (AtomSource.kernel_within n source valid)

theorem decideData_correct (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) :
    decideData source = true ↔ ∃ input : Nat → Bool,
      CNFFormula.eval (Subsumption.reduce (Atoms.compile source)) (Atoms.read source input) = true := by
  rw [decideData_eq_original n source valid, AtomSource.decideData_correct n source valid]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match Atoms.generate formula with
  | .contradiction => false
  | .basis basis => decideData (Atoms.data basis formula)

theorem decideFormula_eq_original {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = AtomSource.decideFormula formula := by
  cases generated : Atoms.generate formula with
  | contradiction => simp [decideFormula, AtomSource.decideFormula, generated]
  | basis basis =>
      simp only [decideFormula, AtomSource.decideFormula, generated]
      exact decideData_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula_eq_original, AtomSource.decideFormula_correct]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  rw [← AtomSource.decideBits_eq_original]
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits, AtomSource.decideBits, parsed]
  | some input => simp [decideBits, AtomSource.decideBits, parsed, decideFormula_eq_original]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original, Encoding.decideBits_iff_rootVerify]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original, Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits, invalid]

def jointValue (source : List (List Row)) (target : Nat → Bool) : Bool :=
  let image := AtomImage.generate (Atoms.table source)
  let formula := Subsumption.reduce (Atoms.compile source)
  CNFFormula.eval formula target && (generate formula image.kernel).holds target

theorem jointValue_eq_original (source : List (List Row)) (target : Nat → Bool) :
    jointValue source target = AtomSource.jointValue source target := by
  rw [jointValue, generate_holds, AtomSource.jointValue, Bool.and_comm]

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
  simp only [AtomSource.sourceAction, sourceAction, jointValue_eq_original]

end SaturationMonoid.ComplexityProjection.SATSource.Affine.JointFeedback
