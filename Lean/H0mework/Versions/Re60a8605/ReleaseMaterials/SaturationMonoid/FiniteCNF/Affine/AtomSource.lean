import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Atoms.Consumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalPivot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AtomImage

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.AtomSource

open InterferenceProgram

theorem terms_free {n : Nat} (basis : List Row) (triangular : Triangular basis) (formula : CNFFormula n)
    (terms : List Nat) (member : terms ∈ Atoms.keys (Atoms.data basis formula)) :
    ∀ i ∈ terms, i ∉ pivots basis := by
  simp only [Atoms.keys, List.mem_dedup, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨row, member, rfl⟩
  · simp
  · obtain ⟨rows, clauseMember, rowMember⟩ := List.mem_flatten.mp member
    obtain ⟨clause, _, same⟩ := List.mem_map.mp clauseMember
    subst rows
    obtain ⟨literal, _, same⟩ := List.mem_map.mp rowMember
    subst row
    intro i hit pivot
    have original : i ∈ (Propagation.residualRow basis literal).vars :=
      (List.mergeSort_perm _ _).mem_iff.mp hit
    obtain ⟨old, member, head⟩ := (mem_pivots basis i).mp pivot
    exact Propagation.residualRow_erases basis triangular literal old member i head original

theorem table_free {n : Nat} (basis : List Row) (triangular : Triangular basis) (formula : CNFFormula n)
    (row : Row) (member : row ∈ (Atoms.table (Atoms.data basis formula)).toList) :
    ∀ i ∈ row.vars, i ∉ pivots basis := by
  simp only [Atoms.table, List.toList_toArray, List.mem_map] at member
  obtain ⟨terms, member, rfl⟩ := member
  exact terms_free basis triangular formula terms member

theorem coordinate_fill (basis : List Row) (table : Array Row)
    (free : ∀ row ∈ table.toList, ∀ i ∈ row.vars, i ∉ pivots basis) (environment : Nat → Bool) :
    Gates.coordinate table (fill basis environment) = Gates.coordinate table environment := by
  funext index
  rw [Table.coordinate_getD, Table.coordinate_getD]
  by_cases inside : index < table.size
  · have valid := free table[index] (Array.getElem_mem_toList inside)
    simp only [Array.getD, inside, ↓reduceDIte, Gates.value, Row.eval]
    exact congrArg (Bool.xor table[index].rhs) (Parity.eval_congr _ _ _
      (fun i member => fill_read basis environment i (valid i member)))
  · simp [Array.getD, inside, Gates.zeroRow, Gates.value, Row.eval, Parity.eval]

theorem read_fill {n : Nat} (basis : List Row) (triangular : Triangular basis) (formula : CNFFormula n)
    (environment : Nat → Bool) :
    Atoms.read (Atoms.data basis formula) (fill basis environment) = Atoms.read (Atoms.data basis formula) environment :=
  coordinate_fill basis _ (table_free basis triangular formula) environment

/-- The whole atom image is unchanged when the original affine relations are restored. -/
theorem image_satisfiable {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) :
    (∃ environment : Nat → Bool,
      CNFFormula.eval (Atoms.ofFormula basis formula) (Atoms.read (Atoms.data basis formula) environment) = true) ↔
      CNFSatisfiable formula := by
  have triangular := Atoms.generated_triangular formula basis generated
  constructor
  · rintro ⟨environment, accepted⟩
    refine ⟨fill basis environment, ?_⟩
    rw [← Atoms.ofFormula_value basis formula _ (fill_holds basis triangular environment), read_fill basis triangular]
    exact accepted
  · rintro ⟨environment, accepted⟩
    exact ⟨environment, (Atoms.ofFormula_value basis formula environment
      (Atoms.generated_relations formula basis generated environment accepted)).trans accepted⟩

theorem holds_restrict (n : Nat) (rows : List Row) (inside : RowsWithin n rows) (environment : Nat → Bool) :
    holds rows (extendAssignment fun i : Fin n => environment i.val) = holds rows environment := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have head : row.holds (extendAssignment fun i : Fin n => environment i.val) = row.holds environment := by
        unfold Row.holds Row.eval
        congr 1
        apply Parity.eval_congr
        intro i member
        simp [extendAssignment, inside row (by simp) i member]
      have tail := ih (fun other member => inside other (by simp [member]))
      simp only [holds, List.all_cons] at *
      rw [head, tail]

def decideRows {n : Nat} (formula : CNFFormula n) (rows : List Row) : Bool :=
  match eliminate rows with
  | .contradiction => false
  | .basis basis => FunctionalSubstitution.decideProgram (Cone.pruneCone (FunctionalPivot.compile formula basis))

theorem decideRows_correct {n : Nat} (formula : CNFFormula n) (rows : List Row) (inside : RowsWithin n rows) :
    decideRows formula rows = true ↔ ∃ assignment : Assignment n,
      holds rows (extendAssignment assignment) = true ∧ CNFFormula.eval formula (extendAssignment assignment) = true := by
  have relation (basis : List Row) (generated : eliminate rows = .basis basis) (environment : Nat → Bool) :
      holds basis environment = holds rows environment := by
    have same := eliminate_holds rows environment
    rw [generated] at same
    exact same
  cases generated : eliminate rows with
  | contradiction =>
      have rejected (environment : Nat → Bool) : holds rows environment = false := by
        have same := eliminate_holds rows environment
        rw [generated] at same
        exact same.symm
      simp [decideRows, generated, rejected]
  | basis basis =>
      have triangular : Triangular basis := by simpa only [generated, Result.triangular] using eliminate_triangular rows
      have bound : RowsWithin n basis := by simpa only [generated, Result.within] using eliminate_within n rows inside
      simp only [decideRows, generated, FunctionalSubstitution.decideProgram_correct, Cone.eval_pruneCone]
      rw [FunctionalPivot.compile, FunctionalSubstitution.prepare,
        FunctionalSubstitution.execute_satisfiable _ _ (fun environment accepted instruction member =>
          FunctionalPivot.candidates_entails formula basis environment accepted instruction
            ((FunctionalSubstitution.select_sublist [] _).subset member))]
      simp only [Acceptance.eval_compile, truth_bit]
      constructor
      · rintro ⟨environment, accepted⟩
        let assignment : Assignment n := fun i => Gates.coordinate (Table.coordinates n basis) environment i.val
        have basisHolds : holds basis (Gates.coordinate (Table.coordinates n basis) environment) = true := by
          rw [Table.coordinates_value n basis bound]
          exact fill_holds basis triangular _
        refine ⟨assignment, ?_, ?_⟩
        · change holds rows (extendAssignment fun i : Fin n => Gates.coordinate (Table.coordinates n basis) environment i.val) = true
          rw [holds_restrict n rows inside, ← relation basis generated]
          exact basisHolds
        · exact (formula_eval_restrict formula _).trans accepted
      · rintro ⟨assignment, relations, accepted⟩
        have basisHolds : holds basis (extendAssignment assignment) = true := by
          rw [relation basis generated]
          exact relations
        have recovered := (Decision.table_lift n basis bound (projectFree n basis assignment)).trans
          (parameterLift_projectFree n basis triangular assignment basisHolds)
        refine ⟨extendAssignment (projectFree n basis assignment), ?_⟩
        rw [← formula_eval_restrict formula _]
        exact (congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) recovered).trans accepted

theorem kernel_within (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) :
    RowsWithin (Atoms.keys source).length (AtomImage.generate (Atoms.table source)).kernel := by
  have inside : AtomImage.SourceWithin n (Atoms.table source) :=
    fun row member => (Atoms.table_valid n source valid row member).2
  have generated := AtomImage.generate_valid n (Atoms.table source) inside
  intro row member
  simpa only [Atoms.table,List.size_toArray,List.length_map] using (generated.2 row member).2

theorem eval_realizes (source : List (List Row)) (input target : Nat → Bool)
    (realized : AtomImage.Realizes (Atoms.table source) input target) :
    CNFFormula.eval (Subsumption.reduce (Atoms.compile source)) (Atoms.read source input) =
      CNFFormula.eval (Subsumption.reduce (Atoms.compile source)) target := by
  have common : (fun i : Fin (Atoms.keys source).length => Atoms.read source input i.val) =
      (fun i : Fin (Atoms.keys source).length => target i.val) := by
    funext i
    exact realized ⟨i.val, by simp [Atoms.table]⟩
  rw [← formula_eval_restrict (Subsumption.reduce (Atoms.compile source)) (Atoms.read source input), common,
    formula_eval_restrict]

/-- The shared forms generate their complete image constraints before the atom clauses are decided. -/
def decideData (source : List (List Row)) : Bool :=
  let generated := AtomImage.generate (Atoms.table source)
  let formula := Subsumption.reduce (Atoms.compile source)
  decideRows formula generated.kernel

theorem decideData_correct (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) :
    decideData source = true ↔ ∃ input : Nat → Bool,
      CNFFormula.eval (Subsumption.reduce (Atoms.compile source)) (Atoms.read source input) = true := by
  rw [decideData, decideRows_correct _ _ (kernel_within n source valid)]
  constructor
  · rintro ⟨target, allowed, accepted⟩
    refine ⟨AtomImage.decode (Atoms.table source) (extendAssignment target), ?_⟩
    exact (eval_realizes source _ _ (AtomImage.decode_realizes (Atoms.table source) _ allowed)).trans accepted
  · rintro ⟨input, accepted⟩
    let target : Assignment (Atoms.keys source).length := fun i => Atoms.read source input i.val
    have allowed : holds (AtomImage.generate (Atoms.table source)).kernel (Atoms.read source input) = true :=
      (AtomImage.image_iff_kernel _ _).mp ⟨input, fun _ => rfl⟩
    refine ⟨target, ?_, (formula_eval_restrict _ _).trans accepted⟩
    exact (holds_restrict _ _ (kernel_within n source valid) _).trans allowed

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match Atoms.generate formula with
  | .contradiction => false
  | .basis basis => decideData (Atoms.data basis formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  cases generated : Atoms.generate formula with
  | contradiction =>
      have rejected : ¬ CNFSatisfiable formula := by
        rintro ⟨assignment, accepted⟩
        rw [Atoms.generated_contradiction_eval formula generated] at accepted
        exact Bool.noConfusion accepted
      simp [decideFormula, generated, rejected]
  | basis basis =>
      simp only [decideFormula, generated]
      rw [decideData_correct n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)]
      exact image_satisfiable formula basis generated

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits, Encoding.decideBits, parsed]
  | some input =>
      simp only [decideBits, Encoding.decideBits, parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct, Dense.decideFormula_correct]

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
  holds (AtomImage.generate (Atoms.table source)).kernel target &&
    CNFFormula.eval (Subsumption.reduce (Atoms.compile source)) target

theorem jointValue_read (source : List (List Row)) (input : Nat → Bool) :
    jointValue source (Atoms.read source input) =
      CNFFormula.eval (Subsumption.reduce (Atoms.compile source)) (Atoms.read source input) := by
  have allowed : holds (AtomImage.generate (Atoms.table source)).kernel (Atoms.read source input) = true :=
    (AtomImage.image_iff_kernel _ _).mp ⟨input, fun _ => rfl⟩
  simp only [jointValue, allowed, Bool.true_and]

def sourceAction {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : Source n) : Source n :=
  fun assignment =>
    let input := extendAssignment assignment
    if holds basis input && jointValue (Atoms.data basis formula) (Atoms.read (Atoms.data basis formula) input)
    then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = sourceAction formula basis source := by
  funext assignment
  rw [zeroProjector_apply, sourceAction, jointValue_read]
  by_cases relations : holds basis (extendAssignment assignment) = true
  · rw [relations, Bool.true_and]
    change _ = if CNFFormula.eval (Atoms.ofFormula basis formula)
      (Atoms.read (Atoms.data basis formula) (extendAssignment assignment)) then source assignment else 0
    rw [Atoms.ofFormula_value basis formula _ relations]
  · have rejected : CNFFormula.eval formula (extendAssignment assignment) ≠ true :=
      fun accepted => relations (Atoms.generated_relations formula basis generated _ accepted)
    simp [relations, rejected]

end SaturationMonoid.ComplexityProjection.SATSource.Affine.AtomSource
