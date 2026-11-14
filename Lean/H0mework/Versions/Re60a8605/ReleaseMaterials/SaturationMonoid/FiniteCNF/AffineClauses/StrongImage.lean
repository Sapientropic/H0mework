import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.ImageSource

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineStrongImage
open SaturationMonoid.ComplexityProjection.SATSource.Affine

/-- One actual feedback result is shared by every downstream chart. -/
def assemble {n : Nat} (formula : CNFFormula n) (initial : Result) : List (AffineImageSource.Chart formula) :=
  (AffineCarrier.pack initial).value.map (AffineImageSource.chart formula)

theorem assemble_read {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) (assignment : Assignment n) :
    AffineImageSource.read (assemble formula initial) assignment =
      (initial.holds (extendAssignment assignment) && CNFFormula.eval formula (extendAssignment assignment)) := by
  cases initial with
  | contradiction => simp [assemble,AffineCarrier.pack,AffineImageSource.read,Result.holds]
  | basis basis =>
      simp only [assemble,AffineCarrier.pack,List.map_cons,List.map_nil,AffineImageSource.read,List.any_cons,List.any_nil,Bool.or_false]
      exact AffineImageSource.chart_read formula basis valid assignment

theorem assemble_image {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) (assignment : Assignment n) :
    (∃ p : AffineImageSource.Parameters (assemble formula initial),
      AffineImageSource.lift (assemble formula initial) p = assignment) ↔
      initial.holds (extendAssignment assignment) = true ∧ CNFFormula.eval formula (extendAssignment assignment) = true := by
  rw [AffineImageSource.list_image]
  cases initial with
  | contradiction => simp [assemble,AffineCarrier.pack,Result.holds]
  | basis basis =>
      simp only [assemble,AffineCarrier.pack,List.map_cons,List.map_nil,List.mem_singleton,exists_eq_left]
      exact AffineImageSource.chart_image formula basis valid assignment

theorem assemble_possible {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) :
    (assemble formula initial).any AffineImageSource.Chart.possible = true ↔
      ∃ assignment : Assignment n, initial.holds (extendAssignment assignment) = true ∧
        CNFFormula.eval formula (extendAssignment assignment) = true := by
  cases initial with
  | contradiction => simp [assemble,AffineCarrier.pack,Result.holds]
  | basis basis =>
      simp only [assemble,AffineCarrier.pack,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false]
      exact AffineImageSource.chart_possible formula basis valid

structure Output (n : Nat) where
  formula : CNFFormula n
  binaryQueries : Nat
  initial : Result
  charts : List (AffineImageSource.Chart formula)

def generate {n : Nat} (original : CNFFormula n) : Output n :=
  let binary := BinaryRelations.generate original
  let initial := AffineCarrier.tightSeed binary.formula
  let charts := assemble binary.formula initial
  ⟨binary.formula,binary.queries,initial,charts⟩

theorem generate_formula {n : Nat} (original : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (generate original).formula assignment = CNFFormula.eval original assignment :=
  BinaryRelations.generate_value original assignment

theorem generate_initial {n : Nat} (original : CNFFormula n) :
    (generate original).initial.triangular ∧ (generate original).initial.within n :=
  AffineCarrier.tightSeed_valid (BinaryRelations.generate original).formula

theorem generate_queries {n : Nat} (original : CNFFormula n) : (generate original).binaryQueries ≤ 16*n^4 :=
  BinaryRelations.generate_queries original

theorem generate_length {n : Nat} (original : CNFFormula n) : (generate original).formula.length ≤ original.length+4*n*n :=
  BinaryRelations.generate_length original

theorem generate_literals {n : Nat} (original : CNFFormula n) :
    Extract.literalCount (generate original).formula ≤ Extract.literalCount original+8*n*n :=
  BinaryRelations.generate_literals original

theorem generate_charts {n : Nat} (original : CNFFormula n) : (generate original).charts.length ≤ 1 := by
  simpa only [generate,assemble,List.length_map] using
    AffineCarrier.Cost.pack_length (AffineCarrier.tightSeed (BinaryRelations.generate original).formula)

theorem generate_initial_size {n : Nat} (original : CNFFormula n) :
    AffineCarrier.resultSize (generate original).initial ≤ AffineCarrier.Cost.cellBound n+1 :=
  AffineCarrier.Cost.result_size n _ (generate_initial original).1 (generate_initial original).2

def read {n : Nat} (output : Output n) (assignment : Assignment n) : Bool := AffineImageSource.read output.charts assignment

theorem generate_read {n : Nat} (original : CNFFormula n) (assignment : Assignment n) :
    read (generate original) assignment = CNFFormula.eval original (extendAssignment assignment) := by
  change AffineImageSource.read (assemble (BinaryRelations.generate original).formula
    (AffineCarrier.tightSeed (BinaryRelations.generate original).formula)) assignment = _
  rw [assemble_read _ _ (AffineCarrier.tightSeed_valid _)]
  by_cases accepted : CNFFormula.eval (BinaryRelations.generate original).formula (extendAssignment assignment) = true
  · rw [AffineCarrier.tightSeed_entails _ _ accepted,Bool.true_and]
    exact BinaryRelations.generate_value original _
  · rw [Bool.eq_false_iff.mpr accepted,Bool.and_false]
    exact (BinaryRelations.generate_value original _).symm.trans (Bool.eq_false_iff.mpr accepted) |>.symm

def Parameters {n : Nat} (output : Output n) := AffineImageSource.Parameters output.charts

def lift {n : Nat} (output : Output n) (parameter : Parameters output) : Assignment n := AffineImageSource.lift output.charts parameter

theorem generate_image {n : Nat} (original : CNFFormula n) (assignment : Assignment n) :
    (∃ p : Parameters (generate original), lift (generate original) p=assignment) ↔
      CNFFormula.eval original (extendAssignment assignment) = true := by
  change (∃ p : AffineImageSource.Parameters (assemble (BinaryRelations.generate original).formula
    (AffineCarrier.tightSeed (BinaryRelations.generate original).formula)), AffineImageSource.lift _ p=assignment) ↔ _
  rw [assemble_image _ _ (AffineCarrier.tightSeed_valid _)]
  constructor
  · intro accepted
    exact (BinaryRelations.generate_value original _).symm.trans accepted.2
  · intro accepted
    have stronger := (BinaryRelations.generate_value original _).trans accepted
    exact ⟨AffineCarrier.tightSeed_entails _ _ stronger,stronger⟩

def decideFormula {n : Nat} (original : CNFFormula n) : Bool := (generate original).charts.any AffineImageSource.Chart.possible

theorem decideFormula_correct {n : Nat} (original : CNFFormula n) : decideFormula original = true ↔ CNFSatisfiable original := by
  change (assemble (BinaryRelations.generate original).formula
    (AffineCarrier.tightSeed (BinaryRelations.generate original).formula)).any AffineImageSource.Chart.possible = true ↔ _
  rw [assemble_possible _ _ (AffineCarrier.tightSeed_valid _)]
  constructor
  · rintro ⟨assignment,_,accepted⟩
    exact ⟨extendAssignment assignment,(BinaryRelations.generate_value original _).symm.trans accepted⟩
  · rintro ⟨assignment,accepted⟩
    let finite : Assignment n := fun i => assignment i.val
    have source := (formula_eval_restrict original assignment).trans accepted
    have stronger := (BinaryRelations.generate_value original (extendAssignment finite)).trans source
    exact ⟨finite,AffineCarrier.tightSeed_entails _ _ stronger,stronger⟩

theorem assemble_preparation {n : Nat} (formula : CNFFormula n) (initial : Result)
    (valid : initial.triangular ∧ initial.within n) :
    AffineImageSource.preparationCells (assemble formula initial) ≤
      AffineClauses.Cost.prepareBudget n formula.length (Extract.literalCount formula) := by
  cases initial with
  | contradiction => simp [assemble,AffineCarrier.pack,AffineImageSource.preparationCells]
  | basis basis =>
      simpa only [assemble,AffineCarrier.pack,AffineImageSource.preparationCells,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
        AffineImageSource.chart_preparation formula basis valid

theorem prepareBudget_mono (n m M ell E : Nat) (hm : m ≤ M) (he : ell ≤ E) :
    AffineClauses.Cost.prepareBudget n m ell ≤ AffineClauses.Cost.prepareBudget n M E := by
  unfold AffineClauses.Cost.prepareBudget AffineClauses.Cost.coordinateCompileBudget AffineClauses.Cost.compileBudget
    AffineClauses.Cost.formulaBudget AffineClauses.Cost.literalBudget AffineClauses.Cost.cleanBudget
  gcongr

theorem generate_preparation {n : Nat} (original : CNFFormula n) :
    AffineImageSource.preparationCells (generate original).charts ≤
      AffineClauses.Cost.prepareBudget n (original.length+4*n*n) (Extract.literalCount original+8*n*n) := by
  have first := assemble_preparation (BinaryRelations.generate original).formula
    (AffineCarrier.tightSeed (BinaryRelations.generate original).formula) (AffineCarrier.tightSeed_valid _)
  exact first.trans (prepareBudget_mono n _ _ _ _ (BinaryRelations.generate_length original) (BinaryRelations.generate_literals original))

def sourceAction {n : Nat} (original : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read (generate original) assignment then source assignment else 0

theorem original_projector {n : Nat} (original : CNFFormula n) (source : Source n) :
    zeroProjector original source = sourceAction original source := by
  funext assignment
  simp only [sourceAction,zeroProjector_apply,generate_read]

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

end SaturationMonoid.ComplexityProjection.SATSource.AffineStrongImage
