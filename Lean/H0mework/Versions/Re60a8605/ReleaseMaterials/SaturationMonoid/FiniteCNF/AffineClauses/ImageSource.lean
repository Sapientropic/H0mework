import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.JointImage
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Source
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineImageSource

open SaturationMonoid.ComplexityProjection.SATSource.Affine

def coordinateFormula {n : Nat} (formula : CNFFormula n) (basis : List Row) : AffineClauses.Formula :=
  (AffineClauses.Cost.prepare basis formula).value

theorem coordinateFormula_within {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    AffineClauses.Within (freeIndices n basis).length (coordinateFormula formula basis) :=
  AffineClauses.Cost.prepare_within basis formula

theorem coordinateFormula_read {n : Nat} (formula : CNFFormula n) (basis : List Row) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    AffineClauses.formulaRead (coordinateFormula formula basis) (extendAssignment parameters) =
      CNFFormula.eval formula (extendAssignment (parameterLift n basis parameters)) :=
  AffineClauses.Cost.prepare_parameter_read basis inside formula parameters

structure Chart {n : Nat} (formula : CNFFormula n) where
  basis : List Row
  model : AffineJointImage.Model (coordinateFormula formula basis)
  preparationCells : Nat

def chart {n : Nat} (formula : CNFFormula n) (basis : List Row) : Chart formula :=
  let prepared := AffineClauses.Cost.prepare basis formula
  ⟨basis,AffineJointImage.generate prepared.value,prepared.cells⟩

theorem chart_preparation {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (chart formula basis).preparationCells ≤ AffineClauses.Cost.prepareBudget n formula.length (Extract.literalCount formula) :=
  AffineClauses.Cost.prepare_cells basis valid formula

def Chart.Parameters {n : Nat} {formula : CNFFormula n} (source : Chart formula) : Type :=
  AffineJointImage.Parameters (freeIndices n source.basis).length (coordinateFormula formula source.basis) source.model

def Chart.lift {n : Nat} {formula : CNFFormula n} (source : Chart formula) (parameter : source.Parameters) : Assignment n :=
  parameterLift n source.basis
    (AffineJointImage.lift (freeIndices n source.basis).length (coordinateFormula formula source.basis) source.model parameter)

def Chart.read {n : Nat} {formula : CNFFormula n} (source : Chart formula) (assignment : Assignment n) : Bool :=
  holds source.basis (extendAssignment assignment) && AffineJointImage.read (coordinateFormula formula source.basis) source.model
    (extendAssignment (projectFree n source.basis assignment))

theorem chart_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    (chart formula basis).read assignment =
      (holds basis (extendAssignment assignment) && CNFFormula.eval formula (extendAssignment assignment)) := by
  change (holds basis (extendAssignment assignment) &&
    AffineJointImage.read (coordinateFormula formula basis) (AffineJointImage.generate (coordinateFormula formula basis))
      (extendAssignment (projectFree n basis assignment))) = _
  rw [AffineJointImage.generate_read _ _ (coordinateFormula_within formula basis),coordinateFormula_read formula basis valid.2]
  by_cases accepted : holds basis (extendAssignment assignment) = true
  · rw [parameterLift_projectFree n basis valid.1 assignment accepted]
  · simp [Bool.eq_false_iff.mpr accepted]

theorem chart_image {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    (∃ parameter : (chart formula basis).Parameters, (chart formula basis).lift parameter = assignment) ↔
      holds basis (extendAssignment assignment) = true ∧ CNFFormula.eval formula (extendAssignment assignment) = true := by
  let data := coordinateFormula formula basis
  have bounded := coordinateFormula_within formula basis
  constructor
  · rintro ⟨parameter,rfl⟩
    let coordinates := AffineJointImage.lift (freeIndices n basis).length data (AffineJointImage.generate data) parameter
    have accepted : AffineClauses.formulaRead data (extendAssignment coordinates) = true :=
      (AffineJointImage.generate_image _ data bounded coordinates).mp ⟨parameter,rfl⟩
    exact ⟨parameterLift_holds n basis valid.1 valid.2 coordinates,
      (coordinateFormula_read formula basis valid.2 coordinates).symm.trans accepted⟩
  · rintro ⟨inBasis,accepted⟩
    let coordinates := projectFree n basis assignment
    have lifted := parameterLift_projectFree n basis valid.1 assignment inBasis
    have rowAccepted : AffineClauses.formulaRead data (extendAssignment coordinates) = true := by
      rw [coordinateFormula_read formula basis valid.2]
      exact (congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) lifted).trans accepted
    obtain ⟨parameter,same⟩ := (AffineJointImage.generate_image _ data bounded coordinates).mpr rowAccepted
    refine ⟨parameter,?_⟩
    change parameterLift n basis (AffineJointImage.lift (freeIndices n basis).length data (AffineJointImage.generate data) parameter) = assignment
    rw [same]
    exact lifted

def Chart.possible {n : Nat} {formula : CNFFormula n} (source : Chart formula) : Bool :=
  AffineJointImage.possible (coordinateFormula formula source.basis) source.model

theorem chart_possible {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (chart formula basis).possible = true ↔ ∃ assignment : Assignment n,
      holds basis (extendAssignment assignment) = true ∧ CNFFormula.eval formula (extendAssignment assignment) = true := by
  let data := coordinateFormula formula basis
  have bounded := coordinateFormula_within formula basis
  change AffineJointImage.possible data (AffineJointImage.generate data) = true ↔ _
  rw [AffineJointImage.generate_possible _ data bounded]
  constructor
  · rintro ⟨point,accepted⟩
    let coordinates : Assignment (freeIndices n basis).length := fun i => point i.val
    have finite := (AffineClauseProduct.formula_restrict _ data bounded point).trans accepted
    obtain ⟨parameter,_⟩ := (AffineJointImage.generate_image _ data bounded coordinates).mpr finite
    exact ⟨(chart formula basis).lift parameter,(chart_image formula basis valid _).mp ⟨parameter,rfl⟩⟩
  · rintro ⟨assignment,inBasis,accepted⟩
    let coordinates := projectFree n basis assignment
    have lifted := parameterLift_projectFree n basis valid.1 assignment inBasis
    refine ⟨extendAssignment coordinates,?_⟩
    exact (coordinateFormula_read formula basis valid.2 coordinates).trans
      ((congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) lifted).trans accepted)

def generate {n : Nat} (formula : CNFFormula n) : List (Chart formula) :=
  let initial := AffineCarrier.seed formula
  initial.value.map (chart formula)

def preparationCells {n : Nat} {formula : CNFFormula n} (sources : List (Chart formula)) : Nat :=
  (sources.map Chart.preparationCells).sum

theorem generate_preparation {n : Nat} (formula : CNFFormula n) :
    preparationCells (generate formula) ≤ AffineClauses.Cost.prepareBudget n formula.length (Extract.literalCount formula) := by
  let budget := AffineClauses.Cost.prepareBudget n formula.length (Extract.literalCount formula)
  have every (bases : AffineCarrier.Cells) (valid : AffineCarrier.Valid n bases) :
      preparationCells (bases.map (chart formula)) ≤ bases.length*budget := by
    induction bases with
    | nil => simp [preparationCells]
    | cons basis rest ih =>
        have first := chart_preparation formula basis (valid basis (by simp))
        have tail := ih (fun b member => valid b (by simp [member]))
        simp only [preparationCells,List.map_cons,List.sum_cons,List.length_cons] at tail ⊢
        dsimp only [budget] at *
        nlinarith
  have generated := every (AffineCarrier.seed formula).value (AffineCarrier.seed_valid formula)
  exact generated.trans (by simpa using Nat.mul_le_mul_right budget (AffineCarrier.Cost.seed_length formula))

def read {n : Nat} {formula : CNFFormula n} (sources : List (Chart formula)) (assignment : Assignment n) : Bool :=
  sources.any (fun source => source.read assignment)

theorem generate_read {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    read (generate formula) assignment = CNFFormula.eval formula (extendAssignment assignment) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    obtain ⟨source,member,truth⟩ := List.any_eq_true.mp accepted
    obtain ⟨basis,present,rfl⟩ := List.mem_map.mp member
    rw [chart_read formula basis (AffineCarrier.seed_valid formula basis present) assignment] at truth
    have both : holds basis (extendAssignment assignment) = true ∧ CNFFormula.eval formula (extendAssignment assignment) = true := by simpa using truth
    exact both.2
  · intro accepted
    have seed := AffineCarrier.seed_entails formula (extendAssignment assignment) accepted
    obtain ⟨basis,present,inBasis⟩ := List.any_eq_true.mp seed
    apply List.any_eq_true.mpr
    refine ⟨chart formula basis,List.mem_map.mpr ⟨basis,present,rfl⟩,?_⟩
    rw [chart_read formula basis (AffineCarrier.seed_valid formula basis present) assignment,inBasis,accepted]
    rfl

def Parameters {n : Nat} {formula : CNFFormula n} (sources : List (Chart formula)) := (i : Fin sources.length) × (sources.get i).Parameters

def lift {n : Nat} {formula : CNFFormula n} (sources : List (Chart formula)) (parameter : Parameters sources) : Assignment n :=
  (sources.get parameter.1).lift parameter.2

theorem list_image {n : Nat} {formula : CNFFormula n} (sources : List (Chart formula)) (assignment : Assignment n) :
    (∃ parameter : Parameters sources, lift sources parameter = assignment) ↔
      ∃ source ∈ sources, ∃ parameter : source.Parameters, source.lift parameter = assignment := by
  constructor
  · rintro ⟨⟨i,parameter⟩,same⟩
    exact ⟨sources.get i,List.get_mem _ _,parameter,same⟩
  · rintro ⟨source,member,parameter,same⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp member
    exact ⟨⟨i,parameter⟩,same⟩

theorem generate_image {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    (∃ parameter : Parameters (generate formula), lift (generate formula) parameter = assignment) ↔
      CNFFormula.eval formula (extendAssignment assignment) = true := by
  rw [list_image]
  constructor
  · rintro ⟨source,member,parameter,same⟩
    obtain ⟨basis,present,rfl⟩ := List.mem_map.mp member
    exact ((chart_image formula basis (AffineCarrier.seed_valid formula basis present) assignment).mp ⟨parameter,same⟩).2
  · intro accepted
    have seed := AffineCarrier.seed_entails formula (extendAssignment assignment) accepted
    obtain ⟨basis,present,inBasis⟩ := List.any_eq_true.mp seed
    obtain ⟨parameter,same⟩ := (chart_image formula basis (AffineCarrier.seed_valid formula basis present) assignment).mpr ⟨inBasis,accepted⟩
    exact ⟨chart formula basis,List.mem_map.mpr ⟨basis,present,rfl⟩,parameter,same⟩

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool := (generate formula).any Chart.possible

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) : decideFormula formula = true ↔ CNFSatisfiable formula := by
  constructor
  · intro accepted
    obtain ⟨source,member,truth⟩ := List.any_eq_true.mp accepted
    obtain ⟨basis,present,rfl⟩ := List.mem_map.mp member
    obtain ⟨assignment,_,satisfies⟩ := (chart_possible formula basis (AffineCarrier.seed_valid formula basis present)).mp truth
    exact ⟨extendAssignment assignment,satisfies⟩
  · rintro ⟨assignment,accepted⟩
    let finite : Assignment n := fun i => assignment i.val
    have original := (formula_eval_restrict formula assignment).trans accepted
    have seed := AffineCarrier.seed_entails formula (extendAssignment finite) original
    obtain ⟨basis,present,inBasis⟩ := List.any_eq_true.mp seed
    apply List.any_eq_true.mpr
    exact ⟨chart formula basis,List.mem_map.mpr ⟨basis,present,rfl⟩,
      (chart_possible formula basis (AffineCarrier.seed_valid formula basis present)).mpr ⟨finite,inBasis,original⟩⟩

def sourceAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read (generate formula) assignment then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (source : Source n) : zeroProjector formula source = sourceAction formula source := by
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

end SaturationMonoid.ComplexityProjection.SATSource.AffineImageSource
