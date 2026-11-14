import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Product

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineCoordinateProduct

open SaturationMonoid.ComplexityProjection.SATSource.Affine

structure Chart (n : Nat) where
  basis : List Row
  model : AffineClauseProduct.Tree (freeIndices n basis).length

def chart {n : Nat} (formula : CNFFormula n) (basis : List Row) : Chart n :=
  let table := Table.coordinates n basis
  let original := AffineClauses.compile table formula
  ⟨basis,AffineClauseProduct.generate (freeIndices n basis).length original⟩

def Chart.read {n : Nat} (source : Chart n) (assignment : Assignment n) : Bool :=
  holds source.basis (extendAssignment assignment) && AffineClauseProduct.read source.model
    (extendAssignment (projectFree n source.basis assignment))

def Chart.Parameters {n : Nat} (source : Chart n) : Type := AffineClauseProduct.Parameters source.model

def Chart.lift {n : Nat} (source : Chart n) (parameter : source.Parameters) : Assignment n :=
  parameterLift n source.basis (AffineClauseProduct.lift source.model parameter)

theorem chart_source {n : Nat} (formula : CNFFormula n) (basis : List Row) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    AffineClauseProduct.read (chart formula basis).model (extendAssignment parameters) =
      CNFFormula.eval formula (extendAssignment (parameterLift n basis parameters)) := by
  have bounded := AffineClauses.compile_within _ _ (Table.coordinates_valid n basis) formula
  rw [chart,AffineClauseProduct.generate_read _ _ bounded]
  exact (AffineClauses.generate_read _ _ bounded _).symm.trans
    (AffineClauses.coordinate_read formula basis inside parameters)

theorem chart_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    (chart formula basis).read assignment =
      (holds basis (extendAssignment assignment) && CNFFormula.eval formula (extendAssignment assignment)) := by
  change (holds basis (extendAssignment assignment) &&
    AffineClauseProduct.read (chart formula basis).model (extendAssignment (projectFree n basis assignment))) = _
  rw [chart_source formula basis valid.2]
  by_cases accepted : holds basis (extendAssignment assignment) = true
  · rw [parameterLift_projectFree n basis valid.1 assignment accepted]
  · simp [Bool.eq_false_iff.mpr accepted]

theorem chart_image {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    (∃ parameter : (chart formula basis).Parameters, (chart formula basis).lift parameter = assignment) ↔
      holds basis (extendAssignment assignment) = true ∧ CNFFormula.eval formula (extendAssignment assignment) = true := by
  let data := AffineClauses.compile (Table.coordinates n basis) formula
  have bounded := AffineClauses.compile_within _ _ (Table.coordinates_valid n basis) formula
  constructor
  · rintro ⟨parameter,rfl⟩
    let coordinates := AffineClauseProduct.lift (chart formula basis).model parameter
    have modelAccepted : AffineClauses.formulaRead data (extendAssignment coordinates) = true :=
      (AffineClauseProduct.generate_image _ data bounded coordinates).mp ⟨parameter,rfl⟩
    have modelRead : AffineClauseProduct.read (chart formula basis).model (extendAssignment coordinates) = true :=
      (AffineClauseProduct.generate_read _ data bounded _).trans modelAccepted
    exact ⟨parameterLift_holds n basis valid.1 valid.2 coordinates,
      (chart_source formula basis valid.2 coordinates).symm.trans modelRead⟩
  · rintro ⟨inBasis,accepted⟩
    let coordinates := projectFree n basis assignment
    have lifted := parameterLift_projectFree n basis valid.1 assignment inBasis
    have modelRead : AffineClauseProduct.read (chart formula basis).model (extendAssignment coordinates) = true := by
      rw [chart_source formula basis valid.2]
      exact (congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) lifted).trans accepted
    have modelAccepted := (AffineClauseProduct.generate_read _ data bounded _).symm.trans modelRead
    obtain ⟨parameter,same⟩ := (AffineClauseProduct.generate_image _ data bounded coordinates).mpr modelAccepted
    refine ⟨parameter,?_⟩
    change parameterLift n basis
      (AffineClauseProduct.lift (AffineClauseProduct.generate (freeIndices n basis).length data) parameter) = assignment
    rw [same]
    exact lifted

theorem chart_possible {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    AffineClauseProduct.possible (chart formula basis).model = true ↔
      ∃ assignment : Assignment n, holds basis (extendAssignment assignment) = true ∧
        CNFFormula.eval formula (extendAssignment assignment) = true := by
  let data := AffineClauses.compile (Table.coordinates n basis) formula
  have bounded := AffineClauses.compile_within _ _ (Table.coordinates_valid n basis) formula
  change AffineClauseProduct.possible (AffineClauseProduct.generate (freeIndices n basis).length data) = true ↔ _
  rw [AffineClauseProduct.generate_possible _ data bounded]
  constructor
  · rintro ⟨point,accepted⟩
    let coordinates : Assignment (freeIndices n basis).length := fun i => point i.val
    have finite := (AffineClauseProduct.formula_restrict _ data bounded point).trans accepted
    obtain ⟨parameter,_⟩ := (AffineClauseProduct.generate_image _ data bounded coordinates).mpr finite
    exact ⟨(chart formula basis).lift parameter,(chart_image formula basis valid _).mp ⟨parameter,rfl⟩⟩
  · rintro ⟨assignment,inBasis,accepted⟩
    let coordinates := projectFree n basis assignment
    have lifted := parameterLift_projectFree n basis valid.1 assignment inBasis
    refine ⟨extendAssignment coordinates,?_⟩
    have same := (AffineClauseProduct.generate_read _ data bounded _).symm.trans
      (chart_source formula basis valid.2 coordinates)
    exact same.trans ((congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) lifted).trans accepted)

def generate {n : Nat} (formula : CNFFormula n) : List (Chart n) :=
  let initial := AffineCarrier.seed formula
  initial.value.map (chart formula)

def read {n : Nat} (sources : List (Chart n)) (assignment : Assignment n) : Bool := sources.any (fun source => source.read assignment)

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

def Parameters {n : Nat} (sources : List (Chart n)) := (i : Fin sources.length) × (sources.get i).Parameters

def lift {n : Nat} (sources : List (Chart n)) (parameter : Parameters sources) : Assignment n :=
  (sources.get parameter.1).lift parameter.2

theorem list_image {n : Nat} (sources : List (Chart n)) (assignment : Assignment n) :
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

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  (generate formula).any (fun source => AffineClauseProduct.possible source.model)

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

end SaturationMonoid.ComplexityProjection.SATSource.AffineCoordinateProduct
