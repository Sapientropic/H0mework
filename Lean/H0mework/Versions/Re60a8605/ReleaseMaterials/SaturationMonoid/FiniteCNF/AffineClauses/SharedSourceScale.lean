import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.SharedSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ForgetCost

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineSharedSource.Scale
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula formulaSize Within)
open AffineClauses.Cost (rowCount termCount)
open CapacityMatching.RowCost (rowCells rowsCells)

private theorem body_canonical (formula : Formula) :
    AffineClauses.Future.body (AffineJointResidual.canonicalRows formula)=
      AffineJointResidual.canonicalRows (AffineClauses.Future.body formula) := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [AffineJointResidual.canonicalRows,List.map_cons,AffineClauses.Future.body,
        List.filter_cons,List.length_map] at ih ⊢
      split <;> simp_all

theorem pending_sublist (formula : Formula) :
    List.Sublist (generate formula).pending
      (AffineJointResidual.canonicalRows (AffineClauses.Future.body
        (AffineClauseImage.liftCNF (AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
          (AtomImage.generate (AffineClauseImage.table formula)).kernel).query))) := by
  let output := AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
    (AtomImage.generate (AffineClauseImage.table formula)).kernel
  change List.Sublist (AffineClauses.Future.body (AffineClauses.cleanRun
    (AffineJointResidual.canonicalRows (AffineJointEmission.constraints output))).value) _
  rw [AffineClauses.cleanRun_value]
  have cleaned : List.Sublist (AffineClauses.clean (AffineJointResidual.canonicalRows
      (AffineJointEmission.constraints output)))
      (AffineJointResidual.canonicalRows (AffineJointEmission.constraints output)) := List.filter_sublist
  have subset := cleaned.filter (fun clause => Decidable.decide (2 ≤ clause.length))
  change List.Sublist (AffineClauses.Future.body (AffineClauses.clean _)) (AffineClauses.Future.body _) at subset
  rw [body_canonical] at subset
  apply subset.trans
  have query := (AffineJointEmission.constraints_body_sublist output).map (fun clause : Clause => clause.map Atoms.canonical)
  simpa only [AffineJointResidual.canonicalRows,AffineClauses.Future.body] using query

private theorem rowCount_sublist {left right : Formula} (subset : List.Sublist left right) :
    rowCount left ≤ rowCount right := by
  have bounds := subset.flatten.length_le
  simpa only [List.length_flatten,rowCount] using bounds

theorem pending_length (formula : Formula) :
    (generate formula).pending.length ≤ formula.length+1+4*(rowCount formula+1)^2 := by
  have bounds := (pending_sublist formula).length_le
  rw [AffineJointResidual.canonical_length] at bounds
  have filtered := List.length_filter_le (fun clause => Decidable.decide (2 ≤ clause.length))
    (AffineClauseImage.liftCNF (AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
      (AtomImage.generate (AffineClauseImage.table formula)).kernel).query)
  have query := AffineJointEmission.emit_length (AffineClauseImage.atomFormula formula)
    (AtomImage.generate (AffineClauseImage.table formula)).kernel
  have base : (AffineClauseImage.atomFormula formula).length=formula.length+1 := by
    change (Atoms.compile (AffineClauseImage.violations formula)).length=formula.length+1
    simpa only [AffineClauseImage.violations,List.length_map] using
      Atoms.compile_length (AffineClauseImage.violations formula)
  have dimension := AffineJointResidual.observation_width formula
  simp only [AffineClauseImage.liftCNF,List.length_map] at filtered
  change (AffineClauses.Future.body _).length ≤ _ at filtered
  rw [base] at query
  have actual := bounds.trans (filtered.trans query)
  have square := Nat.mul_le_mul dimension dimension
  nlinarith

theorem pending_rows (formula : Formula) :
    rowCount (generate formula).pending ≤ rowCount formula+1+8*(rowCount formula+1)^2 := by
  have bounds := rowCount_sublist (pending_sublist formula)
  rw [AffineJointResidual.canonical_rows] at bounds
  have filtered : List.Sublist (AffineClauses.Future.body
      (AffineClauseImage.liftCNF (AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
        (AtomImage.generate (AffineClauseImage.table formula)).kernel).query))
      (AffineClauseImage.liftCNF (AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
        (AtomImage.generate (AffineClauseImage.table formula)).kernel).query) := List.filter_sublist
  have query := AffineJointEmission.emit_literals (AffineClauseImage.atomFormula formula)
    (AtomImage.generate (AffineClauseImage.table formula)).kernel
  have base : Extract.literalCount (AffineClauseImage.atomFormula formula)=rowCount formula+1 := by
    change Extract.literalCount (Atoms.compile (AffineClauseImage.violations formula))=rowCount formula+1
    simp [Atoms.compile,Atoms.clause,AffineClauseImage.violations,Extract.literalCount,rowCount,Function.comp_def,Nat.add_comm]
  have actual := bounds.trans (rowCount_sublist filtered)
  have counts {q : Nat} (input : CNFFormula q) : rowCount (AffineClauseImage.liftCNF input)=Extract.literalCount input := by
    simp [rowCount,AffineClauseImage.liftCNF,Extract.literalCount,Function.comp_def]
  rw [counts] at actual
  rw [base] at query
  have dimension := AffineJointResidual.observation_width formula
  have square := Nat.mul_le_mul dimension dimension
  nlinarith

theorem pending_atom (formula : Formula) (clause : Clause) (member : clause ∈ (generate formula).pending)
    (row : Row) (present : row ∈ clause) : row.vars.length=1 := by
  have included := (pending_sublist formula).subset member
  obtain ⟨original,inBody,rfl⟩ := List.mem_map.mp included
  obtain ⟨source,inClause,rfl⟩ := List.mem_map.mp present
  have inQuery := (List.mem_filter.mp inBody).1
  obtain ⟨query,_,rfl⟩ := List.mem_map.mp inQuery
  obtain ⟨literal,_,rfl⟩ := List.mem_map.mp inClause
  simp [Atoms.canonical,AffineCarrier.trueRow]

theorem pending_terms (formula : Formula) :
    termCount (generate formula).pending ≤ rowCount formula+1+8*(rowCount formula+1)^2 := by
  have exactTerms : termCount (generate formula).pending=rowCount (generate formula).pending := by
    have each (clause : Clause) (member : clause ∈ (generate formula).pending) :
        Gates.rowTerms clause=clause.length := by
      have same : clause.map (fun row => row.vars.length)=clause.map (fun _ => 1) := by
        apply List.map_congr_left
        intro row present
        exact pending_atom formula clause member row present
      unfold Gates.rowTerms
      rw [same]
      simp
    have same : (generate formula).pending.map Gates.rowTerms=(generate formula).pending.map List.length := by
      apply List.map_congr_left
      exact each
    exact congrArg List.sum same
  rw [exactTerms]
  exact pending_rows formula

theorem pending_size (formula : Formula) :
    formulaSize (generate formula).pending ≤ 3*rowCount formula+formula.length+28*(rowCount formula+1)^2+5 := by
  have clauses := pending_length formula
  have rows := pending_rows formula
  have terms := pending_terms formula
  rw [AffineClauses.Cost.formula_size]
  omega

theorem width_bound (formula : Formula) : width (generate formula) ≤ rowCount formula+1 := by
  rw [generate_width]
  exact AffineJointResidual.observation_width formula

theorem seed_basis_length (n : Nat) (formula : Formula) (inside : Within n formula)
    (basis : List Row) (stored : (generate formula).seed=.basis basis) :
    basis.length ≤ width (generate formula) := by
  have valid := generate_bounded n formula inside
  rw [Bounded,stored] at valid
  exact basis_length_le _ basis valid.1 valid.2.1

theorem seed_storage (n : Nat) (formula : Formula) (inside : Within n formula) :
    AffineCarrier.resultSize (generate formula).seed ≤
      (rowCount formula+1)*(rowCount formula+3)+2 := by
  have valid := generate_bounded n formula inside
  have bound := AffineCarrier.Cost.result_size (width (generate formula)) (generate formula).seed valid.1 valid.2.1
  have dimension := width_bound formula
  have terms := Nat.mul_le_mul dimension (show width (generate formula)+2 ≤ rowCount formula+3 by omega)
  simp only [AffineCarrier.Cost.cellBound] at bound
  omega

private theorem keys_terms (formula : Formula) :
    ((Atoms.keys formula).map List.length).sum ≤ Gates.rowTerms formula.flatten := by
  have subset := (List.dedup_sublist ([]::formula.flatten.map Row.vars)).map List.length
  have bound := subset.sum_le_sum (fun value _ => Nat.zero_le value)
  simpa only [Atoms.keys,List.map_cons,List.length_nil,List.sum_cons,Nat.zero_add,
    List.map_map,Function.comp_def,Gates.rowTerms] using bound

private theorem violation_terms (formula : Formula) :
    Gates.rowTerms (AffineClauseImage.violations formula).flatten=termCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [AffineClauseImage.violations,List.map_cons,List.flatten_cons,
        Gates.rowTerms,List.map_append,List.sum_append,List.map_map,Function.comp_def,
        Propagation.flip,AffineClauses.Cost.termCount_cons] at ih ⊢
      exact congrArg (Gates.rowTerms clause+·) ih

theorem table_terms (formula : Formula) : Gates.rowTerms (generate formula).table.toList ≤ termCount formula := by
  rw [generate_table]
  simp only [AffineClauseImage.table,Atoms.table,List.toList_toArray,Gates.rowTerms,
    List.map_map,Function.comp_def]
  exact (keys_terms (AffineClauseImage.violations formula)).trans_eq (violation_terms formula)

theorem table_storage (formula : Formula) :
    AffineCollect.tableSize (generate formula).table ≤ formulaSize formula+2 := by
  have terms := table_terms formula
  have dimension := width_bound formula
  have count : (generate formula).table.toList.length=width (generate formula) := by simp [width]
  rw [AffineCollect.tableSize,AffineCollect.Cost.rows_size,count,AffineClauses.Cost.formula_size]
  omega

private theorem tag_terms (rows : List AtomImage.Tagged) :
    AtomImage.tagTerms rows = Gates.rowTerms (rows.map AtomImage.Tagged.coeff)+
      Gates.rowTerms (rows.map AtomImage.Tagged.label) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [AtomImage.tagTerms,Gates.rowTerms,List.map_cons,List.map_map,
        List.sum_cons,Function.comp_def,AtomImage.Tagged.coeff] at ih ⊢
      omega

theorem imageSize_eq (image : AtomImage.State) :
    AffineForget.Cost.imageSize image = Gates.rowTerms image.coeffs+
      Gates.rowTerms (image.basis.map AtomImage.Tagged.label++image.kernel)+
      3*image.basis.length+2*image.kernel.length+2 := by
  rw [AffineForget.Cost.imageSize,AffineForget.Cost.tagsSize_eq,tag_terms,AffineCollect.Cost.rows_size]
  simp only [AtomImage.State.coeffs,Gates.rowTerms,List.map_append,List.sum_append]
  omega

theorem image_labels (n : Nat) (formula : Formula) (inside : Within n formula) :
    Gates.rowTerms ((generate formula).image.basis.map AtomImage.Tagged.label++(generate formula).image.kernel) ≤
      width (generate formula)*width (generate formula) := by
  rw [generate_image,generate_width]
  simpa only [AffineClauseImage.table_size] using
    AtomImage.generated_label_storage n (AffineClauseImage.table formula) (AffineClauseImage.source_within n formula inside)

theorem image_coeffs (n : Nat) (formula : Formula) (inside : Within n formula) :
    Gates.rowTerms (generate formula).image.coeffs ≤ n*n := by
  rw [generate_image]
  exact AtomImage.generated_coeff_storage n (AffineClauseImage.table formula)
    (AffineClauseImage.source_within n formula inside)

theorem image_storage (n : Nat) (formula : Formula) (inside : Within n formula) :
    AffineForget.Cost.imageSize (generate formula).image ≤
      n*n+(rowCount formula+1)*(rowCount formula+1)+3*(rowCount formula+1)+2 := by
  have labels := image_labels n formula inside
  have coeffs := image_coeffs n formula inside
  have count : (generate formula).image.basis.length+(generate formula).image.kernel.length=width (generate formula) := by
    rw [generate_image,generate_width]
    simpa only [AffineClauseImage.table_size] using AtomImage.generate_count (AffineClauseImage.table formula)
  have dimension := width_bound formula
  have square := Nat.mul_le_mul dimension dimension
  rw [imageSize_eq]
  omega

/-- Full record units for the actual four Model fields, using their existing size conventions. -/
def modelSize (model : Model) : Nat :=
  AffineCollect.tableSize model.table+AffineForget.Cost.imageSize model.image+
    AffineCarrier.resultSize model.seed+formulaSize model.pending+4

theorem model_storage (n : Nat) (formula : Formula) (inside : Within n formula) :
    modelSize (generate formula) ≤ formulaSize formula+n*n+
      30*(rowCount formula+1)*(rowCount formula+1)+5*(rowCount formula+1)+
      3*rowCount formula+formula.length+15 := by
  have table := table_storage formula
  have image := image_storage n formula inside
  have seed := seed_storage n formula inside
  have pending := pending_size formula
  unfold modelSize
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.AffineSharedSource.Scale
