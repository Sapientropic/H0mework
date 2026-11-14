import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Image
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Cost

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineForget
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram

def mask (keep : List Nat) (assignment : Nat → Bool) : Nat → Bool :=
  fun i => if i ∈ keep then assignment i else false

def erase (keep : List Nat) (row : Row) : Row :=
  ⟨row.vars.filter (fun i => decide (i ∈ keep)),row.rhs⟩

theorem erase_parity (keep vars : List Nat) (assignment : Nat → Bool) :
    Parity.eval assignment (vars.filter (fun i => decide (i ∈ keep))) = Parity.eval (mask keep assignment) vars := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      by_cases retained : i ∈ keep <;> simp [retained,Parity.eval,mask,ih]

theorem erase_holds (keep : List Nat) (row : Row) (assignment : Nat → Bool) :
    (erase keep row).holds assignment = row.holds (mask keep assignment) := by
  simp only [erase,Row.holds,Row.eval,erase_parity]

theorem erased_holds (keep : List Nat) (rows : List Row) (assignment : Nat → Bool) :
    holds (rows.map (erase keep)) assignment = holds rows (mask keep assignment) := by
  simp only [holds,List.all_map]
  apply List.all_congr rfl
  intro row
  exact erase_holds keep row assignment

def source (n : Nat) (keep : List Nat) (basis : List Row) : Array Row :=
  let coordinates := Table.coordinates n basis
  Array.ofFn (fun i : Fin n => if i.val ∈ keep then coordinates.getD i.val Gates.zeroRow else Gates.zeroRow)

@[simp] theorem source_size (n : Nat) (keep : List Nat) (basis : List Row) : (source n keep basis).size = n := by
  simp [source]

theorem source_coordinate (n : Nat) (keep : List Nat) (basis : List Row) (parameters : Nat → Bool) :
    Gates.coordinate (source n keep basis) parameters = mask keep (Gates.coordinate (Table.coordinates n basis) parameters) := by
  funext i
  by_cases inside : i < n
  · by_cases retained : i ∈ keep
    · simp [Table.coordinate_getD,source,Array.getD_eq_getD_getElem?,inside,mask,retained]
    · simp [Table.coordinate_getD,source,Array.getD_eq_getD_getElem?,inside,mask,retained,Gates.value,Gates.zeroRow,Row.eval,Parity.eval]
  · have first := AtomImage.coordinate_outside (source n keep basis) parameters i (by simpa using Nat.le_of_not_gt inside)
    have second := AtomImage.coordinate_outside (Table.coordinates n basis) parameters i (by simpa using Nat.le_of_not_gt inside)
    rw [first]
    simp [mask,second]

theorem source_valid (n : Nat) (keep : List Nat) (basis : List Row) :
    Table.Valid (freeIndices n basis).length (source n keep basis) := by
  intro row member
  simp only [source,Array.toList_ofFn,List.mem_ofFn] at member
  obtain ⟨i,rfl⟩ := member
  split
  · exact Table.read_valid _ _ (Table.coordinates_valid n basis) i.val
  · exact Table.zero_valid _

theorem source_within (n : Nat) (keep : List Nat) (basis : List Row) :
    AtomImage.SourceWithin (freeIndices n basis).length (source n keep basis) :=
  fun row member => (source_valid n keep basis row member).2

structure Model where
  basis : List Row
  keep : List Nat
  table : Array Row
  image : AtomImage.State
  value : Result
  deriving Repr

/-- The same generated table and tagged image retain the original fibre. -/
def generate (n : Nat) (keep : List Nat) (basis : List Row) : Model :=
  let table := source n keep basis
  let image := AtomImage.generate table
  let projected := EliminateCost.run (image.kernel.map (erase keep))
  ⟨basis,keep,table,image,projected.result⟩

theorem generate_read (n : Nat) (keep : List Nat) (basis : List Row) (assignment : Nat → Bool) :
    (generate n keep basis).value.holds assignment =
      holds (AtomImage.generate (source n keep basis)).kernel (mask keep assignment) := by
  simp only [generate,EliminateCost.run_result,eliminate_holds,erased_holds]

theorem erase_within (n : Nat) (keep : List Nat) (row : Row) (inside : Parity.Within n row.vars) :
    Parity.Within n (erase keep row).vars := by
  intro i member
  exact inside i (List.mem_filter.mp member).1

theorem generate_valid (n : Nat) (keep : List Nat) (basis : List Row) :
    (generate n keep basis).value.triangular ∧ (generate n keep basis).value.within n := by
  have image := AtomImage.generate_valid _ _ (source_within n keep basis)
  have inside : RowsWithin n ((AtomImage.generate (source n keep basis)).kernel.map (erase keep)) := by
    intro row member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact erase_within n keep original (by simpa only [source_size] using (image.2 original present).2)
  simp only [generate,EliminateCost.run_result]
  exact ⟨eliminate_triangular _,eliminate_within n _ inside⟩

theorem source_parameter (n : Nat) (keep : List Nat) (basis : List Row) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    Gates.coordinate (source n keep basis) (extendAssignment parameters) =
      mask keep (extendAssignment (parameterLift n basis parameters)) := by
  rw [source_coordinate,Table.coordinates_value n basis inside,extend_parameterLift n basis inside]

theorem mask_eq_iff {n : Nat} (keep : List Nat) (left right : Assignment n) :
    mask keep (extendAssignment left) = mask keep (extendAssignment right) ↔
      ∀ i : Fin n, i.val ∈ keep → left i=right i := by
  constructor
  · intro same i retained
    simpa [mask,retained] using congrFun same i.val
  · intro same
    funext i
    by_cases retained : i ∈ keep
    · by_cases inside : i < n
      · simpa [mask,retained,extendAssignment,inside] using same ⟨i,inside⟩ retained
      · simp [mask,retained,extendAssignment,inside]
    · simp [mask,retained]

def observed (n : Nat) (keep : List Nat) (basis : List Row) (assignment : Assignment n) :
    Assignment (source n keep basis).size := fun i => mask keep (extendAssignment assignment) i.val

theorem observed_extend (n : Nat) (keep : List Nat) (basis : List Row) (assignment : Assignment n) :
    extendAssignment (observed n keep basis assignment) = mask keep (extendAssignment assignment) := by
  funext i
  by_cases inside : i < n
  · simp [extendAssignment,source_size,inside,observed]
  · simp [extendAssignment,source_size,inside,mask]

def recover (n : Nat) (model : Model) (assignment : Assignment n) : Assignment n :=
  let width := (freeIndices n model.basis).length
  let decoder := AtomImage.backTable model.image.basis (AtomImage.zeroTable width)
  let target : Assignment model.table.size := fun i => mask model.keep (extendAssignment assignment) i.val
  parameterLift n model.basis (Gates.lift width decoder target)

theorem recover_holds (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    holds basis (extendAssignment (recover n (generate n keep basis) assignment)) = true :=
  parameterLift_holds n basis valid.1 valid.2 _

theorem recover_agrees (n : Nat) (keep : List Nat) (basis : List Row) (inside : RowsWithin n basis)
    (assignment : Assignment n) (accepted : (generate n keep basis).value.holds (extendAssignment assignment)=true)
    (i : Fin n) (retained : i.val ∈ keep) :
    recover n (generate n keep basis) assignment i = assignment i := by
  rw [generate_read] at accepted
  have kernel : holds (AtomImage.generate (source n keep basis)).kernel
      (extendAssignment (observed n keep basis assignment)) = true := by
    rw [observed_extend]
    exact accepted
  let index : Fin (source n keep basis).size := ⟨i.val,by simpa only [source_size] using i.isLt⟩
  have realized := AtomImage.representative_recovers (freeIndices n basis).length (source n keep basis)
    (source_within n keep basis) (observed n keep basis assignment) kernel index
  rw [source_parameter n keep basis inside] at realized
  change mask keep (extendAssignment (recover n (generate n keep basis) assignment)) i.val =
    observed n keep basis assignment index at realized
  simpa [observed,index,mask,retained] using realized

theorem generate_image (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (assignment : Assignment n) :
    (generate n keep basis).value.holds (extendAssignment assignment)=true ↔
      ∃ original : Assignment n, holds basis (extendAssignment original)=true ∧
        ∀ i : Fin n, i.val ∈ keep → original i=assignment i := by
  constructor
  · intro accepted
    exact ⟨recover n (generate n keep basis) assignment,recover_holds n keep basis valid assignment,
      recover_agrees n keep basis valid.2 assignment accepted⟩
  · rintro ⟨original,accepted,agrees⟩
    let parameters := projectFree n basis original
    have originalLift := parameterLift_projectFree n basis valid.1 original accepted
    have realized : AtomImage.Realizes (source n keep basis) (extendAssignment parameters)
        (mask keep (extendAssignment assignment)) := by
      intro i
      rw [source_parameter n keep basis valid.2,originalLift,(mask_eq_iff keep original assignment).mpr agrees]
    rw [generate_read]
    exact (AtomImage.image_iff_kernel _ _).mp ⟨extendAssignment parameters,realized⟩

def FibreParameters (n : Nat) (model : Model) (assignment : Assignment n) : Type :=
  Assignment (freeIndices (freeIndices n model.basis).length
    (model.image.rows (mask model.keep (extendAssignment assignment)))).length

def fibreLift (n : Nat) (model : Model) (assignment : Assignment n) (parameters : FibreParameters n model assignment) : Assignment n :=
  parameterLift n model.basis (parameterLift (freeIndices n model.basis).length
    (model.image.rows (mask model.keep (extendAssignment assignment))) parameters)

theorem fibre_relation (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (before after : Assignment n)
    (accepted : holds basis (extendAssignment before)=true) :
    (holds ((generate n keep basis).image.rows (mask keep (extendAssignment after)))
        (extendAssignment (projectFree n basis before))=true ∧
      (generate n keep basis).value.holds (extendAssignment after)=true) ↔
        ∀ i : Fin n, i.val ∈ keep → before i=after i := by
  rw [generate_read]
  change (holds ((AtomImage.generate (source n keep basis)).rows _) _ =true ∧
    holds (AtomImage.generate (source n keep basis)).kernel _=true) ↔ _
  rw [AffineClauseImage.fibre_realizes]
  have original := parameterLift_projectFree n basis valid.1 before accepted
  constructor
  · intro realized i retained
    let index : Fin (source n keep basis).size := ⟨i.val,by simpa only [source_size] using i.isLt⟩
    have same := realized index
    rw [source_parameter n keep basis valid.2,original] at same
    simpa [index,mask,retained] using same
  · intro agrees i
    rw [source_parameter n keep basis valid.2,original,(mask_eq_iff keep before after).mpr agrees]

theorem fibreLift_image (n : Nat) (keep : List Nat) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (after : Assignment n)
    (accepted : (generate n keep basis).value.holds (extendAssignment after)=true) (before : Assignment n) :
    (∃ parameters : FibreParameters n (generate n keep basis) after,
      fibreLift n (generate n keep basis) after parameters=before) ↔
      holds basis (extendAssignment before)=true ∧ ∀ i : Fin n, i.val ∈ keep → before i=after i := by
  let rows := (AtomImage.generate (source n keep basis)).rows (mask keep (extendAssignment after))
  have triangular := AffineClauseImage.fibre_triangular (source n keep basis) (mask keep (extendAssignment after))
  have inside := AffineClauseImage.fibre_within (freeIndices n basis).length (source n keep basis)
    (source_within n keep basis) (mask keep (extendAssignment after))
  constructor
  · rintro ⟨parameters,rfl⟩
    let originalParameters := parameterLift (freeIndices n basis).length rows parameters
    have inBasis := parameterLift_holds n basis valid.1 valid.2 originalParameters
    refine ⟨inBasis,?_⟩
    apply (fibre_relation n keep basis valid _ after inBasis).mp
    refine ⟨?_,accepted⟩
    change holds rows (extendAssignment (projectFree n basis (parameterLift n basis originalParameters)))=true
    rw [projectFree_parameterLift]
    exact parameterLift_holds _ rows triangular inside parameters
  · rintro ⟨inBasis,agrees⟩
    have inFibre := ((fibre_relation n keep basis valid before after inBasis).mpr agrees).1
    let originalParameters := projectFree n basis before
    refine ⟨projectFree (freeIndices n basis).length rows originalParameters,?_⟩
    change parameterLift n basis (parameterLift (freeIndices n basis).length rows
      (projectFree (freeIndices n basis).length rows originalParameters))=before
    rw [parameterLift_projectFree _ rows triangular originalParameters inFibre,
      parameterLift_projectFree n basis valid.1 before inBasis]

def future {n : Nat} (formula : CNFFormula n) : List Nat := (Shared.sourceVars formula).map Fin.val

theorem future_agrees {n : Nat} (formula : CNFFormula n) (left right : Assignment n)
    (agree : ∀ i : Fin n, i.val ∈ future formula → left i=right i) :
    CNFFormula.eval formula (extendAssignment left) = CNFFormula.eval formula (extendAssignment right) := by
  apply Factor.formula_eval_agree
  intro clause member literal present
  have retained : literal.var.val ∈ future formula :=
    List.mem_map.mpr ⟨literal.var,Shared.sourceVars_supported formula clause member literal present,rfl⟩
  simpa using agree literal.var retained

theorem generate_future {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (∃ assignment : Assignment n, (generate n (future formula) basis).value.holds (extendAssignment assignment)=true ∧
      CNFFormula.eval formula (extendAssignment assignment)=true) ↔
    (∃ assignment : Assignment n, holds basis (extendAssignment assignment)=true ∧
      CNFFormula.eval formula (extendAssignment assignment)=true) := by
  constructor
  · rintro ⟨assignment,projected,accepted⟩
    obtain ⟨original,inside,agrees⟩ := (generate_image n (future formula) basis valid assignment).mp projected
    exact ⟨original,inside,(future_agrees formula original assignment agrees).trans accepted⟩
  · rintro ⟨assignment,inside,accepted⟩
    exact ⟨assignment,(generate_image n (future formula) basis valid assignment).mpr ⟨assignment,inside,by simp⟩,accepted⟩

def cells (n : Nat) (keep : List Nat) (original : AffineCarrier.Cells) : AffineCarrier.Cells :=
  original.flatMap fun basis => (AffineCarrier.pack (generate n keep basis).value).value

theorem cells_valid (n : Nat) (keep : List Nat) (original : AffineCarrier.Cells) :
    AffineCarrier.Valid n (cells n keep original) := by
  intro basis member
  obtain ⟨before,_,present⟩ := List.mem_flatMap.mp member
  have valid := generate_valid n keep before
  exact AffineCarrier.pack_valid n _ valid.1 valid.2 basis present

theorem cells_length (n : Nat) (keep : List Nat) (original : AffineCarrier.Cells) :
    (cells n keep original).length ≤ original.length := by
  induction original with
  | nil => rfl
  | cons basis rest ih =>
      have first := AffineCarrier.Cost.pack_length (generate n keep basis).value
      simp only [cells,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
      omega

theorem cells_image (n : Nat) (keep : List Nat) (original : AffineCarrier.Cells)
    (valid : AffineCarrier.Valid n original) (assignment : Assignment n) :
    AffineCarrier.read (cells n keep original) (extendAssignment assignment)=true ↔
      ∃ before : Assignment n, AffineCarrier.read original (extendAssignment before)=true ∧
        ∀ i : Fin n, i.val ∈ keep → before i=assignment i := by
  induction original with
  | nil => simp [cells,AffineCarrier.read]
  | cons basis rest ih =>
      have first := valid basis (by simp)
      have tail : AffineCarrier.Valid n rest := fun b member => valid b (by simp [member])
      change AffineCarrier.read ((AffineCarrier.pack (generate n keep basis).value).value++cells n keep rest)
        (extendAssignment assignment)=true ↔ _
      simp only [AffineCarrier.read_append,AffineCarrier.read_pack,Bool.or_eq_true]
      rw [generate_image n keep basis first,ih tail]
      constructor
      · rintro (⟨before,inside,agrees⟩ | ⟨before,inside,agrees⟩)
        · refine ⟨before,?_,agrees⟩
          change (holds basis (extendAssignment before) || AffineCarrier.read rest (extendAssignment before))=true
          simp only [Bool.or_eq_true]
          exact Or.inl inside
        · refine ⟨before,?_,agrees⟩
          change (holds basis (extendAssignment before) || AffineCarrier.read rest (extendAssignment before))=true
          simp only [Bool.or_eq_true]
          exact Or.inr inside
      · rintro ⟨before,inside,agrees⟩
        change (holds basis (extendAssignment before) || AffineCarrier.read rest (extendAssignment before))=true at inside
        simp only [Bool.or_eq_true] at inside
        rcases inside with head | tail
        · exact Or.inl ⟨before,head,agrees⟩
        · exact Or.inr ⟨before,tail,agrees⟩

theorem cells_future {n : Nat} (formula : CNFFormula n) (original : AffineCarrier.Cells)
    (valid : AffineCarrier.Valid n original) :
    (∃ assignment : Assignment n, AffineCarrier.read (cells n (future formula) original) (extendAssignment assignment)=true ∧
      CNFFormula.eval formula (extendAssignment assignment)=true) ↔
    (∃ assignment : Assignment n, AffineCarrier.read original (extendAssignment assignment)=true ∧
      CNFFormula.eval formula (extendAssignment assignment)=true) := by
  constructor
  · rintro ⟨assignment,projected,accepted⟩
    obtain ⟨before,inside,agrees⟩ := (cells_image n (future formula) original valid assignment).mp projected
    exact ⟨before,inside,(future_agrees formula before assignment agrees).trans accepted⟩
  · rintro ⟨assignment,inside,accepted⟩
    exact ⟨assignment,(cells_image n (future formula) original valid assignment).mpr ⟨assignment,inside,by simp⟩,accepted⟩

theorem row_support_within (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula)
    (i : Nat) (member : i ∈ AffineClauseProduct.support formula) : i < n := by
  simp only [AffineClauseProduct.support,List.mem_dedup,List.mem_flatMap,List.mem_flatten] at member
  obtain ⟨row,⟨clause,present,hit⟩,term⟩ := member
  exact inside clause present row hit i term

theorem row_future_agrees (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula)
    (left right : Assignment n)
    (agree : ∀ i : Fin n, i.val ∈ AffineClauseProduct.support formula → left i=right i) :
    AffineClauses.formulaRead formula (extendAssignment left) = AffineClauses.formulaRead formula (extendAssignment right) := by
  apply AffineClauseProduct.formula_agree
  intro clause present row hit i term
  have bounded := inside clause present row hit i term
  have member := AffineClauseProduct.variable_mem formula clause present row hit i term
  simpa only [extendAssignment,bounded,↓reduceDIte] using agree ⟨i,bounded⟩ member

theorem cells_row_future (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula)
    (original : AffineCarrier.Cells) (valid : AffineCarrier.Valid n original) :
    (∃ assignment : Assignment n,
      AffineCarrier.read (cells n (AffineClauseProduct.support formula) original) (extendAssignment assignment)=true ∧
        AffineClauses.formulaRead formula (extendAssignment assignment)=true) ↔
    (∃ assignment : Assignment n, AffineCarrier.read original (extendAssignment assignment)=true ∧
      AffineClauses.formulaRead formula (extendAssignment assignment)=true) := by
  constructor
  · rintro ⟨assignment,projected,accepted⟩
    obtain ⟨before,inhabited,agrees⟩ := (cells_image n (AffineClauseProduct.support formula) original valid assignment).mp projected
    exact ⟨before,inhabited,(row_future_agrees n formula inside before assignment agrees).trans accepted⟩
  · rintro ⟨assignment,inhabited,accepted⟩
    exact ⟨assignment,(cells_image n (AffineClauseProduct.support formula) original valid assignment).mpr
      ⟨assignment,inhabited,by simp⟩,accepted⟩

end SaturationMonoid.ComplexityProjection.SATSource.AffineForget
