import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Product

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauseImage

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula clauseRead formulaRead Within)
open InterferenceProgram

def violations (formula : Formula) : Formula := formula.map (fun clause => clause.map Propagation.flip)
def width (formula : Formula) : Nat := (Atoms.keys (violations formula)).length

def table (formula : Formula) : Array Row := Atoms.table (violations formula)

theorem table_size (formula : Formula) : (table formula).size = width formula := by simp [table,width,Atoms.table]

def atomFormula (formula : Formula) : CNFFormula (width formula) := Atoms.compile (violations formula)

theorem atomFormula_read (formula : Formula) (input : Nat → Bool) :
    CNFFormula.eval (atomFormula formula) (Gates.coordinate (table formula) input) = formulaRead formula input := by
  change CNFFormula.eval (Atoms.compile (violations formula)) (Atoms.read (violations formula) input) = _
  rw [Atoms.compile_value]
  simp only [violations,List.all_map,Function.comp_def,AffineClauses.flip_clause,Bool.not_not,formulaRead]

theorem source_within (n : Nat) (formula : Formula) (inside : Within n formula) : AtomImage.SourceWithin n (table formula) := by
  intro row member i hit
  simp only [table,Atoms.table,List.toList_toArray,List.mem_map] at member
  obtain ⟨terms,member,rfl⟩ := member
  simp only [Atoms.keys,List.mem_dedup,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨row,member,rfl⟩
  · cases hit
  · obtain ⟨clause,inFormula,inClause⟩ := List.mem_flatten.mp member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp inFormula
    obtain ⟨originalRow,presentRow,rfl⟩ := List.mem_map.mp inClause
    exact inside original present originalRow presentRow i hit

def liftCNF {n : Nat} (formula : CNFFormula n) : Formula := formula.map (fun clause => clause.map AffineCarrier.trueRow)

theorem liftCNF_read {n : Nat} (formula : CNFFormula n) (input : Nat → Bool) :
    formulaRead (liftCNF formula) input = CNFFormula.eval formula input := by
  simp [liftCNF,formulaRead,clauseRead,Function.comp_def,CNFFormula.eval,CNFClause.eval,AffineCarrier.trueRow_holds]

theorem liftCNF_within {n : Nat} (formula : CNFFormula n) : Within n (liftCNF formula) := by
  intro clause member row present
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  obtain ⟨literal,_,rfl⟩ := List.mem_map.mp present
  exact AffineCarrier.trueRow_within literal

def constraints (formula : Formula) (state : AtomImage.State) : Formula :=
  liftCNF (atomFormula formula)++state.kernel.map (fun row => [row])

theorem constraints_read (formula : Formula) (state : AtomImage.State) (target : Nat → Bool) :
    formulaRead (constraints formula state) target =
      (CNFFormula.eval (atomFormula formula) target && holds state.kernel target) := by
  simp only [constraints,formulaRead,List.all_append,List.all_map,Function.comp_def]
  change (formulaRead (liftCNF (atomFormula formula)) target &&
    state.kernel.all (fun row => clauseRead [row] target)) = _
  rw [liftCNF_read]
  simp [clauseRead,holds]

theorem constraints_within (n : Nat) (formula : Formula) (inside : Within n formula) :
    Within (width formula) (constraints formula (AtomImage.generate (table formula))) := by
  intro clause member
  rcases List.mem_append.mp member with old | fresh
  · exact liftCNF_within (atomFormula formula) clause old
  · obtain ⟨row,present,rfl⟩ := List.mem_map.mp fresh
    have bounded := ((AtomImage.generate_valid n (table formula) (source_within n formula inside)).2 row present).2
    rw [table_size] at bounded
    intro original present
    have same : original=row := List.mem_singleton.mp present
    exact same ▸ bounded

structure Model (formula : Formula) where
  image : AtomImage.State
  tree : AffineClauseProduct.Tree (width formula)

def generate (formula : Formula) : Model formula :=
  let image := AtomImage.generate (table formula)
  let relation := constraints formula image
  ⟨image,AffineClauseProduct.generate (width formula) relation⟩

def read (formula : Formula) (model : Model formula) (input : Nat → Bool) : Bool :=
  AffineClauseProduct.read model.tree (Gates.coordinate (table formula) input)

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (input : Nat → Bool) :
    read formula (generate formula) input = formulaRead formula input := by
  have realized : holds (AtomImage.generate (table formula)).kernel (Gates.coordinate (table formula) input) = true :=
    (AtomImage.image_iff_kernel _ _).mp ⟨input,fun _ => rfl⟩
  rw [read,generate,AffineClauseProduct.generate_read _ _ (constraints_within n formula inside),constraints_read,
    realized,Bool.and_true,atomFormula_read]

def possible (formula : Formula) (model : Model formula) : Bool := AffineClauseProduct.possible model.tree

theorem generate_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    possible formula (generate formula) = true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [possible,generate,AffineClauseProduct.generate_possible _ _ (constraints_within n formula inside)]
  constructor
  · rintro ⟨target,accepted⟩
    rw [constraints_read] at accepted
    have pair : CNFFormula.eval (atomFormula formula) target = true ∧
        holds (AtomImage.generate (table formula)).kernel target = true := by simpa using accepted
    let point := AtomImage.decode (table formula) target
    have realized := AtomImage.decode_realizes (table formula) target pair.2
    refine ⟨point,?_⟩
    rw [← atomFormula_read]
    have same : CNFFormula.eval (atomFormula formula) (Gates.coordinate (table formula) point) =
        CNFFormula.eval (atomFormula formula) target := by
      apply Factor.formula_eval_agree
      intro clause _ literal _
      exact realized ⟨literal.var.val,by simpa only [table_size] using literal.var.isLt⟩
    exact same.trans pair.1
  · rintro ⟨input,accepted⟩
    refine ⟨Gates.coordinate (table formula) input,?_⟩
    rw [constraints_read,atomFormula_read,accepted]
    have allowed := (AtomImage.image_iff_kernel (table formula) _).mp ⟨input,fun _ => rfl⟩
    rw [allowed]
    rfl

theorem fibre_triangular (source : Array Row) (target : Nat → Bool) :
    Triangular ((AtomImage.generate source).rows target) :=
  AtomImage.rows_triangular _ target (AtomImage.run_triangular (AtomImage.tagged source))

theorem fibre_within (n : Nat) (source : Array Row) (inside : AtomImage.SourceWithin n source) (target : Nat → Bool) :
    RowsWithin n ((AtomImage.generate source).rows target) := by
  intro row member
  obtain ⟨tag,present,rfl⟩ := List.mem_map.mp member
  exact ((AtomImage.generate_valid n source inside).1 tag present).1.2

theorem fibre_realizes (source : Array Row) (input target : Nat → Bool) :
    holds ((AtomImage.generate source).rows target) input = true ∧ holds (AtomImage.generate source).kernel target = true ↔
      AtomImage.Realizes source input target := by
  rw [← AtomImage.tagged_holds,← AtomImage.run_holds]
  change _ ↔ (holds ((AtomImage.generate source).rows target) input && holds (AtomImage.generate source).kernel target) = true
  simp only [Bool.and_eq_true]

def Parameters (n : Nat) (formula : Formula) (model : Model formula) :=
  (parameter : AffineClauseProduct.Parameters model.tree) ×
    Assignment (freeIndices n (model.image.rows (extendAssignment (AffineClauseProduct.lift model.tree parameter)))).length

def lift (n : Nat) (formula : Formula) (model : Model formula) (parameter : Parameters n formula model) : Assignment n :=
  let target := AffineClauseProduct.lift model.tree parameter.1
  parameterLift n (model.image.rows (extendAssignment target)) parameter.2

theorem generate_image (n : Nat) (formula : Formula) (inside : Within n formula) (assignment : Assignment n) :
    (∃ parameter : Parameters n formula (generate formula), lift n formula (generate formula) parameter = assignment) ↔
      formulaRead formula (extendAssignment assignment) = true := by
  let source := table formula
  let relation := constraints formula (AtomImage.generate source)
  have bounded := constraints_within n formula inside
  have sourceBound := source_within n formula inside
  constructor
  · rintro ⟨⟨parameter,fibre⟩,rfl⟩
    let target := AffineClauseProduct.lift (generate formula).tree parameter
    have accepted : formulaRead relation (extendAssignment target) = true :=
      (AffineClauseProduct.generate_image _ relation bounded target).mp ⟨parameter,rfl⟩
    rw [constraints_read] at accepted
    have pair : CNFFormula.eval (atomFormula formula) (extendAssignment target) = true ∧
        holds (AtomImage.generate source).kernel (extendAssignment target) = true := by simpa using accepted
    let original := parameterLift n ((AtomImage.generate source).rows (extendAssignment target)) fibre
    have originalInFibre := parameterLift_holds n _ (fibre_triangular source _) (fibre_within n source sourceBound _) fibre
    have realized := (fibre_realizes source (extendAssignment original) (extendAssignment target)).mp ⟨originalInFibre,pair.2⟩
    change formulaRead formula (extendAssignment original) = true
    rw [← atomFormula_read]
    have same : CNFFormula.eval (atomFormula formula) (Gates.coordinate source (extendAssignment original)) =
        CNFFormula.eval (atomFormula formula) (extendAssignment target) := by
      apply Factor.formula_eval_agree
      intro clause _ literal _
      exact realized ⟨literal.var.val,by simpa only [source,table_size] using literal.var.isLt⟩
    exact same.trans pair.1
  · intro accepted
    let target : Assignment (width formula) := fun i => Gates.coordinate source (extendAssignment assignment) i.val
    have realizes : AtomImage.Realizes source (extendAssignment assignment) (extendAssignment target) := by
      intro i
      have bound : i.val < width formula := by simpa only [source,table_size] using i.isLt
      simp [extendAssignment,bound,target]
    have originalInFibre := (fibre_realizes source _ _).mpr realizes
    have originalAccepted : CNFFormula.eval (atomFormula formula) (extendAssignment target) = true := by
      have same := formula_eval_restrict (atomFormula formula) (Gates.coordinate source (extendAssignment assignment))
      exact same.trans ((atomFormula_read formula (extendAssignment assignment)).trans accepted)
    have relationAccepted : formulaRead relation (extendAssignment target) = true := by
      rw [constraints_read,originalAccepted,originalInFibre.2]
      rfl
    obtain ⟨parameter,same⟩ := (AffineClauseProduct.generate_image _ relation bounded target).mpr relationAccepted
    let target' := AffineClauseProduct.lift (AffineClauseProduct.generate (width formula) relation) parameter
    have fibreAccepted : holds ((AtomImage.generate source).rows (extendAssignment target')) (extendAssignment assignment) = true := by
      simpa only [target',same] using originalInFibre.1
    refine ⟨⟨parameter,projectFree n ((AtomImage.generate source).rows (extendAssignment target')) assignment⟩,?_⟩
    exact parameterLift_projectFree n _ (fibre_triangular source _) assignment fibreAccepted

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauseImage
