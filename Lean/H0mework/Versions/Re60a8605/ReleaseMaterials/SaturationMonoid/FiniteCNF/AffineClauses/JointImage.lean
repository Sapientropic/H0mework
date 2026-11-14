import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Image
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Joint

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineJointImage
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Formula formulaRead Within)
open AffineClauseImage (width table table_size atomFormula atomFormula_read source_within constraints constraints_read constraints_within
  fibre_triangular fibre_within fibre_realizes)

structure Model (formula : Formula) where
  image : AtomImage.State
  pieces : AffineClauses.Joint.Pieces

def generate (formula : Formula) : Model formula :=
  let image := AtomImage.generate (table formula)
  let relation := constraints formula image
  ⟨image,AffineClauses.Joint.emit (width formula) relation⟩

def read (formula : Formula) (model : Model formula) (input : Nat → Bool) : Bool :=
  AffineClauses.Joint.piecesRead model.pieces (Gates.coordinate (table formula) input)

theorem generate_read (n : Nat) (formula : Formula) (inside : Within n formula) (input : Nat → Bool) :
    read formula (generate formula) input = formulaRead formula input := by
  have realized : holds (AtomImage.generate (table formula)).kernel (Gates.coordinate (table formula) input) = true :=
    (AtomImage.image_iff_kernel _ _).mp ⟨input,fun _ => rfl⟩
  rw [read,generate,AffineClauses.Joint.emit_read _ _ (constraints_within n formula inside),constraints_read,
    realized,Bool.and_true,atomFormula_read]

def possible (formula : Formula) (model : Model formula) : Bool := AffineClauses.Joint.possible model.pieces

theorem generate_possible (n : Nat) (formula : Formula) (inside : Within n formula) :
    possible formula (generate formula) = true ↔ AffineClauseProduct.Satisfiable formula := by
  rw [possible,generate,AffineClauses.Joint.emit_possible _ _ (constraints_within n formula inside)]
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

def Parameters (n : Nat) (formula : Formula) (model : Model formula) :=
  (parameter : AffineClauses.Joint.Parameters (width formula) model.pieces) ×
    Assignment (freeIndices n (model.image.rows (extendAssignment (AffineClauses.Joint.lift (width formula) model.pieces parameter)))).length

def lift (n : Nat) (formula : Formula) (model : Model formula) (parameter : Parameters n formula model) : Assignment n :=
  let target := AffineClauses.Joint.lift (width formula) model.pieces parameter.1
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
    let target := AffineClauses.Joint.lift (width formula) (generate formula).pieces parameter
    have accepted : formulaRead relation (extendAssignment target) = true :=
      (AffineClauses.Joint.emit_image _ relation bounded target).mp ⟨parameter,rfl⟩
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
    obtain ⟨parameter,same⟩ := (AffineClauses.Joint.emit_image _ relation bounded target).mpr relationAccepted
    let target' := AffineClauses.Joint.lift (width formula) (AffineClauses.Joint.emit (width formula) relation) parameter
    have fibreAccepted : holds ((AtomImage.generate source).rows (extendAssignment target')) (extendAssignment assignment) = true := by
      simpa only [target',same] using originalInFibre.1
    refine ⟨⟨parameter,projectFree n ((AtomImage.generate source).rows (extendAssignment target')) assignment⟩,?_⟩
    exact parameterLift_projectFree n _ (fibre_triangular source _) assignment fibreAccepted

end SaturationMonoid.ComplexityProjection.SATSource.AffineJointImage
