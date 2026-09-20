import H0mework.Physics.QuantumState.SourceCoefficients

/-! The noncommuting matrices are the restrictions of the mother's generated
color actions to the full occupied Dirac/color carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Algebra

open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair Source
open StageNineExteriorMotherLieRepresentation
open StageNineHolonomicField
open SU7ExteriorMatterGaugeCovariantJet SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation
open scoped Matrix

noncomputable section

/-- The same color generator acts on each of the four Dirac components. -/
def colorAction (direction : Fin 3) : Matrix Index Index ℂ :=
  fun row column => if row.1 = column.1 then sourceColorPauli direction row.2 column.2 else 0

theorem colorAction_mulVec (direction : Fin 3) (values : Index → ℂ) (row : Index) :
    (colorAction direction *ᵥ values) row =
      ∑ color, sourceColorPauli direction row.2 color * values (row.1, color) := by
  simp [Matrix.mulVec, dotProduct, colorAction, Fintype.sum_prod_type]

theorem colorAction_from_mother (direction : Fin 3) (row column : Index) :
    colorAction direction row column =
      if row.1 = column.1 then sourceColorDoubletDual row.2
        (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
          (sourceColorDoubletMatter column.2)) else 0 := by
  rw [sourceColorDoublet_generatorAction]
  rcases row with ⟨spin, color⟩
  fin_cases color <;> simp [colorAction, map_smul, sourceColorDoubletDual_basis]

theorem colorAction_noncommuting : colorAction 0 * colorAction 1 ≠
    colorAction 1 * colorAction 0 := by
  intro same
  have coefficient := congrArg (fun matrix : Matrix Index Index ℂ => matrix (0, 0) (0, 0)) same
  have imaginary := congrArg Complex.im coefficient
  norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_four,
    Fin.sum_univ_two, colorAction, sourceColorPauli, Complex.mul_im] at imaginary

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Algebra
