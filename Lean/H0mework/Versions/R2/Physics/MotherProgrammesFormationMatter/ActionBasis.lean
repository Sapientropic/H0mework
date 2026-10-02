import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.Completion
import H0mework.Physics.MotherSource.Contact
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions

open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7MotherLieAlgebra StageNineEnrichedProofFreeSource StandardModelConstraint

noncomputable section

abbrev InternalIndex := ExteriorBasisIndex 6 ⊕ (ExteriorBasisIndex 2 ⊕ ExteriorBasisIndex 4)
abbrev Index := Σ _ : DiracSpinorIndex, InternalIndex

def internalBasis : Module.Basis InternalIndex ℂ SU7ExteriorSpinorMatterCarrier :=
  (su7ExteriorBasis 6).prod ((su7ExteriorBasis 2).prod (su7ExteriorBasis 4))

def matterBasis : Module.Basis Index ℂ DiracExteriorMatterCarrier :=
  Pi.basis (fun _ : DiracSpinorIndex => internalBasis)

theorem dimension : Fintype.card Index = 252 := by
  rw [← Module.finrank_eq_card_basis matterBasis]
  change Module.finrank ℂ (DiracSpinorIndex → SU7ExteriorSpinorMatterCarrier) = 252
  rw [Module.finrank_pi_fintype]
  simp only [su7ExteriorSpinorMatterCarrier_finrank]
  norm_num [DiracSpinorIndex]

abbrev MatrixCoordinate := Index × Index × Fin 2
def coordinateCount : ℕ := Fintype.card MatrixCoordinate

theorem coordinate_count : coordinateCount = 127008 := by
  unfold coordinateCount MatrixCoordinate
  rw [Fintype.card_prod, Fintype.card_prod, dimension, Fintype.card_fin]

def address : MatrixCoordinate ≃ Fin coordinateCount := Fintype.equivFin MatrixCoordinate

/-- The imaginary direction and its normalization are read from the same
actual mother curvature. -/
def complexUnit : ℂ :=
  (generatedMotherCurvature Runtime.source 0 1 : Matrix SU7MotherIndex SU7MotherIndex ℂ)
    hyperPlusIndex hyperPlusIndex /
      (curvatureRate (generatedMotherCurvature Runtime.source 0 1) : ℂ)

theorem complex_unit : complexUnit = Complex.I := by
  unfold complexUnit
  rw [Runtime.source_eq, positive_generatedMotherCurvature_hyperPlus_entry,
    curvatureRate_generated, positive_continuousContactRate]
  have nonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions
