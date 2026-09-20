import H0mework.Physics.SpinPair.ColorDoublet

/-! One epsilon spin/color embedding and its independent linear dual.
The upper and lower amplitudes stay explicit for source temporal phases. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRestriction
open SU7ExteriorMatterRepresentation SU7MotherLieAlgebra

noncomputable section

def sourceColorDiracDual (coefficients : DiracSpinorIndex → Fin 2 → ℂ) :
    Module.Dual ℂ DiracExteriorMatterCarrier where
  toFun matter := ∑ spin, ∑ state,
    coefficients spin state * sourceColorDoubletDual state (matter spin)
  map_add' := by
    intros first second
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intros coefficient matter
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro spin _
    apply Finset.sum_congr rfl
    intro state _
    ring

def spinPairCoefficients (upper lower : ℂ) : DiracSpinorIndex → Fin 2 → ℂ :=
  !![0, upper; -upper, 0; 0, lower; -lower, 0]

def spinPairMatter (upper lower : ℂ) : DiracExteriorMatterCarrier :=
  sourceColorDiracMatter (spinPairCoefficients upper lower)

def spinPairDual (upper lower : ℂ) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  sourceColorDiracDual (spinPairCoefficients upper lower)

theorem sourceColorDoubletDual_basis (row column : Fin 2) :
    sourceColorDoubletDual row (sourceColorDoubletMatter column) =
      if row = column then 1 else 0 := by
  fin_cases row <;> fin_cases column <;>
    simp +decide [sourceColorDoubletDual, sourceColorDoubletMatter, sourceColorDoubletIndex, Fin.castLE]

theorem sourceColorDoubletDual_diracMatter
    (coefficients : DiracSpinorIndex → Fin 2 → ℂ) (spin : DiracSpinorIndex) (state : Fin 2) :
    sourceColorDoubletDual state (sourceColorDiracMatter coefficients spin) = coefficients spin state := by
  unfold sourceColorDiracMatter
  simp only [map_sum, map_smul, sourceColorDoubletDual_basis, smul_eq_mul]
  simp

theorem sourceColorDoubletDual_diracMatrix
    (matrix : DiracMatrix) (coefficients : DiracSpinorIndex → Fin 2 → ℂ)
    (spin : DiracSpinorIndex) (state : Fin 2) :
    sourceColorDoubletDual state
      (diracMatrixMatterAction matrix (sourceColorDiracMatter coefficients) spin) =
      ∑ other : DiracSpinorIndex, matrix spin other * coefficients other state := by
  simp [diracMatrixMatterAction, map_sum, map_smul, sourceColorDoubletDual_diracMatter]

theorem spinPairDual_diracMatrix
    (matrix : DiracMatrix) (p q u v : ℂ) :
    spinPairDual p q (diracMatrixMatterAction matrix (spinPairMatter u v)) =
      p*u*(matrix 0 0 + matrix 1 1) + p*v*(matrix 0 2 + matrix 1 3) +
        q*u*(matrix 2 0 + matrix 3 1) + q*v*(matrix 2 2 + matrix 3 3) := by
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state *
    sourceColorDoubletDual state
      (diracMatrixMatterAction matrix (sourceColorDiracMatter (spinPairCoefficients u v)) spin)) = _
  simp only [sourceColorDoubletDual_diracMatrix]
  simp [spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

def sourceColorMatterCoordinateLinear :
    (DiracSpinorIndex → Fin 2 → ℂ) →ₗ[ℂ] MatterCoordinateCarrier where
  toFun coefficients := matterCoordinateEquiv (sourceColorDiracMatter coefficients)
  map_add' := by
    intros first second
    rw [← map_add]
    congr 1
    funext spin
    simp [sourceColorDiracMatter, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intros coefficient values
    rw [← map_smul]
    congr 1
    funext spin
    simp [sourceColorDiracMatter, smul_smul]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
