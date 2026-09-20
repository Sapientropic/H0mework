import H0mework.Physics.SpinPair.ColorAction

/-! Full P286 current of the source epsilon pair. The color, weak and center
components are evaluated together, before selecting the spatial triad. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField
open SU7ExteriorMatterRepresentation SU7ExteriorMatterGaugeCovariantJet SU7MotherLieAlgebra

noncomputable section

theorem sourceColorDoubletDual_motherAction
    (data : P286LieBlockData) (coefficients : DiracSpinorIndex → Fin 2 → ℂ)
    (spin : DiracSpinorIndex) (state : Fin 2) :
    sourceColorDoubletDual state
      (diracExteriorMotherLieAction (p286LieBlockEmbed data) (sourceColorDiracMatter coefficients) spin) =
      ∑ other : Fin 2, coefficients spin other *
        ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) (state.castLE (by decide)) (other.castLE (by decide)) +
          if state = other then data.2.2.1 else 0) := by
  change sourceColorDoubletDual state
    (exteriorSpinorMotherLieAction (p286LieBlockEmbed data)
      (∑ other : Fin 2, coefficients spin other • sourceColorDoubletMatter other)) = _
  simp only [map_sum, map_smul, sourceColorDoublet_p286ActionCoefficient, smul_eq_mul]

theorem sourceColorDoubletDual_matrixMotherAction
    (matrix : DiracMatrix) (data : P286LieBlockData)
    (coefficients : DiracSpinorIndex → Fin 2 → ℂ)
    (spin : DiracSpinorIndex) (state : Fin 2) :
    sourceColorDoubletDual state
      (diracMatrixMatterAction matrix
        (diracExteriorMotherLieAction (p286LieBlockEmbed data) (sourceColorDiracMatter coefficients)) spin) =
      ∑ otherSpin : DiracSpinorIndex, matrix spin otherSpin *
        ∑ other : Fin 2, coefficients otherSpin other *
          ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) (state.castLE (by decide)) (other.castLE (by decide)) +
            if state = other then data.2.2.1 else 0) := by
  simp [diracMatrixMatterAction, map_sum, map_smul, sourceColorDoubletDual_motherAction]

def spinPairCurrentComplex (direction : LorentzianIndex)
    (data : P286LieBlockData) (p q u v : ℂ) : ℂ :=
  spinPairDual p q
    (Complex.I • diracMatrixMatterAction (diracGamma direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed data) (spinPairMatter u v)))

theorem spinPairCurrentComplex_full
    (direction : LorentzianIndex) (data : P286LieBlockData) (p q u v : ℂ) :
    spinPairCurrentComplex direction data p q u v =
      (![Complex.I*(p*v-q*u)*((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 +
            (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 1 + 2*data.2.2.1),
         -Complex.I*(p*v+q*u)*((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 1 +
            (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 0),
         (p*v+q*u)*((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 1 -
            (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 0),
         -Complex.I*(p*v+q*u)*((data.1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0 -
            (data.1 : Matrix (Fin 3) (Fin 3) ℂ) 1 1)] : LorentzianIndex → ℂ) direction := by
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state * sourceColorDoubletDual state
    ((Complex.I • diracMatrixMatterAction (diracGamma direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed data)
        (sourceColorDiracMatter (spinPairCoefficients u v)))) spin)) = _
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, sourceColorDoubletDual_matrixMotherAction]
  fin_cases direction <;>
    simp [spinPairCoefficients, diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Fin.sum_univ_four, Fin.sum_univ_two, Fin.castLE] <;> ring_nf
  all_goals
    simp [Complex.I_sq]
    ring

theorem spinPairCurrentComplex_temporal_zero
    (data : P286LieBlockData) (p q u v : ℂ) (balanced : p*v = q*u) :
    spinPairCurrentComplex 0 data p q u v = 0 := by
  rw [spinPairCurrentComplex_full]
  simp [balanced]

theorem spinPairCurrentComplex_spatialGenerator
    (direction generator : Fin 3) (p q u v : ℂ) :
    spinPairCurrentComplex direction.succ (sourceColorP286Generator generator) p q u v =
      if direction = generator then p*v+q*u else 0 := by
  rw [spinPairCurrentComplex_full]
  fin_cases direction <;> fin_cases generator <;>
    norm_num [sourceColorP286Generator, SU7MotherGaugeTheory.p286LieBracket,
      SU7MotherGaugeTheory.suLieBracket, SU7MotherGaugeTheory.colorCartanGenerator,
      SU7MotherGaugeTheory.colorCartanRaw, SU7MotherGaugeTheory.colorMixingGenerator,
      SU7MotherGaugeTheory.colorMixingRaw, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
