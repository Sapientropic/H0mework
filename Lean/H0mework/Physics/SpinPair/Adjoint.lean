import H0mework.Physics.SpinPair.Dirac
import H0mework.Physics.Dirac.FullDiracAdjointLocalOperator

/-! The independent linear source dual inherits the full-carrier mother
action and generates its exact spin/gauge and phase kinetic coefficients. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource Stage9C.Dynamics.Homogeneous
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability StageNineLorentzConnectionVariation
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineFullDiracAdjointLocalOperator StageNineFullDiracAdjointMaterial
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7MotherLieAlgebra
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction

noncomputable section

private theorem fullInternalPair_doublet
    (state : Fin 2) (matter : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (sourceColorDoubletMatter state) matter = sourceColorDoubletDual state matter := by
  simp [fullInternalPair, exteriorCoordinatePair, sourceColorDoubletMatter,
    sourceColorDoubletDual, Finsupp.single_apply, apply_ite]

private theorem fullInternalPair_doubletLinear
    (coefficients : Fin 2 → ℂ) (matter : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (∑ state, coefficients state • sourceColorDoubletMatter state) matter =
      ∑ state, star (coefficients state) * sourceColorDoubletDual state matter := by
  simp [Fin.sum_univ_two, fullInternalPair, exteriorCoordinatePair, sourceColorDoubletMatter,
    sourceColorDoubletDual, Finset.sum_add_distrib, add_mul]
  congr 1
  · rw [Finset.sum_eq_single (sourceColorDoubletIndex 0)]
    · simp
    · intro index _ different
      simp [Ne.symm different]
    · simp
  · rw [Finset.sum_eq_single (sourceColorDoubletIndex 1)]
    · simp
    · intro index _ different
      simp [Ne.symm different]
    · simp

/-- The complete internal pairing on the original two-color source carrier. -/
theorem fullInternalPair_colorLinear
    (coefficients : Fin 2 → ℂ) (matter : SU7ExteriorSpinorMatterCarrier) :
    fullInternalPair (∑ state, coefficients state • sourceColorDoubletMatter state) matter =
      ∑ state, star (coefficients state) * sourceColorDoubletDual state matter :=
  fullInternalPair_doubletLinear coefficients matter

theorem sourceColorDoubletDual_generator
    (direction : Fin 3) (state : Fin 2) (matter : SU7ExteriorSpinorMatterCarrier) :
    sourceColorDoubletDual state
      (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction)) matter) =
      ∑ other : Fin 2, sourceColorPauli direction state other * sourceColorDoubletDual other matter := by
  have skew := fullInternalPair_motherLie_skew
    (p286LieBlockEmbed (sourceColorP286Generator direction)) (sourceColorDoubletMatter state) matter
  rw [sourceColorDoublet_generatorAction, fullInternalPair_doubletLinear, fullInternalPair_doublet] at skew
  fin_cases direction <;> fin_cases state <;>
    simp [sourceColorPauli, Fin.sum_univ_two, map_ofNat] at skew ⊢ <;> linear_combination skew

private theorem sourceColorDoubletDual_matrix
    (matrix : DiracMatrix) (matter : DiracExteriorMatterCarrier)
    (spin : DiracSpinorIndex) (state : Fin 2) :
    sourceColorDoubletDual state (diracMatrixMatterAction matrix matter spin) =
      ∑ other : DiracSpinorIndex, matrix spin other * sourceColorDoubletDual state (matter other) := by
  simp [diracMatrixMatterAction, map_sum, map_smul]

theorem spinPairDual_rotationKinetic
    (direction : Fin 3) (p q : ℂ) (matter : DiracExteriorMatterCarrier) :
    spinPairDual p q
      (diracMatrixMatterAction (diracGamma direction.succ)
        (diracMatrixMatterAction (spinRotation direction) matter)) =
      Complex.I * spinPairDual q p matter := by
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state *
    sourceColorDoubletDual state
      (diracMatrixMatterAction (diracGamma direction.succ)
        (diracMatrixMatterAction (spinRotation direction) matter) spin)) = _
  simp only [sourceColorDoubletDual_matrix]
  fin_cases direction <;>
    simp [spinRotation, spinPairDual, sourceColorDiracDual, spinPairCoefficients,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

theorem spinPairDual_generatorKinetic
    (direction : Fin 3) (p q : ℂ) (matter : DiracExteriorMatterCarrier) :
    spinPairDual p q
      (diracMatrixMatterAction (diracGamma direction.succ)
        (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction)) matter)) =
      (-Complex.I / 2) * spinPairDual q p matter := by
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state *
    sourceColorDoubletDual state
      (diracMatrixMatterAction (diracGamma direction.succ)
        (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction)) matter) spin)) = _
  simp only [sourceColorDoubletDual_matrix]
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state *
    ∑ otherSpin, diracGamma direction.succ spin otherSpin * sourceColorDoubletDual state
      (exteriorSpinorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
        (matter otherSpin))) = _
  simp only [sourceColorDoubletDual_generator]
  fin_cases direction <;>
    simp [spinPairDual, sourceColorDiracDual, spinPairCoefficients, sourceColorPauli,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four, Fin.sum_univ_two] <;> ring_nf

theorem spinPairDual_spatialKinetic
    (spin amplitude : ℝ) (direction : Fin 3) (p q : ℂ) (matter : DiracExteriorMatterCarrier) :
    spinPairDual p q
      (Complex.I • diracMatrixMatterAction (diracGamma direction.succ)
        (diracMatrixMatterAction (diracSpinConnectionLift (homogeneousConnection spin) direction.succ)
            matter +
          diracExteriorMotherLieAction (p286LieBlockEmbed (amplitude • sourceColorP286Generator direction))
            matter)) =
      (-((spin-amplitude : ℝ) : ℂ) / 2) * spinPairDual q p matter := by
  rw [homogeneousSpinLift, coframeDiracMatrixMatterAction_smul_matrix,
    p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul, LinearMap.smul_apply]
  simp only [map_add, map_smul, smul_eq_mul, spinPairDual_rotationKinetic,
    spinPairDual_generatorKinetic]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

theorem spinPairDual_temporalKinetic
    (frequency p q : ℂ) (matter : DiracExteriorMatterCarrier) :
    spinPairDual (Complex.I*frequency*p) (-Complex.I*frequency*q)
      (Complex.I • diracMatrixMatterAction (diracGamma 0) matter) =
      -frequency * spinPairDual q p matter := by
  rw [map_smul]
  change Complex.I * (∑ spin, ∑ state,
    spinPairCoefficients (Complex.I*frequency*p) (-Complex.I*frequency*q) spin state *
      sourceColorDoubletDual state (diracMatrixMatterAction (diracGamma 0) matter spin)) = _
  simp only [sourceColorDoubletDual_matrix]
  simp [spinPairDual, sourceColorDiracDual, spinPairCoefficients, diracGamma, diracGammaZero,
    Fin.sum_univ_four, Fin.sum_univ_two]
  ring_nf
  simp [Complex.I_sq]
  ring

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
