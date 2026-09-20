import H0mework.Physics.LowEnergyEvolution.Dirac
import H0mework.Physics.SpinPair.CoframeCalculus

/-! The full Dirac kinetic load on the generated fields supplies the original
coframe derivative. The boost and dilution terms are tested in all 16 entries. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability
open StageNineLorentzConnectionVariation StageNineLorentzConnectionVariationDensity
open StageNineMatterVariation StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineP286GaugeConnectionVariationDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCoframeLocalVariation StageNineCoframeVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open SU7ExteriorBreakingYukawa
open scoped Matrix.Norms.Elementwise
noncomputable section

def pairingDensity (x : State) : ℝ := spinScale*dilution (x 0)^2

theorem spinAmplitude_product (x : State) :
    spinAmplitude 1 x*spinAmplitude (-1) x = ((dilution (x 0)^2 : ℝ) : ℂ) := by
  simp only [spinAmplitude, Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul]
  have phase : Complex.exp (Complex.I*(x 6 : ℂ))*Complex.exp (-(Complex.I*(x 6 : ℂ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc
    _ = ((dilution (x 0)^2 : ℝ) : ℂ)*
        (Complex.exp (Complex.I*(x 6 : ℂ))*Complex.exp (-(Complex.I*(x 6 : ℂ)))) := by push_cast; ring
    _ = _ := by rw [phase, mul_one]

theorem spinAmplitude_pairing (x : State) :
    ((spinScale : ℂ)*spinAmplitude 1 x)*spinAmplitude (-1) x = (pairingDensity x : ℂ) ∧
    ((spinScale : ℂ)*spinAmplitude (-1) x)*spinAmplitude 1 x = (pairingDensity x : ℂ) := by
  constructor
  · rw [mul_assoc, spinAmplitude_product]
    simp [pairingDensity]
  · rw [mul_assoc, mul_comm (spinAmplitude (-1) x), spinAmplitude_product]
    simp [pairingDensity]

private theorem plainLoad_zero (internal : LorentzianIndex) (density : ℝ) (p q u v : ℂ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma internal) (spinPairMatter u v)) = 0 := by
  rw [map_smul, spinPairDual_diracMatrix, pv, qu]
  fin_cases internal <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree]
  all_goals ring

private theorem scaledPlainLoad_zero (internal : LorentzianIndex) (density : ℝ) (factor p q u v : ℂ)
    (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (factor • spinPairMatter u v)) = 0 := by
  have plain := plainLoad_zero internal density p q u v pv qu
  simp only [map_smul, smul_eq_mul] at plain ⊢
  linear_combination factor*plain

private theorem phaseTimeLoad (internal : LorentzianIndex) (rate p q u v : ℂ) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (spinPairMatter (Complex.I*rate*u) (-Complex.I*rate*v))) =
      if internal = 0 then 2*rate*(p*v+q*u) else 0 := by
  rw [map_smul, spinPairDual_diracMatrix]
  fin_cases internal <;>
    simp [diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree, smul_eq_mul]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]

private theorem rotationLoad (internal : LorentzianIndex) (axis : Fin 3) (coefficient p q u v : ℂ) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (coefficient • diracMatrixMatterAction (spinRotation axis) (spinPairMatter u v))) =
      if internal = axis.succ then -2*coefficient*(p*v+q*u) else 0 := by
  rw [map_smul, map_smul, map_smul]
  rw [Stage9C.Dynamics.PlaneWave.matrixAction_comp, spinPairDual_diracMatrix]
  fin_cases internal <;> fin_cases axis <;>
    simp [spinRotation, diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_four, smul_eq_mul] <;> ring_nf
  all_goals simp [Complex.I_sq]; ring

set_option maxHeartbeats 1000000 in
private theorem boostLoad_zero (internal : LorentzianIndex) (axis : Fin 3) (velocity density : ℝ)
    (p q u v : ℂ) (pv : p*v = (density : ℂ)) (qu : q*u = (density : ℂ)) :
    spinPairDual p q (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (diracMatrixMatterAction (diracSpinConnectionLift (boostConnection velocity) axis.succ)
        (spinPairMatter u v))) = 0 := by
  rw [map_smul, Stage9C.Dynamics.PlaneWave.matrixAction_comp, spinPairDual_diracMatrix, pv, qu]
  fin_cases internal <;> fin_cases axis <;>
    simp [diracSpinConnectionLift, loweredLorentzConnectionCoefficient, boostConnection,
      lorentzBivectorFirst, lorentzBivectorSecond, minkowskiInternalSign,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;> ring_nf

def Solution.kineticLoad {initial : State} (flow : Solution initial) (point : BasePoint) : LorentzianCoframe :=
  fun internal mu => (flow.configuration.conjugateMatter point
    (Complex.I • diracMatrixMatterAction (diracGamma internal)
      (holonomicMatterCovariantDerivative flow.configuration point mu))).re

theorem Solution.kineticLoad_time {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (internal : LorentzianIndex) :
    flow.kineticLoad point internal 0 =
      if internal = 0 then 4*pairingDensity (flow.pointState point)*generator (flow.pointState point) 6 else 0 := by
  unfold Solution.kineticLoad
  rw [flow.dual, flow.matter_covariant_time point inside]
  simp only [spinVelocity, Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_mul]
  rw [← sub_eq_add_neg, spinPairMatter_damped]
  simp only [map_add, smul_add]
  rw [scaledPlainLoad_zero internal (pairingDensity (flow.pointState point)) _ _ _ _ _
    (spinAmplitude_pairing (flow.pointState point)).1 (spinAmplitude_pairing (flow.pointState point)).2,
    zero_add, phaseTimeLoad,
    (spinAmplitude_pairing (flow.pointState point)).1, (spinAmplitude_pairing (flow.pointState point)).2]
  split_ifs <;> simp [Complex.mul_re]
  all_goals ring

theorem Solution.kineticLoad_spatial {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (internal : LorentzianIndex) (axis : Fin 3) :
    flow.kineticLoad point internal axis.succ =
      if internal = axis.succ then -2*pairingDensity (flow.pointState point)*
        (contorsion (flow.pointState point)-flow.pointState point 2) else 0 := by
  unfold Solution.kineticLoad
  rw [flow.dual, flow.matter_covariant_spatial point inside, flow.matter]
  simp only [map_add, smul_add]
  rw [boostLoad_zero internal axis _ (pairingDensity (flow.pointState point)) _ _ _ _
    (spinAmplitude_pairing (flow.pointState point)).1 (spinAmplitude_pairing (flow.pointState point)).2,
    zero_add, rotationLoad, (spinAmplitude_pairing (flow.pointState point)).1,
    (spinAmplitude_pairing (flow.pointState point)).2]
  split_ifs <;> simp [Complex.mul_re]
  all_goals ring

theorem Solution.kineticLoad_diagonal {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    flow.kineticLoad point = Matrix.diagonal
      ![4*pairingDensity (flow.pointState point)*generator (flow.pointState point) 6,
        -2*pairingDensity (flow.pointState point)*(contorsion (flow.pointState point)-flow.pointState point 2),
        -2*pairingDensity (flow.pointState point)*(contorsion (flow.pointState point)-flow.pointState point 2),
        -2*pairingDensity (flow.pointState point)*(contorsion (flow.pointState point)-flow.pointState point 2)] := by
  ext internal mu
  induction mu using Fin.cases with
  | zero => rw [flow.kineticLoad_time point inside]; fin_cases internal <;> simp
  | succ axis => rw [flow.kineticLoad_spatial point inside]; fin_cases internal <;> fin_cases axis <;> simp

private theorem inverseGamma_load (candidate : LorentzianCoframe) (mu : LorentzianIndex)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (derivative : DiracExteriorMatterCarrier) :
    (dual (Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := candidate, derivative := 0 } mu) derivative)).re =
      ∑ internal, candidate⁻¹ mu internal *
        (dual (Complex.I • diracMatrixMatterAction (diracGamma internal) derivative)).re := by
  unfold inverseCoframeDiracGamma
  simp only [Fin.sum_univ_four, coframeDiracMatrixMatterAction_add_matrix,
    coframeDiracMatrixMatterAction_smul_matrix, smul_add, map_add, map_smul, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]

theorem Solution.frozen_kinetic_density {initial : State} (flow : Solution initial)
    (point : BasePoint) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField flow.configuration point) candidate) =
      |candidate.det| * inverseLoad (flow.kineticLoad point) candidate := by
  unfold generatedDensitizedContinuumMatterKineticDensity generatedContinuumMatterKineticVector
    matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [withCoframe, toContinuumPointField, generatedVolumeDensity,
    matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    Finset.smul_sum, map_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  exact inverseGamma_load candidate mu _ _

theorem Solution.inverseLoad_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    inverseLoad (flow.kineticLoad point) (flow.configuration.coframe point) = 0 := by
  have density : generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField flow.configuration point) (flow.configuration.coframe point)) = 0 := by
    change generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) = 0
    unfold generatedDensitizedContinuumMatterKineticDensity
    rw [flow.kinetic_zero point inside]
    simp
  rw [flow.frozen_kinetic_density] at density
  exact (mul_eq_zero.mp density).resolve_left (abs_ne_zero.mpr (flow.nondegenerate_at point inside))

theorem Solution.kinetic_coframe_derivative {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (variation : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField flow.configuration point) (flow.configuration.coframe point+t • variation)))
      (-6*spinScale*(contorsion (flow.pointState point)-flow.pointState point 2)/(flow.pointState point 0)*variation 0 0 +
        2*clock (flow.pointState point)*spinScale*(contorsion (flow.pointState point)-flow.pointState point 2)/
          (flow.pointState point 0)^2*(variation 1 1+variation 2 2+variation 3 3)) 0 := by
  simp_rw [flow.frozen_kinetic_density]
  have derivative := volumeInverseLoad_line_hasDerivAt (flow.kineticLoad point)
    (flow.configuration.coframe point) variation (flow.nondegenerate_at point inside) (flow.inverseLoad_zero point inside)
  convert derivative using 1
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalCoframe_det, abs_of_pos
    (mul_pos (clock_positive _ admissible) (pow_pos admissible.1 3)),
    diagonalCoframe_inv _ _ (ne_of_gt (clock_positive _ admissible)) (ne_of_gt admissible.1),
    flow.kineticLoad_diagonal point inside]
  simp [diagonalCoframe, Matrix.mul_apply, Fin.sum_univ_four, pairingDensity,
    dilution_square _ admissible.1, generator]
  field_simp [ne_of_gt (clock_positive _ admissible), ne_of_gt admissible.1]
  ring

theorem Solution.frozen_yukawa_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (candidate : LorentzianCoframe) :
    StageNineDiracDualYukawaLocalSpinDensity.generatedDensitizedContinuumDiracDualYukawaDensity
      positiveSmoothUnifiedSource 0 point (withCoframe (toContinuumPointField flow.configuration point) candidate) = 0 := by
  have vector := flow.yukawa_zero point
  unfold StageNineDiracDualYukawaLocalSpinDensity.generatedContinuumDiracDualYukawaVector at vector
  unfold StageNineDiracDualYukawaLocalSpinDensity.generatedDensitizedContinuumDiracDualYukawaDensity
    StageNineDiracDualYukawaLocalSpinDensity.generatedContinuumDiracDualYukawaVector
  simp only [withCoframe]
  rw [vector]
  simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
