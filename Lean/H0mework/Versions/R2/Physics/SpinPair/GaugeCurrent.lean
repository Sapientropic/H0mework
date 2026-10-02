import H0mework.Versions.R2.Physics.SpinPair.GaugeField
import H0mework.Versions.R2.Physics.SpinPair.DiracActual
import H0mework.Physics.Matter.ChargedGaugeCurrentThreeForm

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineConnectionSectorSourceBalance
open StageNineMatterVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineCoframeLocalDifferentiability StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeAuxiliaryVariation
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineTopologicalP286GaugeThreeFormDuality StageNineTopologicalLorentzThreeFormDuality
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterGaugeCovariantJet
open Stage9C.Dynamics.Homogeneous

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

theorem actual_spinPairCurrent_time (point : BasePoint) (data : P286LieBlockData) :
    spinPairCurrentComplex 0 data (upperDualPhase point) (lowerDualPhase point)
      (upperPhase point) (lowerPhase point) = 0 := by
  apply spinPairCurrentComplex_temporal_zero
  rw [upperDual_lower_product, lowerDual_upper_product]

theorem actual_spinPairCurrent_spatial
    (point : BasePoint) (direction : Fin 3) (data : P286LieBlockData) :
    (spinPairCurrentComplex direction.succ data (upperDualPhase point) (lowerDualPhase point)
      (upperPhase point) (lowerPhase point)).re =
      4 * spinScale * p286LiePairing (sourceColorP286Generator direction) data := by
  have product : upperDualPhase point * lowerPhase point + lowerDualPhase point * upperPhase point =
      ((2 * spinScale : ℝ) : ℂ) := by
    rw [upperDual_lower_product, lowerDual_upper_product]
    push_cast
    ring
  rw [spinPairCurrentComplex_spatial_pairing direction data _ _ _ _ (2*spinScale) product]
  ring

private theorem inverseGamma_current
    (point : BasePoint) (direction : LorentzianIndex) (data : P286LieBlockData) :
    actual.conjugateMatter point
      (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } direction)
        (diracExteriorMotherLieAction (p286LieBlockEmbed data) (actual.matter point))) =
      (if direction = 0 then ((lapse⁻¹ : ℝ) : ℂ) else 1) *
        spinPairCurrentComplex direction data (upperDualPhase point) (lowerDualPhase point)
          (upperPhase point) (lowerPhase point) := by
  rw [actual_coframe, actual_matter, actual_conjugateMatter,
    homogeneousInverseGamma lapse (ne_of_gt lapse_pos), coframeDiracMatrixMatterAction_smul_matrix,
    smul_comm, map_smul]
  rfl

theorem actual_p286MatterCurrent (point : BasePoint) (variation : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual variation point =
      4*lapse*spinScale * ∑ index : Fin 3,
        p286LiePairing (sourceColorP286Generator index)
          (p286CoordinateEquiv.symm (variation index.succ)) := by
  have derivative (direction : LorentzianIndex) :
      holonomicMatterGaugeConnectionVariation actual (fun _ => variation) point direction =
        diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
          (actual.matter point) := rfl
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart, derivative]
  change |(actual.coframe point).det| * (actual.conjugateMatter point
    (Complex.I • ∑ direction, diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := actual.coframe point, derivative := 0 } direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
        (actual.matter point)))).re = _
  rw [Finset.smul_sum, map_sum, Complex.re_sum]
  simp_rw [inverseGamma_current]
  rw [actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  simp only [Fin.sum_univ_four, ite_true, actual_spinPairCurrent_time, mul_zero,
    Complex.zero_re, zero_add]
  simp only [show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, if_false, one_mul]
  have first := actual_spinPairCurrent_spatial point 0 (p286CoordinateEquiv.symm (variation 1))
  have second := actual_spinPairCurrent_spatial point 1 (p286CoordinateEquiv.symm (variation 2))
  have third := actual_spinPairCurrent_spatial point 2 (p286CoordinateEquiv.symm (variation 3))
  rw [show (0 : Fin 3).succ = (1 : Fin 4) by decide] at first
  rw [show (1 : Fin 3).succ = (2 : Fin 4) by decide] at second
  rw [show (2 : Fin 3).succ = (3 : Fin 4) by decide] at third
  rw [first, second, third]
  simp [Fin.sum_univ_three]
  ring

theorem actual_chargedCoefficient (point : BasePoint) (variation : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
      (toContinuumPointField actual point) variation =
      4*lapse*spinScale * ∑ index : Fin 3,
        p286LiePairing (sourceColorP286Generator index)
          (p286CoordinateEquiv.symm (variation index.succ)) := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [actual_scalarKineticFirstVariation_zero, zero_add]
  exact actual_p286MatterCurrent point variation

def chargedThreeForm : P286GaugeThreeForm :=
  ![(-4*lapse*spinScale) • p286CoordinateEquiv (sourceColorP286Generator 2),
    (4*lapse*spinScale) • p286CoordinateEquiv (sourceColorP286Generator 1),
    (-4*lapse*spinScale) • p286CoordinateEquiv (sourceColorP286Generator 0),0]

private theorem chargedThreeForm_represents (variation : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient variation chargedThreeForm =
      4*lapse*spinScale * ∑ index : Fin 3,
        p286LiePairing (sourceColorP286Generator index)
          (p286CoordinateEquiv.symm (variation index.succ)) := by
  have pairing (coordinate : P286CoordinateCarrier) (index : Fin 3) :
      p286CoordinateLiePairing coordinate (p286CoordinateEquiv (sourceColorP286Generator index)) =
        p286LiePairing (sourceColorP286Generator index) (p286CoordinateEquiv.symm coordinate) := by
    unfold p286CoordinateLiePairing
    rw [p286CoordinateEquiv.symm_apply_apply, p286LiePairing_symmetric]
  rw [p286GaugeOneFormThreeFormWedgeCoefficient, Fin.sum_univ_four]
  change 1 * p286CoordinateLiePairing (variation 0) 0 +
      (-1) * p286CoordinateLiePairing (variation 1)
        ((-4*lapse*spinScale) • p286CoordinateEquiv (sourceColorP286Generator 0)) +
      1 * p286CoordinateLiePairing (variation 2)
        ((4*lapse*spinScale) • p286CoordinateEquiv (sourceColorP286Generator 1)) +
      (-1) * p286CoordinateLiePairing (variation 3)
        ((-4*lapse*spinScale) • p286CoordinateEquiv (sourceColorP286Generator 2)) = _
  simp only [p286CoordinateLiePairing_smul_right, pairing]
  have zero (coordinate : P286CoordinateCarrier) : p286CoordinateLiePairing coordinate 0 = 0 := by
    simp [p286CoordinateLiePairing, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]
  simp only [zero]
  simp only [Fin.sum_univ_three]
  rw [show (0 : Fin 3).succ = (1 : Fin 4) by decide,
    show (1 : Fin 3).succ = (2 : Fin 4) by decide,
    show (2 : Fin 3).succ = (3 : Fin 4) by decide]
  ring

theorem actual_chargedThreeForm (point : BasePoint) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField actual point) = chargedThreeForm :=
  (formNativeChargedGaugeThreeForm_unique positiveSmoothUnifiedSource 0 point
    (toContinuumPointField actual point) chargedThreeForm
    (fun variation => (chargedThreeForm_represents variation).trans
      (actual_chargedCoefficient point variation).symm)).symm

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
