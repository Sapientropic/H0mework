import H0mework.Physics.SourceGauge.Material
import H0mework.Physics.Matter.ChargedGaugeCurrentThreeForm

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Gauge

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField StageNineConnectionSectorSourceBalance
open StageNineMatterVariation StageNineCoframeLocalDifferentiability StageNineMatterCovariantDerivativeAffine
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineTopologicalP286GaugeThreeFormDuality StageNineTopologicalLorentzThreeFormDuality
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem spin_current_time (step : ℕ) (point : BasePoint) (data : P286LieBlockData) :
    spinPairCurrentComplex 0 data (upperDual step point) (lowerDual step point)
      (upper step point) (lower step point) = 0 := by
  apply spinPairCurrentComplex_temporal_zero
  rw [upperDual_lower, lowerDual_upper]

theorem spin_current_spatial (step : ℕ) (point : BasePoint) (direction : Fin 3) (data : P286LieBlockData) :
    (spinPairCurrentComplex direction.succ data (upperDual step point) (lowerDual step point)
      (upper step point) (lower step point)).re =
      4 * spinScale * p286LiePairing (sourceColorP286Generator direction) data := by
  have product : upperDual step point * lower step point + lowerDual step point * upper step point =
      ((2 * spinScale : ℝ) : ℂ) := by
    rw [upperDual_lower, lowerDual_upper]
    push_cast
    ring
  rw [spinPairCurrentComplex_spatial_pairing direction data _ _ _ _ (2 * spinScale) product]
  ring

private theorem inverseGamma_current (step : ℕ) (point : BasePoint)
    (direction : LorentzianIndex) (data : P286LieBlockData) :
    (fieldAt step).conjugateMatter point
      (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma { coframe := (fieldAt step).coframe point, derivative := 0 } direction)
        (diracExteriorMotherLieAction (p286LieBlockEmbed data) ((fieldAt step).matter point))) =
      (if direction = 0 then (((clock step)⁻¹ : ℝ) : ℂ) else 1) *
        spinPairCurrentComplex direction data (upperDual step point) (lowerDual step point)
          (upper step point) (lower step point) := by
  rw [field_coframe, field_matter, field_dual,
    homogeneousInverseGamma (clock step) (ne_of_gt (clock_pos step)),
    coframeDiracMatrixMatterAction_smul_matrix, smul_comm, map_smul]
  rfl

theorem matter_current (step : ℕ) (point : BasePoint) (variation : P286GaugeOneForm) :
    p286MatterCurrentCoefficient (sourceAt step) (fieldAt step) variation point =
      4 * clock step * spinScale * ∑ index : Fin 3,
        p286LiePairing (sourceColorP286Generator index)
          (p286CoordinateEquiv.symm (variation index.succ)) := by
  have derivative (direction : LorentzianIndex) :
      holonomicMatterGaugeConnectionVariation (fieldAt step) (fun _ => variation) point direction =
        diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
          ((fieldAt step).matter point) := rfl
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_chartZero, matterDerivativeFrameRelative_zeroChart, derivative]
  change |((fieldAt step).coframe point).det| * ((fieldAt step).conjugateMatter point
    (Complex.I • ∑ direction, diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := (fieldAt step).coframe point, derivative := 0 } direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
        ((fieldAt step).matter point)))).re = _
  rw [Finset.smul_sum, map_sum, Complex.re_sum]
  simp_rw [inverseGamma_current]
  rw [field_coframe, homogeneousCoframe_det, abs_of_pos (clock_pos step)]
  simp only [Fin.sum_univ_four, ite_true, spin_current_time, mul_zero, Complex.zero_re, zero_add]
  simp only [show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, if_false, one_mul]
  have first := spin_current_spatial step point 0 (p286CoordinateEquiv.symm (variation 1))
  have second := spin_current_spatial step point 1 (p286CoordinateEquiv.symm (variation 2))
  have third := spin_current_spatial step point 2 (p286CoordinateEquiv.symm (variation 3))
  rw [show (0 : Fin 3).succ = (1 : Fin 4) by decide] at first
  rw [show (1 : Fin 3).succ = (2 : Fin 4) by decide] at second
  rw [show (2 : Fin 3).succ = (3 : Fin 4) by decide] at third
  rw [first, second, third]
  simp [Fin.sum_univ_three]
  ring

theorem charged_coefficient (step : ℕ) (point : BasePoint) (variation : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient (sourceAt step) 0 point
      (toContinuumPointField (fieldAt step) point) variation =
      4 * clock step * spinScale * ∑ index : Fin 3,
        p286LiePairing (sourceColorP286Generator index)
          (p286CoordinateEquiv.symm (variation index.succ)) := by
  unfold formNativeChargedGaugeFirstCoefficient
  rw [scalar_gauge_coefficient_zero, zero_add]
  exact matter_current step point variation

def charged (step : ℕ) : P286GaugeThreeForm :=
  ![(-4 * clock step * spinScale) • p286CoordinateEquiv (sourceColorP286Generator 2),
    (4 * clock step * spinScale) • p286CoordinateEquiv (sourceColorP286Generator 1),
    (-4 * clock step * spinScale) • p286CoordinateEquiv (sourceColorP286Generator 0), 0]

private theorem charged_represents (step : ℕ) (variation : P286GaugeOneForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient variation (charged step) =
      4 * clock step * spinScale * ∑ index : Fin 3,
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
        ((-4 * clock step * spinScale) • p286CoordinateEquiv (sourceColorP286Generator 0)) +
      1 * p286CoordinateLiePairing (variation 2)
        ((4 * clock step * spinScale) • p286CoordinateEquiv (sourceColorP286Generator 1)) +
      (-1) * p286CoordinateLiePairing (variation 3)
        ((-4 * clock step * spinScale) • p286CoordinateEquiv (sourceColorP286Generator 2)) = _
  simp only [p286CoordinateLiePairing_smul_right, pairing]
  have zero (coordinate : P286CoordinateCarrier) : p286CoordinateLiePairing coordinate 0 = 0 := by
    simp [p286CoordinateLiePairing, p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]
  simp only [zero, Fin.sum_univ_three]
  rw [show (0 : Fin 3).succ = (1 : Fin 4) by decide,
    show (1 : Fin 3).succ = (2 : Fin 4) by decide,
    show (2 : Fin 3).succ = (3 : Fin 4) by decide]
  ring

theorem charged_three_form (step : ℕ) (point : BasePoint) :
    formNativeChargedGaugeThreeForm (sourceAt step) 0 point
      (toContinuumPointField (fieldAt step) point) = charged step :=
  (formNativeChargedGaugeThreeForm_unique (sourceAt step) 0 point
    (toContinuumPointField (fieldAt step) point) (charged step)
    (fun variation => (charged_represents step variation).trans
      (charged_coefficient step point variation).symm)).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamily.Gauge
