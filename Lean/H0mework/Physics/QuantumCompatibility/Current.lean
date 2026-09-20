import H0mework.Physics.QuantumCompatibility.DualResponse
import H0mework.Physics.SpinPair.GaugeCurrent

/-! The full P286 current is evaluated on the accepted matter, independent
dual and actual connection. Source normalization retains its physical scale. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeAuxiliaryVariation StageNineP286GaugeConnectionActionVariation
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open scoped Matrix

noncomputable section

def currentAction (direction : LorentzianIndex) (data : P286LieBlockData) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • (diracMatrixMatterAction (diracGamma direction)).comp
    (diracExteriorMotherLieAction (p286LieBlockEmbed data))

def currentObservable (direction : LorentzianIndex) (data : P286LieBlockData) : Matrix8 :=
  responseMatrix (currentAction direction data)

theorem current_classical_quantum (point : BasePoint) (direction : LorentzianIndex)
    (data : P286LieBlockData) :
    spinPairCurrentComplex direction data (upperDualPhase point) (lowerDualPhase point)
      (upperPhase point) (lowerPhase point) =
      4 * (spinScale : ℂ) * vectorRead point (currentObservable direction data) :=
  actual_action_quantumResponse point (currentAction direction data)

theorem current_source_prediction (point : BasePoint) (direction generator : Fin 3) :
    vectorRead point (currentObservable direction.succ (sourceColorP286Generator generator)) =
      if direction = generator then 1 / 2 else 0 := by
  have observed := current_classical_quantum point direction.succ (sourceColorP286Generator generator)
  rw [spinPairCurrentComplex_spatialGenerator, upperDual_lower_product,
    lowerDual_upper_product] at observed
  have nonzero : (spinScale : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt spinScale_pos
  have scale : 4 * (spinScale : ℂ) ≠ 0 := mul_ne_zero (by norm_num) nonzero
  split_ifs at observed ⊢ <;> apply (mul_left_cancel₀ scale)
  · linear_combination -observed
  · simpa using observed.symm

theorem current_time_zero (point : BasePoint) (data : P286LieBlockData) :
    vectorRead point (currentObservable 0 data) = 0 := by
  have observed := current_classical_quantum point 0 data
  rw [actual_spinPairCurrent_time] at observed
  have nonzero : (spinScale : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt spinScale_pos
  exact (mul_eq_zero.mp observed.symm).resolve_left (mul_ne_zero (by norm_num) nonzero)

def currentResponse (point : BasePoint) (variation : P286GaugeOneForm) : ℝ :=
  4 * lapse * spinScale * ∑ direction : Fin 3,
    (vectorRead point (currentObservable direction.succ
      (p286CoordinateEquiv.symm (variation direction.succ)))).re

theorem current_spatial_pairing (point : BasePoint) (direction : Fin 3)
    (data : P286LieBlockData) :
    (vectorRead point (currentObservable direction.succ data)).re =
      p286LiePairing (sourceColorP286Generator direction) data := by
  have observed := congrArg Complex.re (current_classical_quantum point direction.succ data)
  rw [actual_spinPairCurrent_spatial] at observed
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at observed
  norm_num at observed
  exact ((observed.resolve_right (ne_of_gt spinScale_pos))).symm

theorem currentResponse_eq_classical (point : BasePoint) (variation : P286GaugeOneForm) :
    currentResponse point variation =
      p286MatterCurrentCoefficient positiveSmoothUnifiedSource actual variation point := by
  rw [actual_p286MatterCurrent]
  simp only [currentResponse, current_spatial_pairing]

def actualConnectionObservable (point : BasePoint) (direction : LorentzianIndex) : Matrix8 :=
  currentObservable direction (actual.gaugeConnection point direction)

theorem actual_connection_source (point : BasePoint) (direction : Fin 3) :
    actual.gaugeConnection point direction.succ = gaugeScale • sourceColorP286Generator direction := by
  rw [actual_gaugeConnection]
  fin_cases direction <;> rfl

theorem actual_connection_response (point : BasePoint) (direction : LorentzianIndex) :
    actual.conjugateMatter point
      (Complex.I • diracMatrixMatterAction (diracGamma direction)
        (diracExteriorMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point direction))
          (actual.matter point))) =
      4 * (spinScale : ℂ) * vectorRead point (actualConnectionObservable point direction) :=
  actual_action_quantumResponse point
    (currentAction direction (actual.gaugeConnection point direction))

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
