import H0mework.Physics.NonlinearOrbit.Scalar

/-! The complete charged three-form is recomputed on the jointly moving
configuration and agrees with the original source current. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeAuxiliaryVariation StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineConnectionSectorSourceBalance
open StageNineMatterCovariantDerivativeAffine StageNineMatterVariation
open DiracCliffordRepresentation DiracExteriorMatterAction Stage9C.Dynamics.Homogeneous
open StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability
open SU7MotherLieAlgebra SU7MotherGaugeTheory

noncomputable section

variable {initial : PhaseSpace} {initialTime : ℝ}

def phaseCurrent (angle : ℝ) (direction : LorentzianIndex) (data : P286LieBlockData) : ℂ :=
  spinPairCurrentComplex direction data ((spinScale : ℂ)*unitPhase angle)
    ((spinScale : ℂ)*unitPhase (-angle)) (unitPhase angle) (unitPhase (-angle))

theorem phaseCurrent_time (angle : ℝ) (data : P286LieBlockData) : phaseCurrent angle 0 data = 0 := by
  apply spinPairCurrentComplex_temporal_zero
  ring

theorem phaseCurrent_spatial (angle : ℝ) (direction : Fin 3) (data : P286LieBlockData) :
    (phaseCurrent angle direction.succ data).re =
      4*spinScale*p286LiePairing (sourceColorP286Generator direction) data := movingCurrent _ _ _

private theorem inverseGamma_current (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (direction : LorentzianIndex) (data : P286LieBlockData) :
    flow.configuration.conjugateMatter point (Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed data) (flow.configuration.matter point))) =
      (if direction = 0 then ((lapse⁻¹ : ℝ) : ℂ) else 1) * phaseCurrent (flow.angle (point 0)) direction data := by
  have frame : flow.configuration.coframe point = homogeneousCoframe lapse := by
    change Runtime.configuration.coframe point = _
    rw [Runtime.configuration_eq, actual_coframe]
  rw [frame, homogeneousInverseGamma lapse (ne_of_gt lapse_pos), coframeDiracMatrixMatterAction_smul_matrix,
    smul_comm, map_smul]
  rfl

theorem LocalOrbit.matterCurrent (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (variation : P286GaugeOneForm) :
    p286MatterCurrentCoefficient positiveSmoothUnifiedSource flow.configuration variation point =
      4*lapse*spinScale * ∑ axis : Fin 3,
        p286LiePairing (sourceColorP286Generator axis) (p286CoordinateEquiv.symm (variation axis.succ)) := by
  unfold p286MatterCurrentCoefficient matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]
  change |(flow.configuration.coframe point).det| * (flow.configuration.conjugateMatter point
    (Complex.I • ∑ direction, diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } direction)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (variation direction)))
        (flow.configuration.matter point)))).re = _
  rw [Finset.smul_sum, map_sum, Complex.re_sum]
  simp_rw [inverseGamma_current]
  have frame : flow.configuration.coframe point = homogeneousCoframe lapse := by
    change Runtime.configuration.coframe point = _
    rw [Runtime.configuration_eq, actual_coframe]
  rw [frame, homogeneousCoframe_det, abs_of_pos lapse_pos, Fin.sum_univ_succ]
  simp only [ite_true, phaseCurrent_time, mul_zero, Complex.zero_re, zero_add,
    Fin.succ_ne_zero, ite_false, one_mul]
  simp_rw [phaseCurrent_spatial]
  rw [← Finset.mul_sum]
  ring

theorem LocalOrbit.chargedCoefficient (flow : LocalOrbit initial initialTime) (point : BasePoint)
    (variation : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) variation =
      formNativeChargedGaugeFirstCoefficient positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Runtime.configuration point) variation := by
  rw [Runtime.configuration_eq, actual_chargedCoefficient]
  unfold formNativeChargedGaugeFirstCoefficient
  rw [flow.scalarFirst_zero, zero_add]
  exact flow.matterCurrent point variation

theorem LocalOrbit.chargedThreeForm (flow : LocalOrbit initial initialTime) (point : BasePoint) :
    formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) =
      formNativeChargedGaugeThreeForm positiveSmoothUnifiedSource 0 point
        (toContinuumPointField Runtime.configuration point) := by
  unfold formNativeChargedGaugeThreeForm
  apply congrArg p286GaugeThreeFormOfDual
  apply LinearMap.ext
  intro variation
  exact flow.chargedCoefficient point variation

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
