import H0mework.Physics.GaugeStanding.ScalarPairingSkew

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
noncomputable section

namespace LowEnergy.DressedColourYScalarRows

open SaturationMonoid.PhysicsCore SU7MotherLieAlgebra
open StageNineHolonomicField StageNineDynamicBreakingVacuum
open StageNineGlobalIntegratedAction
open StageNineP286GaugeConnectionVariation
open StageNineP286LinkedActiveScalarPairingSkew

theorem scalar_complex_pairing (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second = (inner ℂ first second).re := by
  simp [scalarCoordinatePairingRe, PiLp.inner_apply, mul_comm]

theorem scalar_action_complex_smul (matrix : SU7MotherLieMatrix)
    (c : ℂ) (phi : ScalarCoordinateCarrier) :
    scalarMotherLieAction matrix (c • phi) = c • scalarMotherLieAction matrix phi := by
  unfold scalarMotherLieAction
  rw [map_smul, map_smul, map_smul]

theorem scalar_action_complex_skew (matrix : SU7MotherLieMatrix)
    (first second : ScalarCoordinateCarrier) :
    inner ℂ (scalarMotherLieAction matrix first) second +
      inner ℂ first (scalarMotherLieAction matrix second) = 0 := by
  have realPart :=
    scalarCoordinatePairingRe_scalarMotherLieAction_skew matrix first second
  have imaginaryPart :=
    scalarCoordinatePairingRe_scalarMotherLieAction_skew matrix first (Complex.I • second)
  rw [scalar_complex_pairing, scalar_complex_pairing] at realPart
  rw [scalar_complex_pairing, scalar_complex_pairing, scalar_action_complex_smul,
    inner_smul_right, inner_smul_right] at imaginaryPart
  apply Complex.ext
  · simpa only [Complex.add_re, Complex.zero_re] using realPart
  · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub] at imaginaryPart
    simp only [Complex.add_im, Complex.zero_im]
    linarith

end LowEnergy.DressedColourYScalarRows
