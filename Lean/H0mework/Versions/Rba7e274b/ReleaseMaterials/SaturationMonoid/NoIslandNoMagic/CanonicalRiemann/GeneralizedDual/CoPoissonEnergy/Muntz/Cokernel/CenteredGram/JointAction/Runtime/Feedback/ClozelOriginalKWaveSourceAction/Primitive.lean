import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Coefficient
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFinitePairing OriginalPaPhysicalGreen
local notation "q" => (1 / 4 : ℝ)

def actualPositionBandDensity (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (coordinate.value - 1) * positionSource coordinate x
def actualFourierBandDensity (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-coordinate.value) * burnolRieszSingleFourierSourceRaw coordinate x
def actualPositionBandPrimitive (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in (q * Real.exp (-h))..q, actualPositionBandDensity coordinate x
def actualFourierBandPrimitive (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ in (q * Real.exp (-h))..q, actualFourierBandDensity coordinate x
def actualBandCoefficientAction (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  Complex.exp ((coordinate.value - 1 / 4) * (h : ℂ)) * actualPositionBandPrimitive coordinate h +
    Complex.exp ((3 / 4 - coordinate.value) * (h : ℂ)) * actualFourierBandPrimitive coordinate h

theorem actual_original_band_action_initial (coordinate : BurnolCompletedMellinCoordinate) :
    actualPositionBandPrimitive coordinate 0 = 0 ∧ actualFourierBandPrimitive coordinate 0 = 0 ∧
    actualBandCoefficientAction coordinate 0 = 0 := by
  simp only [actualPositionBandPrimitive, actualFourierBandPrimitive, actualBandCoefficientAction,
    neg_zero, Real.exp_zero, mul_one, intervalIntegral.integral_same, mul_zero, add_zero]
  exact ⟨trivial, trivial, trivial⟩

private theorem position_density_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousAt (actualPositionBandDensity coordinate) q := by
  exact (Complex.continuousAt_ofReal_cpow_const q (coordinate.value - 1) (Or.inr (by norm_num))).mul
    (positionSource_continuousAt coordinate (by norm_num))
private theorem fourier_density_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousAt (actualFourierBandDensity coordinate) q := by
  exact (Complex.continuousAt_ofReal_cpow_const q (-coordinate.value) (Or.inr (by norm_num))).mul
    (burnolRieszSingleFourierSourceRaw_continuousAt coordinate (by norm_num))

theorem actual_original_band_primitive_action (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (actualPositionBandPrimitive coordinate)
      ((q : ℂ) * actualPositionBandDensity coordinate q) 0 ∧
    HasDerivAt (actualFourierBandPrimitive coordinate)
      ((q : ℂ) * actualFourierBandDensity coordinate q) 0 := by
  have lower : HasDerivAt (fun h : ℝ => q * Real.exp (-h)) (-q) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).neg.exp).const_mul q using 1
    norm_num
  have positionContinuous : ContinuousOn (actualPositionBandDensity coordinate) (Ioi 0) := by
    intro x positive
    exact ((Complex.continuousAt_ofReal_cpow_const x (coordinate.value - 1) (Or.inr positive.ne')).mul
      (positionSource_continuousAt coordinate positive)).continuousWithinAt
  have fourierContinuous : ContinuousOn (actualFourierBandDensity coordinate) (Ioi 0) := by
    intro x positive
    exact ((Complex.continuousAt_ofReal_cpow_const x (-coordinate.value) (Or.inr positive.ne')).mul
      (burnolRieszSingleFourierSourceRaw_continuousAt coordinate positive.ne')).continuousWithinAt
  have positionPrimitive := intervalIntegral.integral_hasDerivAt_left
    (IntervalIntegrable.refl : IntervalIntegrable (actualPositionBandDensity coordinate) volume q q)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi positionContinuous q (by norm_num))
    (position_density_continuous coordinate)
  have fourierPrimitive := intervalIntegral.integral_hasDerivAt_left
    (IntervalIntegrable.refl : IntervalIntegrable (actualFourierBandDensity coordinate) volume q q)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi fourierContinuous q (by norm_num))
    (fourier_density_continuous coordinate)
  constructor
  · have atLower : HasDerivAt (fun u => ∫ x : ℝ in u..q, actualPositionBandDensity coordinate x)
        (-actualPositionBandDensity coordinate q) (q * Real.exp (-0)) := by simpa using positionPrimitive
    convert! atLower.scomp 0 lower using 1
    simp only [Complex.real_smul, Complex.ofReal_neg, neg_mul_neg]
  · have atLower : HasDerivAt (fun u => ∫ x : ℝ in u..q, actualFourierBandDensity coordinate x)
        (-actualFourierBandDensity coordinate q) (q * Real.exp (-0)) := by simpa using fourierPrimitive
    convert! atLower.scomp 0 lower using 1
    simp only [Complex.real_smul, Complex.ofReal_neg, neg_mul_neg]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
