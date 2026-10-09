import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.SourceActionResolvent

/-! Same-source contact and strong-action coordinates of the original Pa correction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem tate_orbit_derivative (value velocity : BurnolL2)
    (generated : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value) velocity 0) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (burnolTateReciprocalL2 value))
      (-burnolTateReciprocalL2 velocity) 0 := by
  have base : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value) velocity
      ((fun h : ℝ => -h) 0) := by simpa only [neg_zero] using generated
  have reverse := base.scomp (0 : ℝ) (hasDerivAt_id (0 : ℝ)).neg
  have mapped := (burnolTateReciprocalL2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 reverse
  convert! mapped using 1
  · funext h
    change burnolMultiplicativeDilation (-h / 2) (burnolTateReciprocalL2 value) =
      burnolTateReciprocalL2 (burnolMultiplicativeDilation (-(-h) / 2) value)
    rw [burnolTateReciprocalL2_dilation_inverse]
    simp only [neg_neg, neg_div]
  · simp

def sourceSecondWhole (coordinate : BurnolCompletedMellinCoordinate) (sigma : BurnolL2) : BurnolL2 :=
  (2 / (2 * coordinate.value - 1) : ℂ) •
    (burnolDirectRightResolvent (coordinate.value / 2) sigma +
      burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value / 2) sigma))

def sourceSecondVelocity (coordinate : BurnolCompletedMellinCoordinate) (sigma : BurnolL2) : BurnolL2 :=
  (1 / 2 : ℂ) • (burnolDirectRightResolvent (coordinate.value / 2) sigma -
    burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value / 2) sigma))

theorem source_second_strong (coordinate : BurnolCompletedMellinCoordinate) (sigma : BurnolL2)
    (fixed : burnolTateReciprocalL2 sigma = sigma) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (sourceSecondWhole coordinate sigma))
      (sourceSecondVelocity coordinate sigma) 0 ∧
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (sourceSecondVelocity coordinate sigma))
      (((coordinate.value / 2 - 1 / 4) ^ 2) • sourceSecondWhole coordinate sigma + sigma) 0 := by
  let z := coordinate.value
  let alpha := z / 2 - 1 / 4
  let X := burnolDirectRightResolvent (z / 2) sigma
  let W := X + burnolTateReciprocalL2 X
  let Y := X - burnolTateReciprocalL2 X
  have rq : 1 / 4 < (z / 2).re := by rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf]
  have direct : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) X)
      (alpha • X + sigma) 0 := burnolDirectRightResolventOrbit_hasDerivAt (z / 2) rq sigma
  have dual := tate_orbit_derivative X (alpha • X + sigma) direct
  rw [map_add, map_smul, fixed] at dual
  have whole : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) W) (alpha • Y) 0 := by
    convert! direct.add dual using 1
    · funext h
      rw [map_add]
      rfl
    · dsimp only [Y]
      module
  have odd : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) Y)
      (alpha • W + (2 : ℂ) • sigma) 0 := by
    convert! direct.sub dual using 1
    · funext h
      rw [map_sub]
      rfl
    · dsimp only [W]
      module
  have delta : 2 * z - 1 ≠ 0 := by
    intro zero
    have re := congrArg Complex.re zero
    norm_num [Complex.mul_re, Complex.sub_re] at re
    linarith [coordinate.rightHalf]
  have scale : (2 / (2 * z - 1) : ℂ) * alpha = 1 / 2 := by
    dsimp only [alpha]
    field_simp [delta]
    ring
  have square : alpha ^ 2 * (2 / (2 * z - 1) : ℂ) = (1 / 2 : ℂ) * alpha := by
    calc
      _ = ((2 / (2 * z - 1) : ℂ) * alpha) * alpha := by ring
      _ = _ := by rw [scale]
  constructor
  · convert! whole.const_smul (2 / (2 * z - 1) : ℂ) using 1
    · funext h
      change burnolMultiplicativeDilation (-h / 2) ((2 / (2 * z - 1) : ℂ) • W) = _
      rw [map_smul]
      rfl
    · change (1 / 2 : ℂ) • Y = (2 / (2 * z - 1) : ℂ) • (alpha • Y)
      rw [smul_smul, scale]
  · convert! odd.const_smul (1 / 2 : ℂ) using 1
    · funext h
      change burnolMultiplicativeDilation (-h / 2) ((1 / 2 : ℂ) • Y) = _
      rw [map_smul]
      rfl
    · change alpha ^ 2 • ((2 / (2 * z - 1) : ℂ) • W) + sigma =
        (1 / 2 : ℂ) • (alpha • W + (2 : ℂ) • sigma)
      rw [smul_smul, square]
      module

theorem pa_fixed_source (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius p = p) :
    burnolTateReciprocalL2 (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2 p) := by
  have read := burnolMobiusSource_fourier p inside
  rw [fixed] at read
  rw [burnolTateReciprocalL2_involutive]
  exact read

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
