import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.FixedCollar

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CountedXi
open scoped Topology InnerProductSpace
open private ordinary_log_read ordinary_log_domain from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Mellin
open private fixed_collar_geometry from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.FixedCollar
local notation "q" => (1 / 4 : ℝ)
local notation "r₀" => q / stageZeroSonineQ
local notation "h₀" => Real.log stageZeroSonineQ

private theorem shifted_count_moment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (r : ℝ) (rPositive : 0 < r) (n : Nat) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (star c.value - 1) *
      (Real.log (x / r) : ℂ) ^ n * fullFloorRaw c x) volume 0 q ∧
    (∫ x : ℝ in (0 : ℝ)..q, (x : ℂ) ^ (star c.value - 1) *
      (Real.log (x / r) : ℂ) ^ n * fullFloorRaw c x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * (-(Real.log r : ℂ)) ^ (n - j) *
        iteratedDeriv j (mellin (fullFloorRaw c)) (star c.value) := by
  have positive : 0 < (star c.value).re := by
    simpa only [Complex.star_def, Complex.conj_re] using
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) c.rightHalf)
  let a : Nat → ℂ := fun j => (n.choose j : ℂ) * (-(Real.log r : ℂ)) ^ (n - j)
  let f : Nat → ℝ → ℂ := fun j x => (x : ℂ) ^ (star c.value - 1) * (Real.log x : ℂ) ^ j * fullFloorRaw c x
  have expansion (x : ℝ) (xPositive : 0 < x) :
      (x : ℂ) ^ (star c.value - 1) * (Real.log (x / r) : ℂ) ^ n * fullFloorRaw c x =
        ∑ j ∈ Finset.range (n + 1), a j * f j x := by
    rw [Real.log_div xPositive.ne' rPositive.ne', Complex.ofReal_sub,
      show (Real.log x : ℂ) - (Real.log r : ℂ) = (Real.log x : ℂ) + -(Real.log r : ℂ) by ring,
      add_pow, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [a, f]
    ring
  have pieces (j : Nat) (_member : j ∈ Finset.range (n + 1)) : IntervalIntegrable (fun x => a j * f j x) volume 0 q :=
    (ordinary_log_domain c zero j (star c.value) positive).const_mul (a j)
  have expanded := IntervalIntegrable.sum (Finset.range (n + 1)) pieces
  have domain : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (star c.value - 1) *
      (Real.log (x / r) : ℂ) ^ n * fullFloorRaw c x) volume 0 q := by
    apply expanded.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x inside
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ q)] at inside
    simpa only [Finset.sum_apply] using (expansion x inside.1).symm
  refine ⟨domain, ?_⟩
  have integral : (∫ x : ℝ in (0 : ℝ)..q, (x : ℂ) ^ (star c.value - 1) *
      (Real.log (x / r) : ℂ) ^ n * fullFloorRaw c x) =
        ∫ x : ℝ in (0 : ℝ)..q, ∑ j ∈ Finset.range (n + 1), a j * f j x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x inside
    exact expansion x inside.1
  rw [integral, intervalIntegral.integral_finsetSum pieces]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  change a j * (∫ x : ℝ in (0 : ℝ)..q, f j x) = _
  rw [show (∫ x : ℝ in (0 : ℝ)..q, f j x) =
      iteratedDeriv j (mellin (fullFloorRaw c)) (star c.value) by
    rw [actual_floor_iterated_mellin c zero j _ positive, ordinary_log_read]]

theorem actual_shifted_count_top_moment (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (r : ℝ) (rPositive : 0 < r) :
    (∫ x : ℝ in (0 : ℝ)..q, (x : ℂ) ^ (star c.value - 1) *
      (Real.log (x / r) : ℂ) ^ (generatedRiemannXiZeroOrder ActualAnalyticOwner c.value - 1) * fullFloorRaw c x) =
      ((generatedRiemannXiZeroOrder ActualAnalyticOwner c.value - 1).factorial : ℂ) *
        generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star c.value) (star c.value) / 2 := by
  rw [(shifted_count_moment c zero r rPositive _).2]
  rw [Finset.sum_eq_single (generatedRiemannXiZeroOrder ActualAnalyticOwner c.value - 1)]
  · simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, one_mul]
    exact actual_count_top_jet c zero
  · intro j member different
    have lower : j < generatedRiemannXiZeroOrder ActualAnalyticOwner c.value - 1 := by
      have := Finset.mem_range.mp member
      omega
    rw [actual_count_lower_jet c zero j lower, mul_zero]
  · intro absent
    exact (absent (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
include nontrivial

/-- The complete C bank is paid by its original top jet; the actual smaller-radius prefix remains intact. -/
theorem actual_native_unit_plus_fixed_prefix_top :
    inner ℂ (U (m - 1)) (burnolMultiplicativeDilation h₀ (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native.nativeReturn c)) =
      fullMellinTranslationCharacter (star (c).value) (-h₀) *
        ((2 : ℂ) ^ (m - 1) * generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star (c).value) (star (c).value) -
          (2 : ℂ) ^ m / ((m - 1).factorial : ℂ) *
            (∫ x : ℝ in (0 : ℝ)..r₀, (x : ℂ) ^ (star (c).value - 1) *
              (Real.log (x / r₀) : ℂ) ^ (m - 1) * fullFloorRaw c x) - star e) := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have zero : riemannZeta (c).value = 0 := observation.mathlibZero
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (star (c).value - 1) *
    (Real.log (x / r₀) : ℂ) ^ (m - 1) * fullFloorRaw c x
  have domain : IntervalIntegrable f volume 0 q := (shifted_count_moment c zero r₀ fixed_collar_geometry.1 (m - 1)).1
  have left : IntervalIntegrable f volume 0 r₀ := domain.mono_set (by
    rw [uIcc_of_le fixed_collar_geometry.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
    exact Icc_subset_Icc le_rfl fixed_collar_geometry.2.2.1.le)
  have right : IntervalIntegrable f volume r₀ q := domain.mono_set (by
    rw [uIcc_of_le fixed_collar_geometry.2.2.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
    exact Icc_subset_Icc fixed_collar_geometry.1.le le_rfl)
  have whole : (∫ x : ℝ in (0 : ℝ)..q, f x) = ((m - 1).factorial : ℂ) *
      generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star (c).value) (star (c).value) / 2 :=
    actual_shifted_count_top_moment c zero r₀ fixed_collar_geometry.1
  have split := intervalIntegral.integral_add_adjacent_intervals left right
  have collar : (∫ x : ℝ in r₀..q, f x) = ((m - 1).factorial : ℂ) *
      generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star (c).value) (star (c).value) / 2 -
        ∫ x : ℝ in (0 : ℝ)..r₀, f x := by
    rw [whole] at split
    linear_combination split
  rw [actual_native_unit_plus_fixed_collar_top observation nontrivial half]
  change _ * ((2 : ℂ) ^ m / ((m - 1).factorial : ℂ) * (∫ x : ℝ in r₀..q, f x) - star e) = _
  rw [collar]
  have power : (2 : ℂ) ^ m = (2 : ℂ) ^ (m - 1) * 2 := by
    calc
      _ = (2 : ℂ) ^ ((m - 1) + 1) := congrArg (fun n : Nat => (2 : ℂ) ^ n) (by omega)
      _ = _ := pow_succ _ _
  have factorial : ((m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - 1)
  let b := generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star (c).value) (star (c).value)
  let prefixPrice := ∫ x : ℝ in (0 : ℝ)..r₀, f x
  change fullMellinTranslationCharacter (star (c).value) (-h₀) *
    ((2 : ℂ) ^ m / ((m - 1).factorial : ℂ) * (((m - 1).factorial : ℂ) * b / 2 - prefixPrice) - star e) =
    fullMellinTranslationCharacter (star (c).value) (-h₀) *
      ((2 : ℂ) ^ (m - 1) * b - (2 : ℂ) ^ m / ((m - 1).factorial : ℂ) * prefixPrice - star e)
  have paid : (2 : ℂ) ^ m / ((m - 1).factorial : ℂ) * (((m - 1).factorial : ℂ) * b / 2) =
      (2 : ℂ) ^ (m - 1) * b := by
    rw [power]
    field_simp [factorial]
  simp only [mul_sub, paid]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
