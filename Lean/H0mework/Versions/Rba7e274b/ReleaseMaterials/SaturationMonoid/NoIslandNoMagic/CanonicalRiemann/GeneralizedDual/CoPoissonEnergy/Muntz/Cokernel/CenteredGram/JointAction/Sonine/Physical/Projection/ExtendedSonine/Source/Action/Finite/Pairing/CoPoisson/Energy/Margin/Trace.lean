import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Source
import H0mework.Versions.V2.Arithmetic.RieszGreen.KernelGram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy.Margin

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFinitePairing
open OriginalRieszFinitePairing.CoPoisson

noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

theorem positionSource_endpoint (coordinate : BurnolCompletedMellinCoordinate) :
    positionSource coordinate q = -Kernel.A coordinate := by
  have actual := GapEuler.gapMean_primitive q (by norm_num) coordinate
  unfold positionSource Kernel.A
  linear_combination -actual

theorem fourierSource_endpoint (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszSingleFourierSourceRaw coordinate q = Kernel.beta coordinate := rfl

private theorem endpoint_of_seed_zero (shift : ℝ) (positive : 0 < shift)
    (profile : ℝ → ℂ) (regular : ∀ x, 0 < x → ContinuousAt profile x) (seed : BurnolL2)
    (read : ∀ test : BurnolL2, inner ℂ test seed =
      ∫ x : ℝ, inner ℂ (test x) (bandRaw shift profile x)) (zeroSeed : seed = 0) :
    profile q = 0 := by
  let radius : ℝ := q * Real.exp shift
  let window : Set ℝ := Ioc q radius
  let raw : ℝ → ℂ := fun x => -(Real.exp (-shift / 2) : ℂ) * profile (Real.exp (-shift) * x)
  have ordered : q < radius := by
    have exponential : 1 < Real.exp shift := Real.one_lt_exp_iff.mpr positive
    dsimp only [radius]
    nlinarith
  have continuousRaw : ContinuousOn raw (Icc q radius) := by
    intro x inside
    have xPositive : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < q) inside.1
    exact (continuousAt_const.mul ((regular _ (mul_pos (Real.exp_pos _) xPositive)).comp
      (continuousAt_const.mul continuousAt_id))).continuousWithinAt
  have integrableRaw : IntegrableOn raw window :=
    continuousRaw.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have integrableSquare : IntegrableOn (fun x => ‖raw x‖ ^ 2) window :=
    (continuousRaw.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have localLp : MemLp raw 2 (volume.restrict window) :=
    (memLp_two_iff_integrable_sq_norm integrableRaw.aestronglyMeasurable).mpr integrableSquare
  have rawLp : MemLp (window.indicator raw) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc).mpr localLp
  let test : BurnolL2 := rawLp.toLp (window.indicator raw)
  have testRead : (test : ℝ → ℂ) =ᵐ[volume] window.indicator raw := rawLp.coeFn_toLp
  have selfZero : inner ℂ test test = 0 := by
    have actual := read test
    rw [zeroSeed, inner_zero_right] at actual
    rw [L2.inner_def]
    apply Eq.trans _ actual.symm
    apply integral_congr_ae
    filter_upwards [testRead] with x source
    by_cases inside : x ∈ window
    · have xPositive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) inside.1
      have active : q < x ∧ x ≤ q * Real.exp shift := inside
      rw [source, indicator_of_mem inside]
      simp only [bandRaw, abs_of_pos xPositive, if_pos active]
      rfl
    · rw [source, indicator_of_notMem inside]
      simp
  have testZero : test = 0 := inner_self_eq_zero.mp selfZero
  have rawZero : raw =ᵐ[volume.restrict window] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae testRead, ae_restrict_of_ae (Lp.coeFn_zero ℂ 2 volume),
      ae_restrict_mem measurableSet_Ioc] with x source zero inside
    rw [testZero] at source
    rw [zero, indicator_of_mem inside] at source
    exact source.symm
  have endpoint : raw radius = 0 := Measure.eqOn_Ioc_of_ae_eq volume rawZero
    (continuousRaw.mono Ioc_subset_Icc_self) continuousOn_const ⟨ordered, le_rfl⟩
  have inverse : Real.exp (-shift) * radius = q := by
    dsimp only [radius]
    rw [Real.exp_neg]
    field_simp
  change -(Real.exp (-shift / 2) : ℂ) * profile (Real.exp (-shift) * radius) = 0 at endpoint
  rw [inverse] at endpoint
  exact (mul_eq_zero.mp endpoint).resolve_left
    (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))

theorem positionSeed_zero_A (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (positive : 0 < shift) (zeroSeed : positionSeed coordinate shift = 0) : Kernel.A coordinate = 0 := by
  have endpoint := endpoint_of_seed_zero shift positive (positionSource coordinate)
    (fun _ hx => positionSource_continuousAt coordinate hx) (positionSeed coordinate shift)
    (positionSeed_pairing coordinate shift positive.le) zeroSeed
  rw [positionSource_endpoint, neg_eq_zero] at endpoint
  exact endpoint

theorem fourierSeed_zero_beta (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (positive : 0 < shift) (zeroSeed : fourierSeed coordinate shift = 0) : Kernel.beta coordinate = 0 :=
  endpoint_of_seed_zero shift positive (burnolRieszSingleFourierSourceRaw coordinate)
    (fun _ hx => burnolRieszSingleFourierSourceRaw_continuousAt coordinate hx.ne')
    (fourierSeed coordinate shift) (fourierSeed_pairing coordinate shift positive.le) zeroSeed

theorem source_energy_zero_kernel (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (positive : 0 < shift)
    (zeroEnergy : inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift) = 0) :
    (K coordinate : BurnolL2) = 0 := by
  have realEnergy := congrArg Complex.re zeroEnergy
  simp only [Complex.add_re, Complex.zero_re] at realEnergy
  have positionNorm : (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift)).re =
      ‖positionSeed coordinate shift‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  have fourierNorm : (inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re =
      ‖fourierSeed coordinate shift‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [positionNorm, fourierNorm] at realEnergy
  have positionZero : positionSeed coordinate shift = 0 := norm_eq_zero.mp (by
    nlinarith [sq_nonneg ‖fourierSeed coordinate shift‖, norm_nonneg (positionSeed coordinate shift)])
  have fourierZero : fourierSeed coordinate shift = 0 := norm_eq_zero.mp (by
    nlinarith [sq_nonneg ‖positionSeed coordinate shift‖, norm_nonneg (fourierSeed coordinate shift)])
  have AZero := positionSeed_zero_A coordinate shift positive positionZero
  have betaZero := fourierSeed_zero_beta coordinate shift positive fourierZero
  have gram := original_kernel_gram coordinate coordinate
  rw [AZero, betaZero] at gram
  simp only [star_zero, mul_zero, sub_self] at gram
  have coefficient : coordinate.value + star coordinate.value - 1 ≠ 0 := by
    intro zero
    have real := congrArg Complex.re zero
    change coordinate.value.re + coordinate.value.re - 1 = 0 at real
    linarith [coordinate.rightHalf]
  exact inner_self_eq_zero.mp ((mul_eq_zero.mp gram).resolve_left coefficient)

end
end OriginalRieszFinitePairing.CoPoisson.Energy.Margin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
