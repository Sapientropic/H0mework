import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.OriginalHead
import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.FourierPhysical

/-! The original W profile produces every integer-cell derivative and contact flux. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaGreenContact
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def cellWave (s : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  1 / s - 1 / (1 - s) - (x : ℂ) ^ (-s) * (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (s - 1)) +
    (x : ℂ) ^ (s - 1) * (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (-s))

def cellFlux (s : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  s * (x : ℂ) ^ (1 - s) * (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (s - 1)) +
    (s - 1) * (x : ℂ) ^ s * (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (-s))

theorem cell_wave_read (s : ℂ) (k : ℕ) {x : ℝ}
    (inside : x ∈ Ioc (k : ℝ) (k + 1 : ℝ)) :
    burnolUnitTailDirichletRaw s 1 x - burnolUnitTailDirichletRaw (1 - s) 1 x =
      cellWave s k x := by
  have positive : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg k) inside.1
  have ceil : ⌈x⌉₊ = k + 1 := (Nat.ceil_eq_iff (by omega : k + 1 ≠ 0)).mpr (by simpa using inside)
  have channels : burnolUnitTailDirichletChannels 1 x = Finset.Icc 1 k := by
    simp only [burnolUnitTailDirichletChannels, div_one, abs_of_pos positive, ceil, Finset.Ico_add_one_right_eq_Icc]
  simp only [burnolUnitTailDirichletRaw, Complex.ofReal_one, Complex.one_cpow, channels,
    abs_of_pos positive, cellWave, show -(1 - s) = s - 1 by ring,
    show 1 - s - 1 = -s by ring]
  ring

theorem cell_flux_derivative (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ)
    {x : ℝ} (positive : 0 < x) :
    HasDerivAt (cellFlux coordinate.value k)
      (-coordinate.value * (1 - coordinate.value) * cellWave coordinate.value k x -
        (2 * coordinate.value - 1)) x := by
  let s := coordinate.value
  have sn : s ≠ 0 := by intro zero; have re := congrArg Complex.re zero; simp only [Complex.zero_re] at re; linarith [coordinate.rightHalf]
  have on : 1 - s ≠ 0 := by
    intro zero
    have re := congrArg Complex.re zero
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at re
    linarith [coordinate.belowOne]
  have left := ((hasDerivAt_ofReal_cpow_const positive.ne' on).const_mul s).mul_const
    (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (s - 1))
  have right := ((hasDerivAt_ofReal_cpow_const positive.ne' sn).const_mul (s - 1)).mul_const
    (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (-s))
  convert! left.add right using 1
  simp only [cellWave, show 1 - s - 1 = -s by ring]
  change -s * (1 - s) * (1 / s - 1 / (1 - s) - _ + _) - (2 * s - 1) = _
  field_simp [sn, on]
  ring

theorem cell_wave_derivative (coordinate : BurnolCompletedMellinCoordinate) (k : ℕ)
    {x : ℝ} (positive : 0 < x) :
    HasDerivAt (cellWave coordinate.value k)
      ((x : ℂ) ^ (-2 : ℂ) * cellFlux coordinate.value k x) x := by
  let s := coordinate.value
  have sn : s ≠ 0 := by
    intro zero
    have re := congrArg Complex.re zero
    simp only [Complex.zero_re] at re
    linarith [coordinate.rightHalf]
  have sm : s - 1 ≠ 0 := by
    intro zero
    have re := congrArg Complex.re zero
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at re
    linarith [coordinate.belowOne]
  have left := (hasDerivAt_ofReal_cpow_const positive.ne' (neg_ne_zero.mpr sn)).mul_const
    (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (s - 1))
  have right := (hasDerivAt_ofReal_cpow_const positive.ne' sm).mul_const
    (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (-s))
  have nonzero : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have firstPower : (x : ℂ) ^ (-2 : ℂ) * (x : ℂ) ^ (1 - s) = (x : ℂ) ^ (-s - 1) := by
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  have secondPower : (x : ℂ) ^ (-2 : ℂ) * (x : ℂ) ^ s = (x : ℂ) ^ (s - 1 - 1) := by
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  convert! ((hasDerivAt_const x (1 / s - 1 / (1 - s))).sub left).add right using 1
  change (x : ℂ) ^ (-2 : ℂ) * cellFlux s k x = _
  simp only [cellFlux]
  calc
    _ = s * ((x : ℂ) ^ (-2 : ℂ) * (x : ℂ) ^ (1 - s)) * (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (s - 1)) +
        (s - 1) * ((x : ℂ) ^ (-2 : ℂ) * (x : ℂ) ^ s) * (∑ n ∈ Finset.Icc 1 k, (n : ℂ) ^ (-s)) := by ring
    _ = _ := by rw [firstPower, secondPower]; ring

theorem actual_wave_cell {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (k : ℕ) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    (((one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier) : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (k : ℝ) (k + 1 : ℝ))] cellWave observation.coordinate k := by
  filter_upwards [ae_restrict_of_ae (burnolZeroOwnedUnitOnePair_dirichlet_coeFn observation nontrivial rightHalf),
    ae_restrict_mem measurableSet_Ioc] with x read inside
  exact read.trans (cell_wave_read observation.coordinate k inside)

theorem cell_wave_at_contact (s : ℂ) (k : ℕ) :
    cellWave s (k + 1) (k + 1 : ℝ) = cellWave s k (k + 1 : ℝ) := by
  simp only [cellWave, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1),
    Nat.cast_add, Nat.cast_one]
  push_cast
  ring

theorem cell_flux_contact (s : ℂ) (k : ℕ) :
    cellFlux s (k + 1) (k + 1 : ℝ) - cellFlux s k (k + 1 : ℝ) = 2 * s - 1 := by
  have nonzero : ((k : ℂ) + 1) ≠ 0 := by
    have positive : (0 : ℝ) < k + 1 := by positivity
    exact_mod_cast positive.ne'
  have powers : ((k : ℂ) + 1) ^ (1 - s) * ((k : ℂ) + 1) ^ (s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ nonzero, show 1 - s + (s - 1) = 0 by ring, Complex.cpow_zero]
  have dual : ((k : ℂ) + 1) ^ s * ((k : ℂ) + 1) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ nonzero, add_neg_cancel, Complex.cpow_zero]
  simp only [cellFlux, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), Nat.cast_add, Nat.cast_one]
  push_cast
  calc
    _ = s * (((k : ℂ) + 1) ^ (1 - s) * ((k : ℂ) + 1) ^ (s - 1)) +
      (s - 1) * (((k : ℂ) + 1) ^ s * ((k : ℂ) + 1) ^ (-s)) := by ring
    _ = _ := by rw [powers, dual]; ring


end
end OriginalPaGreenContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
