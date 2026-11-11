import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ConstantFourier

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- The actual Tate image of the original constant is the existing scaled reciprocal primitive. -/
theorem reciprocal_source : burnolTateReciprocalL2 ConstantDual.seed =
    burnolSourceScalePrimitive burnolUnitReciprocalPrimitiveL2 q := by
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp ConstantDual.seed)
    ((Lp.memLp ConstantDual.seed).ae_eq ConstantDual.seed_coeFn) ConstantDual.seed_coeFn
  apply Lp.ext
  filter_upwards [burnolTateReciprocalL2_coeFn ConstantDual.seed, pulled,
    burnolSourceScalePrimitive_coeFn burnolUnitReciprocalPrimitiveL2 burnolUnitReciprocalPrimitiveRaw
      burnolUnitReciprocalPrimitive_coeFn q (by norm_num),
    volume.ae_ne (0 : ℝ), volume.ae_ne (4 : ℝ), volume.ae_ne (-4 : ℝ)]
      with x actual raw scaled nonzero notRight notLeft
  rw [actual, raw, scaled]
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have notEdge : |x| ≠ 4 := by
    intro equality
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 4)).mp equality with right | left
    · exact notRight right
    · exact notLeft left
  have incidence : |x⁻¹| ≤ q ↔ 1 < |q * x| := by
    rw [abs_inv, inv_le_comm₀ positive (by norm_num : (0 : ℝ) < q), abs_mul]
    norm_num
    constructor
    · intro inside
      have strict : 4 < |x| := lt_of_le_of_ne inside notEdge.symm
      linarith
    · intro inside
      linarith
  unfold burnolTateReciprocalRaw ConstantDual.seedRaw burnolUnitReciprocalPrimitiveRaw
  simp only [incidence]
  split_ifs
  · rw [mul_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < q), Complex.ofReal_mul]
    field_simp
  · simp

/-- Closed floor and open primitive endpoints agree in L²; their countable exceptional set is explicit. -/
theorem reciprocal_value : burnolTateReciprocalL2 ConstantDual.value =
    burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 q := by
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp ConstantDual.value)
    ConstantDual.sawtooth_memLp ConstantDual.value_coeFn
  have offGrid : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ, x ≠ 4 * n ∧ x ≠ -(4 * n) := by
    apply ae_all_iff.mpr
    intro n
    exact (volume.ae_ne (4 * n : ℝ)).and (volume.ae_ne (-(4 * n) : ℝ))
  apply Lp.ext
  filter_upwards [burnolTateReciprocalL2_coeFn ConstantDual.value, pulled,
    burnolSourceScalePrimitive_coeFn burnolUnitCountingPrimitiveL2 burnolUnitCountingPrimitiveRaw
      burnolUnitCountingPrimitive_memLp.coeFn_toLp q (by norm_num), offGrid]
      with x actual raw scaled off
  have nonzero : x ≠ 0 := by simpa using (off 0).1
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have nonnegative : 0 ≤ q * |x| := by positivity
  have noninteger (n : ℕ) : q * |x| ≠ n := by
    intro equality
    have absolute : |x| = 4 * n := by linarith
    rcases (abs_eq (by positivity : (0 : ℝ) ≤ 4 * n)).mp absolute with right | left
    · exact (off n).1 right
    · exact (off n).2 left
  have rounding : ⌈q * |x|⌉₊ = ⌊q * |x|⌋₊ + 1 := by
    apply (Nat.ceil_eq_iff (by omega)).mpr
    simp only [Nat.add_sub_cancel]
    exact ⟨lt_of_le_of_ne (Nat.floor_le nonnegative) (noninteger _).symm,
      by exact_mod_cast (Nat.lt_floor_add_one (q * |x|)).le⟩
  rw [actual, raw, scaled]
  unfold burnolTateReciprocalRaw ConstantDual.sawtoothRaw burnolUnitCountingPrimitiveRaw
  rw [if_neg (mul_ne_zero (by norm_num : q ≠ 0) nonzero), abs_inv,
    div_inv_eq_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < q), rounding, Int.fract,
    ← natCast_floor_eq_intCast_floor nonnegative]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  ring

/-- Full source realization, including its nonzero normalization, identifies the Fourier output. -/
theorem original_square : fourierL2 ConstantForward.value = burnolTateReciprocalL2 ConstantDual.value := by
  have actual := burnolRemainderRealization_fourier ConstantDual.seed ConstantForward.value
    ConstantForward.original_realizes
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  have source := actual test
  rw [reciprocal_source, burnolSourceScalePrimitive_realizes q (by norm_num) (by norm_num)] at source
  rw [reciprocal_value]
  exact source.symm

/-- The actual full finite reverse programme acts on F(E1), not a mean-zero replacement. -/
theorem original_tendsto :
    Tendsto (fun N : ℕ => DualSource.source N (fourierL2 ConstantDual.seed)) atTop
      (𝓝 (burnolTateReciprocalL2 ConstantDual.value)) := by
  have actual := (fourierL2.continuous.tendsto ConstantForward.value).comp ConstantForward.original_tendsto
  rw [original_square] at actual
  exact actual.congr' (Eventually.of_forall (fun N => (KCounting.dual_fourier N ConstantDual.seed).symm))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ConstantFourier
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
