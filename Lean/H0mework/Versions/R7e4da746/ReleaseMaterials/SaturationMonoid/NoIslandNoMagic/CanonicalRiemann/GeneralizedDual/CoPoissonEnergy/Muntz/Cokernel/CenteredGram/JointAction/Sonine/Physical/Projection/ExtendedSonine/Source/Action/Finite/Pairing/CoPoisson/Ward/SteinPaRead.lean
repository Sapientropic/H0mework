import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SteinPaRead

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def weight (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : ℂ :=
  (u : ℂ)⁻¹ * burnolRieszReturnRaw coordinate (2 * u)⁻¹

def slope (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) : ℂ :=
  (-1 / (u : ℂ) ^ 2) * burnolRieszReturnRaw coordinate (2 * u)⁻¹ +
    (u : ℂ)⁻¹ * ((-2 / (2 * u) ^ 2 : ℝ) • burnolRieszReturnRawDerivative coordinate (2 * u)⁻¹)

theorem derivative (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) (nonzero : u ≠ 0) :
    HasDerivAt (weight coordinate) (slope coordinate u) u := by
  have argument : HasDerivAt (fun t : ℝ => (2 * t)⁻¹) (-2 / (2 * u) ^ 2) u :=
    by simpa only [id_eq, mul_one] using!
      ((hasDerivAt_id u).const_mul 2).inv (mul_ne_zero (by norm_num) nonzero)
  exact (Complex.ofRealCLM.hasDerivAt.inv (Complex.ofReal_ne_zero.mpr nonzero)).mul
    ((burnolRieszReturnRaw_hasDerivAt coordinate (2 * u)⁻¹).scomp u argument)

theorem weight_measurable (coordinate : BurnolCompletedMellinCoordinate) : Measurable (weight coordinate) := by
  unfold weight
  exact Complex.measurable_ofReal.inv.mul
    ((burnolRieszReturnRaw_continuous coordinate).measurable.comp (measurable_const.mul measurable_id).inv)

theorem slope_measurable (coordinate : BurnolCompletedMellinCoordinate) : Measurable (slope coordinate) := by
  unfold slope
  have argument : Measurable (fun u : ℝ => (2 * u)⁻¹) := by fun_prop
  have first : Measurable (fun u : ℝ => -1 / (u : ℂ) ^ 2) := by fun_prop
  have inverse : Measurable (fun u : ℝ => (u : ℂ)⁻¹) := by fun_prop
  have scalar : Measurable (fun u : ℝ => -2 / (2 * u) ^ 2) := by fun_prop
  exact (first.mul ((burnolRieszReturnRaw_continuous coordinate).measurable.comp argument)).add
    (inverse.mul (scalar.smul ((burnolRieszReturnRawDerivative_continuous coordinate).measurable.comp argument)))

theorem slope_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (slope coordinate) (Icc (2 : ℝ) 4) := by
  intro u inside
  have nonzero : u ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) inside.1)
  have argument : ContinuousAt (fun t : ℝ => (2 * t)⁻¹) u :=
    (continuousAt_const.mul continuousAt_id).inv₀ (mul_ne_zero (by norm_num) nonzero)
  have inverse : ContinuousAt (fun t : ℝ => (t : ℂ)⁻¹) u :=
    Complex.continuous_ofReal.continuousAt.inv₀ (Complex.ofReal_ne_zero.mpr nonzero)
  unfold slope
  apply ContinuousAt.continuousWithinAt
  exact ((continuousAt_const.div (Complex.continuous_ofReal.continuousAt.pow 2)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr nonzero))).mul
      ((burnolRieszReturnRaw_continuous coordinate).continuousAt.comp argument)).add
    (inverse.mul ((continuousAt_const.div ((continuousAt_const.mul continuousAt_id).pow 2)
      (pow_ne_zero 2 (mul_ne_zero (by norm_num) nonzero))).smul
        ((burnolRieszReturnRawDerivative_continuous coordinate).continuousAt.comp argument)))

def source (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolWeightedReciprocalStepSource 2 4 (weight coordinate) (slope coordinate)

def wave (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolWeightedReciprocalStepWave 2 4 (weight coordinate) (slope coordinate)

/-- The original r supplies this actual outer half-window source, with its own endpoints. -/
theorem source_read (coordinate : BurnolCompletedMellinCoordinate) :
    (source coordinate : ℝ → ℂ) =ᵐ[volume] fun x =>
      if q < |x| ∧ |x| ≤ 2 * q then burnolRieszReturnRaw coordinate (|x| / 2) else 0 := by
  have actual := weighted_source_coeFn 2 4 (weight coordinate) (slope coordinate)
    (by norm_num) (by norm_num)
    (fun u inside => derivative coordinate u (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) inside.1)))
    (slope_continuous coordinate) (slope_measurable coordinate)
  filter_upwards [actual, volume.ae_ne (0 : ℝ)] with x read nonzero
  rw [source, read]
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have incidence : 2 ≤ |x|⁻¹ ∧ |x|⁻¹ < 4 ↔ q < |x| ∧ |x| ≤ 2 * q := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2) positive,
      inv_lt_comm₀ positive (by norm_num : (0 : ℝ) < 4)]
    norm_num
    exact and_comm
  unfold burnolReciprocalStepSourceRaw
  simp only [incidence]
  split_ifs
  · rw [weight, Complex.ofReal_inv, inv_inv]
    have argument : (2 * |x|⁻¹)⁻¹ = |x| / 2 := by field_simp
    rw [argument]
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  · exact mul_zero _

theorem wave_inPa (coordinate : BurnolCompletedMellinCoordinate) :
    wave coordinate ∈ burnolOriginalPaInL2 :=
  burnolWeightedReciprocalStepWave_inPa 2 4 _ _ (by norm_num) (by norm_num) (slope_continuous coordinate)

theorem original_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (source coordinate)) atTop (𝓝 (wave coordinate)) := by
  have generated := weightedPrefix_tendsto 2 4 (weight coordinate) (slope coordinate)
    (by norm_num) (slope_continuous coordinate)
  apply generated.congr'
  filter_upwards with N
  exact weighted_prefix_eq_finite_sub_continuous 2 4 _ _ N (by norm_num) (by norm_num)
    (fun u inside => derivative coordinate u (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) inside.1)))
    (slope_continuous coordinate) (slope_measurable coordinate) (weight_measurable coordinate)

/-- Only the generated forward Pa wave is consumed here; no Tate/reverse Pa invariance is asserted. -/
theorem original_zero (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (wave coordinate) (burnolCompletedMellinRieszVector coordinate : BurnolL2) = 0 := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp (wave_inPa coordinate)
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have read := (burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp orthogonal physical inPa
  change inner ℂ (physical : BurnolL2) (burnolCompletedMellinRieszVector coordinate : BurnolL2) = 0 at read
  change (physical : BurnolL2) = wave coordinate at actual
  rwa [actual] at read

theorem finite_pair_tendsto_zero (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => inner ℂ (FiniteForcing.source N (source coordinate))
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)) atTop (𝓝 0) := by
  simpa only [original_zero coordinate zero] using
    (original_tendsto coordinate).inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := (burnolCompletedMellinRieszVector coordinate : BurnolL2)))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SteinPaRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
