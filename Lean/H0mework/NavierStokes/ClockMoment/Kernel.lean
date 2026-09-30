import H0mework.NavierStokes.InitialData.SourceOwnedLocalKernelAbsorption

set_option autoImplicit false
open scoped BigOperators
namespace SaturationMonoid.NavierStokes.NativeUnheatedClockMomentKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
noncomputable section

theorem cube_mono {first last : ℕ} (ordered : first ≤ last) :
    integerWaveFrequencyCube first ⊆ integerWaveFrequencyCube last := by
  intro wave inside
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at inside ⊢
  intro coordinate
  have range := inside coordinate
  rw [Finset.mem_Icc] at range ⊢
  constructor <;> omega

def shell (radius : ℕ) := integerWaveFrequencyCube (radius+1) \ integerWaveFrequencyCube radius

theorem shell_card (radius : ℕ) : (shell radius).card = 24*(radius+1)^2+2 := by
  rw [shell, Finset.card_sdiff_of_subset (cube_mono (Nat.le_succ radius)), integerWaveFrequencyCube_card, integerWaveFrequencyCube_card]
  have same : (2*(radius+1)+1)^3 = (24*(radius+1)^2+2)+(2*radius+1)^3 := by ring
  rw [same]
  omega

theorem shell_frequency (radius : ℕ) (wave : IntegerWavevector) (inside : wave ∈ shell radius) :
    ((radius+1 : ℕ) : ℝ)^2 ≤ integerWaveNormSq wave := by
  have outside := (Finset.mem_sdiff.mp inside).2
  have large : radius < integerWaveCoordinateRadius wave := by
    by_contra notLarge
    exact outside (integerWave_mem_frequencyCube_of_radius_le wave radius (Nat.le_of_not_gt notLarge))
  rw [integerWaveCoordinateRadius] at large
  obtain ⟨coordinate, _, large⟩ := Finset.lt_sup_iff.mp large
  have step : radius+1 ≤ Int.natAbs (wave coordinate) := Nat.succ_le_iff.mpr large
  have natAbsCast : ((Int.natAbs (wave coordinate) : ℕ) : ℝ) = |(wave coordinate : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
    norm_cast
  have scalar : ((radius+1 : ℕ) : ℝ) ≤ |(wave coordinate : ℝ)| := by
    rw [← natAbsCast]
    exact_mod_cast step
  apply (pow_le_pow_left₀ (by positivity) scalar 2).trans
  rw [sq_abs]
  unfold integerWaveNormSq
  exact Finset.single_le_sum (fun other _ => sq_nonneg (wave other : ℝ)) (Finset.mem_univ coordinate)

theorem shell_inverse_sum (radius : ℕ) : (∑ wave ∈ shell radius, (integerWaveNormSq wave)⁻¹) ≤ 26 := by
  have row (wave : IntegerWavevector) (inside : wave ∈ shell radius) :
      (integerWaveNormSq wave)⁻¹ ≤ (((radius+1 : ℕ) : ℝ)^2)⁻¹ :=
    inv_anti₀ (by positivity) (shell_frequency radius wave inside)
  have paid := Finset.sum_le_card_nsmul _ _ _ row
  rw [shell_card, nsmul_eq_mul] at paid
  apply paid.trans
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have positive : 0 < (radius : ℝ)+1 := by positivity
  have atLeast : (1 : ℝ) ≤ (radius : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) radius]
  apply (mul_inv_le_iff₀ (sq_pos_of_pos positive)).mpr
  nlinarith [sq_nonneg ((radius : ℝ)+1-1)]

theorem cube_inverse_sum (radius : ℕ) :
    (∑ wave ∈ integerWaveFrequencyCube radius, (integerWaveNormSq wave)⁻¹) ≤ 26*(radius : ℝ) := by
  induction radius with
  | zero =>
      have cube : integerWaveFrequencyCube 0 = {0} := by
        ext wave
        simp only [integerWaveFrequencyCube, Fintype.mem_piFinset, Finset.mem_Icc, Int.natCast_zero, neg_zero,
          Finset.mem_singleton]
        constructor
        · intro member; funext coordinate; exact le_antisymm (member coordinate).2 (member coordinate).1
        · intro zero; subst wave; simp
      simp [cube, integerWaveNormSq]
  | succ radius previous =>
      rw [← Finset.sum_sdiff (cube_mono (Nat.le_succ radius))]
      have paid := add_le_add (shell_inverse_sum radius) previous
      convert! paid using 1
      push_cast
      ring

theorem velocity_reciprocal_bound (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes state ^ 2 ≤
      biotSavartSerrinConstant * (∑ wave ∈ modes, (integerWaveNormSq wave)⁻¹) * finiteStateVorticityCoefficientEnstrophy modes state := by
  have row (wave : IntegerWavevector) : complexCoordinateAmplitudeSq (finiteStateVelocityCoefficient state wave) ≤
      (biotSavartSerrinConstant * (integerWaveNormSq wave)⁻¹) * complexCoordinateAmplitudeSq (state wave) := by
    apply (finiteStateVelocityCoefficient_criticalAmplitudeSq_le state wave).trans_eq
    unfold integerWaveCriticalKernel
    by_cases zero : integerWaveNormSq wave = 0
    · simp [zero]
    · field_simp
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul modes
    (r := fun wave => Real.sqrt (complexCoordinateAmplitudeSq (finiteStateVelocityCoefficient state wave)))
    (f := fun wave => biotSavartSerrinConstant * (integerWaveNormSq wave)⁻¹)
    (g := fun wave => complexCoordinateAmplitudeSq (state wave))
    (fun wave _ => mul_nonneg biotSavartSerrinConstant_nonneg (inv_nonneg.mpr (integerWaveNormSq_nonneg wave)))
    (fun _ _ => complexCoordinateAmplitudeSq_nonneg _) (fun wave _ => by
      rw [Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg _)]
      exact row wave)
  simpa only [finiteStateVelocityMajorant, finiteVelocityFourierMajorant, finiteStateVorticityCoefficientEnstrophy, Finset.mul_sum] using cauchy

def core (nu : Viscosity) (ceiling : ℝ) : ℝ :=
  biotSavartSerrinConstant * ∑ wave ∈ sourceOwnedLocalKernelCore nu ceiling, (integerWaveNormSq wave)⁻¹

theorem core_nonnegative (nu : Viscosity) (ceiling : ℝ) : 0 ≤ core nu ceiling :=
  mul_nonneg biotSavartSerrinConstant_nonneg (Finset.sum_nonneg fun wave _ => inv_nonneg.mpr (integerWaveNormSq_nonneg wave))

theorem core_radius_bound (nu : Viscosity) (ceiling : ℝ) :
    core nu ceiling ≤ 26*biotSavartSerrinConstant*(sourceOwnedLocalKernelRadius nu ceiling : ℝ) := by
  rw [core, sourceOwnedLocalKernelCore_eq_frequencyCube]
  exact (mul_le_mul_of_nonneg_left (cube_inverse_sum _) biotSavartSerrinConstant_nonneg).trans_eq (by ring)

theorem core_linear_bound (nu : Viscosity) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling) :
    core nu ceiling ≤ 26*biotSavartSerrinConstant*(sourceOwnedLocalKernelRadiusSlope nu+2)*(ceiling+1) := by
  exact (core_radius_bound nu ceiling).trans ((mul_le_mul_of_nonneg_left
    (sourceOwnedLocalKernelRadius_lt_linear nu ceiling nonnegative).le (by positivity [biotSavartSerrinConstant_pos])).trans_eq (by ring))

theorem low_majorant_bound (nu : Viscosity) (ceiling : ℝ) (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant (sourceOwnedLocalLowModes nu ceiling modes) state ^ 2 ≤
      core nu ceiling * finiteStateVorticityCoefficientEnstrophy modes state := by
  have reciprocal := Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right (s₁ := modes)
    (s₂ := sourceOwnedLocalKernelCore nu ceiling)) (fun wave _ _ => inv_nonneg.mpr (integerWaveNormSq_nonneg wave))
  have mass := Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left (s₁ := modes)
    (s₂ := sourceOwnedLocalKernelCore nu ceiling)) (fun wave _ _ => complexCoordinateAmplitudeSq_nonneg (state wave))
  exact (velocity_reciprocal_bound _ state).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left reciprocal biotSavartSerrinConstant_nonneg) mass
    (Finset.sum_nonneg fun _ _ => complexCoordinateAmplitudeSq_nonneg _) (core_nonnegative nu ceiling))

theorem majorant_bound (nu : Viscosity) (ceiling : ℝ) (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes state ^ 2 ≤ 2*core nu ceiling*finiteStateVorticityCoefficientEnstrophy modes state +
      2*biotSavartSerrinConstant*sourceOwnedKernelTailTolerance nu ceiling*finiteStateVorticityEnstrophyMass modes state := by
  have low := low_majorant_bound nu ceiling modes state
  have high := sourceOwnedLocalHigh_velocityMajorant_sq_le nu ceiling modes state
  have split := sourceOwnedLocalVelocityMajorant_split nu ceiling modes state
  rw [← split]
  nlinarith [sq_nonneg (finiteStateVelocityMajorant (sourceOwnedLocalLowModes nu ceiling modes) state -
    finiteStateVelocityMajorant (sourceOwnedLocalHighModes nu ceiling modes) state)]

theorem stretching_bound (nu : Viscosity) (ceiling : ℝ) (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (transverse : ∀ wave ∈ modes, complexWavevector wave ⬝ᵥ state wave = 0)
    (below : finiteStateVorticityCoefficientEnstrophy modes state ≤ ceiling) :
    finiteStateVorticityStretchingWork modes state - nu.coeff*(2*Real.pi)^2*
      finiteStateVorticityEnstrophyMass modes state ≤
      -(3*nu.coeff/8)*((2*Real.pi)^2*finiteStateVorticityEnstrophyMass modes state) +
        nu.coeff⁻¹*core nu ceiling*finiteStateVorticityCoefficientEnstrophy modes state^2 := by
  apply (finiteStateVorticity_stretching_sub_viscous_le_criticalRate modes state nu.coeff nu.coeff_pos transverse).trans
  have enstrophy0 : 0 ≤ finiteStateVorticityCoefficientEnstrophy modes state :=
    Finset.sum_nonneg fun _ _ => complexCoordinateAmplitudeSq_nonneg _
  have bounded := mul_le_mul_of_nonneg_right (majorant_bound nu ceiling modes state)
    (mul_nonneg (div_nonneg (inv_nonneg.mpr nu.coeff_pos.le) (by norm_num : (0 : ℝ) ≤ 2)) enstrophy0)
  have absorbed := sourceOwnedLocalHigh_nonlinearTerm_le_viscousEighth nu ceiling modes state below
  unfold finiteStateVorticityCriticalEnstrophyRate
  nlinarith

end
end SaturationMonoid.NavierStokes.NativeUnheatedClockMomentKernel
