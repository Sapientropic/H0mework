import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedJointNoetherSourcePrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumColumnClock

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.GaussComposite.ActualSourcePreparedFourClockCarrier
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedNoether
open PreparationVacuumPhysicalPoleSheet ActualDressedSignal
open PreparationVacuumActionFieldLift
open ActualDressedFrequencyHalf ActualDressedStaticResponse ActualDressedUniformMaterialCoefficients
open ActualDressedSylvester
open ActualDressedUniformClockNonzero ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMTensorClock
open ActualSourcePreparedJointNoetherSourcePrice
open LowEnergy.ActualDressedVisiblePole Filter Set
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open scoped Topology Matrix BigOperators
attribute [local irreducible] commonNumerator commonDenominator dressedStaticPolarization

private theorem positive_complex_punctured :
    Tendsto (fun sigma : ℝ => (sigma : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using positive.ne'

theorem bounded_fraction_clock_factor (P D : ℂ[X]) (B : ℝ) (nonzero : D ≠ 0)
    (bound : ∀ sigma : ℝ, 0 < sigma → sigma ≤ 1 →
      ‖P.eval (sigma : ℂ) / D.eval (sigma : ℂ)‖ ≤ B) :
    (X : ℂ[X]) ^ D.natTrailingDegree ∣ P := by
  let R := readFraction P D
  have noPole : poleOrder R 0 = 0 := by
    by_contra failed
    have high : 0 < poleOrder R 0 := Nat.pos_of_ne_zero failed
    have root : (0 : ℂ) ∈ visibleRoots R := by
      rw [visibleRoots, mem_roots (RatFunc.denom_ne_zero R)]
      exact (rootMultiplicity_pos (RatFunc.denom_ne_zero R)).mp high
    have nonzeroLeading := leading_pole_coefficient_nonzero R 0 root
    have price : Tendsto (fun sigma : ℝ => sigma ^ poleOrder R 0 * B)
        (𝓝[>] 0) (𝓝 0) := by
      have identity : Tendsto (fun sigma : ℝ => sigma) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left inf_le_left
      simpa only [zero_pow high.ne', zero_mul] using (identity.pow (poleOrder R 0)).mul_const B
    have near : ∀ᶠ sigma : ℝ in 𝓝[>] 0, sigma < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
    have chart := (source_static_punctured_chart D nonzero).filter_mono
      (nhdsWithin_mono 0 (show Ioi (0 : ℝ) ⊆ {0}ᶜ from fun s h => by simpa using h.ne'))
    have zero : Tendsto (fun sigma : ℝ => (sigma : ℂ) ^ poleOrder R 0 *
        (R.num.eval (sigma : ℂ) / R.denom.eval (sigma : ℂ))) (𝓝[>] 0) (𝓝 0) := by
      apply squeeze_zero_norm' _ price
      filter_upwards [self_mem_nhdsWithin, near, chart] with sigma positive small regular
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg positive.le _)
      rw [reduced_read_at_regular P D (sigma : ℂ) regular]
      exact bound sigma positive small.le
    have actual := (pole_order_limit R 0).comp positive_complex_punctured
    simp only [Function.comp_def, sub_zero] at actual
    exact nonzeroLeading (tendsto_nhds_unique actual zero)
  by_cases pZero : P = 0
  · rw [pZero]
    exact dvd_zero _
  have cross := reduced_cross_identity P D nonzero
  have rightNonzero : P * R.denom ≠ 0 := mul_ne_zero pZero (RatFunc.denom_ne_zero R)
  have leftNonzero : R.num * D ≠ 0 := by rw [cross]; exact rightNonzero
  have order := congrArg (fun Q : ℂ[X] => Q.rootMultiplicity 0) cross
  rw [rootMultiplicity_mul leftNonzero, rootMultiplicity_mul rightNonzero] at order
  change R.num.rootMultiplicity 0 + D.rootMultiplicity 0 =
    P.rootMultiplicity 0 + poleOrder R 0 at order
  rw [noPole, add_zero, rootMultiplicity_eq_natTrailingDegree' (p := D)] at order
  have less : D.natTrailingDegree ≤ P.rootMultiplicity 0 := by omega
  simpa using (le_rootMultiplicity_iff pZero).mp less

theorem bivariate_bounded_clock_factor (P D : (ℂ[X])[X])
    (nonzero : ∀ eps : ℝ, clockSpecialize eps D ≠ 0)
    (bounded : ∀ eps : ℝ, ∃ B : ℝ, ∀ sigma : ℝ, 0 < sigma → sigma ≤ 1 →
      ‖(clockSpecialize eps P).eval (sigma : ℂ) /
        (clockSpecialize eps D).eval (sigma : ℂ)‖ ≤ B) :
    (X : (ℂ[X])[X]) ^ D.natTrailingDegree ∣ P := by
  apply X_pow_dvd_iff.mpr
  intro k less
  apply Polynomial.eq_of_infinite_eval_eq (P.coeff k) 0
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro z ⟨eps, rfl⟩
  obtain ⟨B, price⟩ := bounded eps
  have factor := bounded_fraction_clock_factor (clockSpecialize eps P)
    (clockSpecialize eps D) B (nonzero eps) price
  have mLe : D.natTrailingDegree ≤ (clockSpecialize eps D).natTrailingDegree := by
    apply le_natTrailingDegree (nonzero eps)
    intro j low
    simp only [clockSpecialize, Polynomial.coe_mapRingHom, coeff_map]
    rw [coeff_eq_zero_of_lt_natTrailingDegree low, map_zero]
  have inherited : (X : ℂ[X]) ^ D.natTrailingDegree ∣ clockSpecialize eps P :=
    dvd_trans (pow_dvd_pow X mLe) factor
  have zero := X_pow_dvd_iff.mp inherited k less
  change (P.coeff k).eval (eps : ℂ) = (0 : ℂ[X]).eval (eps : ℂ)
  simpa only [clockSpecialize, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coe_evalRingHom, eval_zero] using zero

/-- The original clock clearing polynomial, before spatial specialization. -/
def sourceFourClockClearing (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  staticIRClockSlice (commonDenominator event n)

def sourceFourClockOrder (event : DressedEvent) (n : PhysicalMomentum) : ℕ :=
  (sourceFourClockClearing event n).natTrailingDegree

def sourceFourClockNumerator (event : DressedEvent) (n : PhysicalMomentum) (i j : Fin 289) :
    (ℂ[X])[X] := X^4 * staticIRClockSlice (commonNumerator event n i j)

theorem static_pi_clear (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma) (i j : Fin 289) :
    MvPolynomial.eval (irValues eps sigma 0) (commonDenominator event n) *
      dressedStaticPolarization event (eps^2 • n) (sigma : ℂ) i j =
    MvPolynomial.eval (irValues eps sigma 0) (commonNumerator event n i j) := by
  have clear := congrFun (congrFun (actual_common_ir_pi_clear event n eps sigma 0 positive) i) j
  have clock : dampedFourierClock (sourceFrequency eps 0) sigma = (sigma : ℂ) := by
    simp [dampedFourierClock, sourceFrequency]
  have static : frequencyRay eps 0 n 0 = 0 := by
    simp [frequencyRay, physicalFrequencyMomentum]
  rw [clock] at clear
  have same := dressed_static_polarization_actual event (eps^2 • n)
    (frequencyRay eps 0 n) static (sigma : ℂ) (by simpa using positive) i j
  change dressedSignalHalfOperator event (eps^2 • n) (frequencyRay eps 0 n)
    (sigma : ℂ) (Pi.single j 1) i = _ at same
  change MvPolynomial.eval (irValues eps sigma 0) (commonDenominator event n) *
    dressedSignalHalfOperator event (eps^2 • n) (frequencyRay eps 0 n)
      (sigma : ℂ) (Pi.single j 1) i = _ at clear
  rw [same] at clear
  exact clear

private theorem source_static_clearing_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (eps : ℝ) : clockSpecialize eps (sourceFourClockClearing event n) ≠ 0 := by
  have value := actual_common_ir_denominator_nonzero event n eps 1 0 (by norm_num)
  have evaluate : (clockSpecialize eps (sourceFourClockClearing event n)).eval (1 : ℂ) ≠ 0 := by
    rw [sourceFourClockClearing, ir_clock_specialize]
    have bridge := damping_slice_eval eps 1 (commonDenominator event n)
    simp only [Complex.ofReal_one] at bridge
    exact fun zero => value (bridge.symm.trans zero)
  exact fun zero => evaluate (by rw [zero, eval_zero])

private theorem source_four_clock_ratio (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (positive : 0 < sigma) (i j : Fin 289) :
    (clockSpecialize eps (sourceFourClockNumerator event n i j)).eval (sigma : ℂ) /
      (clockSpecialize eps (sourceFourClockClearing event n)).eval (sigma : ℂ) =
      (sigma : ℂ)^4 * dressedStaticPolarization event (eps^2 • n) (sigma : ℂ) i j := by
  have dNonzero := actual_common_ir_denominator_nonzero event n eps sigma 0 positive
  have clear := static_pi_clear event n eps sigma positive i j
  simp only [sourceFourClockNumerator, sourceFourClockClearing, map_mul, map_pow,
    clockSpecialize, Polynomial.coe_mapRingHom, Polynomial.map_X, eval_mul, eval_pow, eval_X]
  change (sigma : ℂ)^4 * (clockSpecialize eps (staticIRClockSlice (commonNumerator event n i j))).eval
      (sigma : ℂ) / (clockSpecialize eps (staticIRClockSlice (commonDenominator event n))).eval
      (sigma : ℂ) = _
  rw [ir_clock_specialize, ir_clock_specialize, damping_slice_eval, damping_slice_eval, ← clear]
  field_simp

/-- The full source sigma-four price forces every lower clock coefficient to
vanish on the common spatial-clock carrier; no factor witness is supplied. -/
theorem source_four_clock_numerator_factor (event : DressedEvent) (n : PhysicalMomentum)
    (i j : Fin 289) :
    (X : (ℂ[X])[X]) ^ sourceFourClockOrder event n ∣ sourceFourClockNumerator event n i j := by
  apply bivariate_bounded_clock_factor _ _ (source_static_clearing_nonzero event n)
  intro eps
  refine ⟨56 * sourceJointCubicNoetherPrice event n (eps^2) (fieldUnit i) (fieldUnit j), ?_⟩
  intro sigma positive small
  rw [source_four_clock_ratio event n eps sigma positive i j, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  exact source_joint_polarization_sigma_four_price event eps n (eps^2) le_rfl sigma positive small i j

def sourceFourClockDenominator (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  sourceFourClockClearing event n /ₘ X ^ sourceFourClockOrder event n

def sourceFourClockResponseNumerator (event : DressedEvent) (n : PhysicalMomentum) (i j : Fin 289) :
    (ℂ[X])[X] := sourceFourClockNumerator event n i j /ₘ X ^ sourceFourClockOrder event n

private theorem power_quotient {R : Type*} [CommRing R] (P : R[X]) (m : ℕ) (factor : X^m ∣ P) :
    X^m * (P /ₘ X^m) = P := by
  obtain ⟨Q, eq⟩ := factor
  rw [eq, mul_divByMonic_cancel_left Q (monic_X_pow m)]

theorem source_four_clock_denominator_factor (event : DressedEvent) (n : PhysicalMomentum) :
    X ^ sourceFourClockOrder event n * sourceFourClockDenominator event n = sourceFourClockClearing event n :=
  power_quotient _ _ (X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less))

theorem source_four_clock_response_factor (event : DressedEvent) (n : PhysicalMomentum) (i j : Fin 289) :
    X ^ sourceFourClockOrder event n * sourceFourClockResponseNumerator event n i j =
      sourceFourClockNumerator event n i j :=
  power_quotient _ _ (source_four_clock_numerator_factor event n i j)

end LowEnergy.GaussComposite.ActualSourcePreparedFourClockCarrier
