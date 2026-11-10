import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedZeroClockReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedProjectedClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalNativePhotonFluxReturn ActualDressedFullCoulomb
open ActualDressedOrderedStatic ActualDressedEMTensorClock ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMQuantumThreshold ActualDressedFrequencyHalf ActualEMAction
open ActualSourcePreparedNoetherPi ActualSourcePreparedPhotonPoleRead
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedZeroClockReturn
open Filter Set
open scoped Matrix BigOperators Topology

attribute [local irreducible] fullClockClearing fullClockQuantumNumerator fullClockPencil
  sourcePreparedPiEntry sourcePreparedPhotonPoleResponse sourcePreparedModeResponse
  sourcePhotonLeftReaderCLM emOriginalJacobi

def sourceStaticClockClearing (event : DressedEvent) (epsilon : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  clockSpecialize 0 (fullClockClearing event epsilon n)

theorem source_static_clock_clearing_positive (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    (sourceStaticClockClearing event epsilon n).eval (sigma : ℂ) ≠ 0 := by
  have paid := ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero
    event n epsilon sigma 0 positive
  rw [← frequency_damping_eval epsilon 0 sigma, ← frequency_clock_specialize epsilon 0] at paid
  simpa only [sourceStaticClockClearing, fullClockClearing] using paid

theorem source_static_clock_clearing_nonzero (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) : sourceStaticClockClearing event epsilon n ≠ 0 := by
  have paid := source_static_clock_clearing_positive event epsilon 1 n (by norm_num)
  intro zero
  rw [zero, eval_zero] at paid
  exact paid rfl

def sourceStaticClockOrder (event : DressedEvent) (epsilon : ℝ) (n : PhysicalMomentum) : ℕ :=
  (sourceStaticClockClearing event epsilon n).natTrailingDegree

theorem source_static_clock_leading_nonzero (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) :
    (sourceStaticClockClearing event epsilon n).coeff (sourceStaticClockOrder event epsilon n) ≠ 0 :=
  coeff_natTrailingDegree_ne_zero.mpr (source_static_clock_clearing_nonzero event epsilon n)

private theorem reader_basis (L : (Fin 289 → ℂ) →L[ℂ] ℂ) (v : Fin 289 → ℂ) :
    L v = ∑i, L (Pi.single i 1) * v i := by
  have split : v = ∑i, v i • (Pi.single i 1 : Fin 289 → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  calc
    L v = L (∑i, v i • (Pi.single i 1 : Fin 289 → ℂ)) := congrArg L split
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul, mul_comm]

def sourceProjectedClockNumerator (event : DressedEvent) (epsilon : ℝ) (n : PhysicalMomentum)
    (branch : Fin 2) (sheet : ℝ) : ℂ[X] :=
  let L := sourcePhotonLeftReaderCLM branch epsilon sheet n
  let U := sourceNativeFrequencyPolarization branch epsilon sheet n
  ∑i, ∑j, C (L (Pi.single i 1)) *
    (X * clockSpecialize 0 (fullClockQuantumNumerator event epsilon n i j)) * C (U j)

private theorem prepared_entry_fraction (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (i j : Fin 289) :
    (sigma : ℂ) * sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j =
      (X * clockSpecialize 0 (fullClockQuantumNumerator event epsilon n i j)).eval (sigma : ℂ) /
        (sourceStaticClockClearing event epsilon n).eval (sigma : ℂ) := by
  have fraction := actual_pencil_clock_fraction event epsilon sigma 0 n positive i j
  rw [← source_prepared_static_pencil_actual event epsilon sigma n positive] at fraction
  have equation := congrArg (fun P : ℂ[X] => P.eval (sigma : ℂ))
    (actual_clock_quantum_polynomial event epsilon 0 n i j)
  simp only [eval_sub, eval_mul, eval_C] at equation
  rw [equation] at fraction
  change emOriginalJacobi (frequencyRay epsilon 0 n) i j -
      (sigma : ℂ) * sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j = _ at fraction
  have denominator := source_static_clock_clearing_positive event epsilon sigma n positive
  change (clockSpecialize 0 (fullClockClearing event epsilon n)).eval (sigma : ℂ) ≠ 0 at denominator
  rw [sub_div, mul_div_cancel_left₀ _ denominator] at fraction
  simpa only [sourceStaticClockClearing, eval_mul] using (sub_right_inj.mp fraction)

/-- The scalar full response is generated from the original matrix numerator and
independent left/right mode. No full-matrix balance or clearing-chart premise is used. -/
theorem source_prepared_projected_clock_fraction (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) (positive : 0 < sigma) :
    (sigma : ℂ) * sourcePreparedPhotonPoleResponse event ((epsilon^2 : ℝ) • n)
        branch epsilon sheet n (sigma : ℂ) =
      (sourceProjectedClockNumerator event epsilon n branch sheet).eval (sigma : ℂ) /
        (sourceStaticClockClearing event epsilon n).eval (sigma : ℂ) := by
  have paid : 0 < (sigma : ℂ).re := by simpa using positive
  unfold sourcePreparedPhotonPoleResponse
  rw [source_prepared_mode_response_actual event ((epsilon^2 : ℝ) • n) (sigma : ℂ) paid,
    reader_basis]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  unfold sourceProjectedClockNumerator
  simp only [eval_finsetSum, eval_mul, eval_C, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have entry := prepared_entry_fraction event epsilon sigma n positive i j
  simp only [eval_mul] at entry
  linear_combination (sourcePhotonLeftReaderCLM branch epsilon sheet n (Pi.single i 1)) *
    (sourceNativeFrequencyPolarization branch epsilon sheet n j) * entry

private theorem factored_limit (N D : ℂ[X]) (m : ℕ) (nf : X^m ∣ N) (df : X^m ∣ D)
    (regular : D.coeff m ≠ 0) :
    Tendsto (fun sigma : ℝ => N.eval (sigma : ℂ) / D.eval (sigma : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (N.coeff m / D.coeff m)) := by
  obtain ⟨Nq, nEq⟩ := nf
  obtain ⟨Dq, dEq⟩ := df
  have nValue : Nq.eval 0 = N.coeff m := by
    rw [nEq, ← coeff_zero_eq_eval_zero]
    simpa only [zero_add] using (coeff_X_pow_mul Nq m 0).symm
  have dValue : Dq.eval 0 = D.coeff m := by
    rw [dEq, ← coeff_zero_eq_eval_zero]
    simpa only [zero_add] using (coeff_X_pow_mul Dq m 0).symm
  have qRegular : Dq.eval 0 ≠ 0 := by rw [dValue]; exact regular
  have cn : Continuous (fun sigma : ℝ => Nq.eval (sigma : ℂ)) := by fun_prop
  have cd : Continuous (fun sigma : ℝ => Dq.eval (sigma : ℂ)) := by fun_prop
  have base := (cn.continuousAt.div cd.continuousAt qRegular).tendsto.mono_left
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0 from inf_le_left)
  simp only [Pi.div_apply, Complex.ofReal_zero] at base
  rw [nValue, dValue] at base
  apply Tendsto.congr' _ base
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  have nonzero : (sigma : ℂ)^m ≠ 0 :=
    pow_ne_zero m (Complex.ofReal_ne_zero.mpr (ne_of_gt positive))
  rw [nEq, dEq]
  simp only [eval_mul, eval_pow, eval_X, Pi.div_apply]
  exact (mul_div_mul_left _ _ nonzero).symm

/-- Only this actual electromagnetic scalar numerator must pay the effective
clock order; all other full-matrix entries retain their own source behaviour. -/
theorem source_prepared_projected_clock_limit (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ)
    (finite : X^sourceStaticClockOrder event epsilon n ∣
      sourceProjectedClockNumerator event epsilon n branch sheet) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ) * sourcePreparedPhotonPoleResponse event
        ((epsilon^2 : ℝ) • n) branch epsilon sheet n (sigma : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 ((sourceProjectedClockNumerator event epsilon n branch sheet).coeff
          (sourceStaticClockOrder event epsilon n) /
        (sourceStaticClockClearing event epsilon n).coeff (sourceStaticClockOrder event epsilon n))) := by
  have factor : X^sourceStaticClockOrder event epsilon n ∣ sourceStaticClockClearing event epsilon n :=
    X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)
  have limit := factored_limit _ _ _ finite factor
    (source_static_clock_leading_nonzero event epsilon n)
  apply Tendsto.congr' _ limit
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  exact (source_prepared_projected_clock_fraction event epsilon sigma n branch sheet positive).symm

/-- The original input-integral normalization provides one clock factor in every
term of the actual projected numerator. -/
theorem source_projected_clock_has_input_factor (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ) :
    X ∣ sourceProjectedClockNumerator event epsilon n branch sheet := by
  unfold sourceProjectedClockNumerator
  apply Finset.dvd_sum
  intro i _
  apply Finset.dvd_sum
  intro j _
  refine ⟨C (sourcePhotonLeftReaderCLM branch epsilon sheet n (Pi.single i 1)) *
    clockSpecialize 0 (fullClockQuantumNumerator event epsilon n i j) *
      C (sourceNativeFrequencyPolarization branch epsilon sheet n j), ?_⟩
  ring

/-- On the source order-zero/one clearing branch the finite scalar response is
fully generated, without a supplied projected numerator cancellation. -/
theorem source_prepared_projected_low_order_limit (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (branch : Fin 2) (sheet : ℝ)
    (order : sourceStaticClockOrder event epsilon n ≤ 1) :
    Tendsto (fun sigma : ℝ => (sigma : ℂ) * sourcePreparedPhotonPoleResponse event
        ((epsilon^2 : ℝ) • n) branch epsilon sheet n (sigma : ℂ))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 ((sourceProjectedClockNumerator event epsilon n branch sheet).coeff
          (sourceStaticClockOrder event epsilon n) /
        (sourceStaticClockClearing event epsilon n).coeff (sourceStaticClockOrder event epsilon n))) := by
  apply source_prepared_projected_clock_limit
  have factor := source_projected_clock_has_input_factor event epsilon n branch sheet
  have exponent : (X : ℂ[X])^sourceStaticClockOrder event epsilon n ∣ X := by
    simpa only [pow_one] using (pow_dvd_pow X order)
  exact dvd_trans exponent factor

end LowEnergy.GaussComposite.ActualSourcePreparedProjectedClock
