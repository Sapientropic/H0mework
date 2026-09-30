import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.EnergySize
import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.EffectiveTime
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeightedInverse

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryEffectiveBounds
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent
open NativeWholeH1Mixed (modes)
open NativeWindowHistoryEffectiveInverse (Operator average generator unit)
open NativeWindowHistoryEffectiveTime (jet)
open NativeWindowHistoryHeatDual (energy heatEnergy)
open NativeWindowHistoryHeatSize (size)
open NativeWindowHistorySchurForm (cap)
open NativeWindowFiniteStressUniform (kernelBound)
noncomputable section
variable {nu : Viscosity}

private theorem inverse_negative_product {R : Type*} [Ring R] (A J X : R) (inverse : A*J=1) :
    A*(-J*X)= -X := by
  rw [← mul_assoc,mul_neg,inverse,neg_one_mul]

def normalized (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : Operator M :=
  average seed M 0 time*jet seed M order time

theorem normalized_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : normalized seed M 0 time=1 :=
  (unit seed M time).val_inv

theorem recover (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    generator seed M time*normalized seed M order time=jet seed M order time := by
  change generator seed M time*(average seed M 0 time*jet seed M order time)=_
  rw [← mul_assoc,show generator seed M time*average seed M 0 time=1 from (unit seed M time).inv_val,one_mul]

theorem normalized_recurrence (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    normalized seed M (order+1) time= -∑ i∈Finset.range (order+1),
      ((order+1).choose (i+1) : Operator M)*average seed M (i+1) time*generator seed M time*normalized seed M (order-i) time := by
  have paid : normalized seed M (order+1) time= -∑ i∈Finset.range (order+1),
      ((order+1).choose (i+1) : Operator M)*average seed M (i+1) time*jet seed M (order-i) time := by
    change average seed M 0 time*jet seed M (order+1) time=_
    rw [NativeWindowHistoryEffectiveTime.jet_recurrence]
    simpa only [] using! inverse_negative_product (R := Operator M) (average seed M 0 time) (generator seed M time) _ (unit seed M time).val_inv
  refine paid.trans (congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => ?_)))
  rw [← recover seed M (order-i) time]
  simp only [mul_assoc]

theorem normalized_apply (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    normalized seed M (order+1) time v= -∑ i∈Finset.range (order+1),
      (order+1).choose (i+1) • average seed M (i+1) time (generator seed M time (normalized seed M (order-i) time v)) := by
  have source := congrArg (fun A : Operator M => A v) (normalized_recurrence seed M order time)
  simpa only [neg_apply,sum_apply,mul_apply_eq_comp,ContinuousLinearMap.natCast_apply] using! source

def radius (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℕ → ℝ
  | 0 => 1
  | order+1 => ∑ i∈Finset.range (order+1),((order+1).choose (i+1) : ℝ)*kernelBound (i+1)*cap seed horizon*radius seed horizon (order-i)
termination_by order => order
decreasing_by omega

theorem radius_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) :
    0 ≤ radius seed horizon order := by
  induction order using Nat.strong_induction_on with
  | h order ih =>
    cases order with
    | zero => rw [radius]; exact zero_le_one
    | succ order =>
      rw [radius]
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (NativeWindowFiniteStressUniform.kernelBound_positive (i+1)).le)
        (NativeWindowHistorySchurForm.cap_nonnegative seed horizon)) (ih (order-i) (by omega))

theorem source_composed_size (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    size nu M (average seed M order time (generator seed M time v)) ≤ kernelBound order*cap seed horizon*size nu M v := by
  have paid := NativeWindowHistorySchurWeightedInverse.source_time_word_bound seed horizon M order time inside v
  have normalizedBound : energy nu M (average seed M order time (generator seed M time v)) ≤
      (kernelBound order*cap seed horizon)^2*energy nu M v := paid.trans_eq (by ring)
  exact NativeWindowHistoryHeatSize.size_bound nu M _ v _
    (mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive order).le (NativeWindowHistorySchurForm.cap_nonnegative seed horizon)) normalizedBound

theorem source_normalized_size (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    size nu M (normalized seed M order time v) ≤ radius seed horizon order*size nu M v := by
  induction order using Nat.strong_induction_on with
  | h order ih =>
    cases order with
    | zero =>
      rw [normalized_zero,radius]
      simp only [one_apply_eq_self,one_mul,le_refl]
    | succ order =>
      rw [normalized_apply,NativeWindowHistoryHeatSize.size_neg,radius]
      refine (NativeWindowHistoryHeatSize.size_sum nu M (Finset.range (order+1)) _).trans ?_
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have raw := source_composed_size seed horizon M (i+1) time inside (normalized seed M (order-i) time v)
      have old := ih (order-i) (by omega)
      have scaled := (mul_le_mul_of_nonneg_left old (mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive (i+1)).le
        (NativeWindowHistorySchurForm.cap_nonnegative seed horizon)))
      have term := (NativeWindowHistoryHeatSize.size_nsmul nu M ((order+1).choose (i+1)) _).trans
        (mul_le_mul_of_nonneg_left (raw.trans scaled) (Nat.cast_nonneg _))
      exact term.trans_eq (by ring)

theorem source_normalized_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    energy nu M (normalized seed M order time v) ≤ (radius seed horizon order)^2*energy nu M v :=
  NativeWindowHistoryHeatSize.energy_bound nu M _ v _ (source_normalized_size seed horizon M order time inside v)

theorem source_jet_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    heatEnergy nu M (jet seed M order time v) ≤ (cap seed horizon*radius seed horizon order)^2*energy nu M v := by
  have recovery := congrArg (fun A : Operator M => A v) (recover seed M order time)
  have actual := congrArg (heatEnergy nu M) recovery
  exact actual.symm.trans_le
    ((NativeWindowHistorySchurWeightedInverse.source_generator_bound seed horizon M time inside (normalized seed M order time v)).trans
      ((mul_le_mul_of_nonneg_left (source_normalized_bound seed horizon M order time inside v) (sq_nonneg _)).trans_eq (by ring)))

theorem source_pairing_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (u v : physicalSpace (modes M)) :
    |pairing (modes M) u (jet seed M order time v)| ≤
      cap seed horizon*radius seed horizon order*size nu M u*size nu M v := by
  have paid := (NativeWindowHistoryHeatDual.dual_pairing_bound nu M u (jet seed M order time v)).trans
    (mul_le_mul_of_nonneg_left (source_jet_bound seed horizon M order time inside v)
      (NativeWindowHistoryHeatDual.energy_nonnegative nu M u))
  have source := Real.sqrt_le_sqrt paid
  rw [Real.sqrt_sq_eq_abs,Real.sqrt_mul (NativeWindowHistoryHeatDual.energy_nonnegative nu M u),
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg (NativeWindowHistorySchurForm.cap_nonnegative seed horizon)
      (radius_nonnegative seed horizon order))] at source
  exact source.trans_eq (by change size nu M u*(cap seed horizon*radius seed horizon order*size nu M v)=_; ring)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem normalized_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    normalized seed M order (step.2.clockAdvance+time)=normalized step.1 M order time :=
  congrArg₂ (fun A J : Operator M => A*J)
    (NativeWindowHistoryEffectiveInverse.average_next seed M 0 step generated time time0)
    (NativeWindowHistoryEffectiveTime.jet_next seed M order step generated time time0)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryEffectiveBounds
