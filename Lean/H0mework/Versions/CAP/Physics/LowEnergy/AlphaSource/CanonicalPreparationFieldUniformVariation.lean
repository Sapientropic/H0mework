import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPhysicalLaplace
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldPerturbation
open SourceFiniteUnitary FullYSourceCutoffVolterra CanonicalGradedVariation
open MeasureTheory Set Filter
open scoped Topology Interval

section Variation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

 theorem time_operator_derivative (C : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (time C) (time C t*((-Complex.I) • C)) t :=
  hasDerivAt_exp_smul_const ((-Complex.I) • C) t

 theorem time_continuous (C : E →L[ℂ] E) : Continuous (time C) :=
  continuous_iff_continuousAt.mpr (fun t=>(time_operator_derivative C t).continuousAt)

 theorem time_unit_bound (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) : ‖time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul,time_norm C symmetric] using (le_refl ‖x‖)

 def picture (C A : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=time (C+A) t*time C (-t)

 theorem picture_derivative (C A : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (picture C A) (picture C A t*interaction C A t) t := by
  have hU:=time_operator_derivative (C+A) t
  have hV:=(time_operator_derivative C (-t)).scomp t ((hasDerivAt_id t).neg)
  have generated:=hU.mul hV
  have commuting : ((-Complex.I) • C)*time C (-t)=time C (-t)*((-Complex.I) • C) :=
    ((time_commutes C C (Commute.refl C) (-t)).smul_left (-Complex.I)).eq
  have inverse : time C (-t)*time C t=1 := by rw [←time_add,neg_add_cancel,time_zero]
  have reduced : picture C A t*interaction C A t=time (C+A) t*((-Complex.I) • A)*time C (-t) := by
    unfold picture interaction
    calc
      _ = (time (C+A) t*(time C (-t)*time C t))*((-Complex.I) • A)*time C (-t) := by simp only [mul_assoc]
      _ = _ := by rw [inverse,mul_one]
  rw [reduced]
  convert! generated using 1
  simp only [Function.comp_apply,neg_one_smul,smul_add,mul_add,add_mul,mul_neg,mul_assoc]
  rw [←commuting]
  abel

 theorem picture_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) (future : 0 ≤ t) :
    ‖picture C A t‖ ≤ Real.exp (‖A‖*t) := by
  have continuous : Continuous (picture C A) := continuous_iff_continuousAt.mpr
    (fun s=>(picture_derivative C A s).continuousAt)
  have derivative (s : ℝ) (_ : s∈Ico 0 t) :
      HasDerivWithinAt (picture C A) (picture C A s*interaction C A s) (Ici s) s :=
    (picture_derivative C A s).hasDerivWithinAt
  have initial : ‖picture C A 0‖ ≤ (1:ℝ) := by
    simpa only [picture,neg_zero,time_zero,one_mul] using time_unit_bound C symmetric 0
  have bound (s : ℝ) (_ : s∈Ico 0 t) :
      ‖picture C A s*interaction C A s‖ ≤ ‖A‖*‖picture C A s‖+0 :=
    (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (interaction_bound C A symmetric s) (norm_nonneg _)).trans_eq (by ring))
  have h:=norm_le_gronwallBound_of_norm_deriv_right_le continuous.continuousOn derivative initial bound t ⟨future,le_rfl⟩
  simpa only [sub_zero,gronwallBound_ε0,one_mul] using h

 theorem perturbed_time_positive_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) (future : 0 ≤ t) :
    ‖time (C+A) t‖ ≤ Real.exp (‖A‖*t) := by
  have inverse : time C (-t)*time C t=1 := by rw [←time_add,neg_add_cancel,time_zero]
  have reconstruction : time (C+A) t=picture C A t*time C t := by
    unfold picture
    rw [mul_assoc,inverse,mul_one]
  rw [reconstruction]
  exact (norm_mul_le _ _).trans ((mul_le_mul (picture_bound C A symmetric t future)
    (time_unit_bound C symmetric t) (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_one _))

 theorem time_neg_generator (C : E →L[ℂ] E) (t : ℝ) : time (-C) t=time C (-t) := by
  simp only [time,smul_neg,neg_smul]

 theorem perturbed_time_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    ‖time (C+A) t‖ ≤ Real.exp (‖A‖*|t|) := by
  by_cases future : 0 ≤ t
  · simpa only [abs_of_nonneg future] using perturbed_time_positive_bound C A symmetric t future
  · have h:=perturbed_time_positive_bound (-C) (-A) symmetric.neg (-t) (by linarith)
    simpa only [←neg_add,time_neg_generator,neg_neg,norm_neg,abs_of_nonpos (le_of_not_ge future)] using h

 theorem interval_times {s t : ℝ} (member : s∈Ι (0:ℝ) t) : |s| ≤ |t| ∧ |t-s| ≤ |t| := by
  by_cases future : 0 ≤ t
  · rw [uIoc_of_le future] at member
    rw [abs_of_pos member.1,abs_of_nonneg future,abs_of_nonneg (sub_nonneg.mpr member.2)]
    constructor <;> linarith [member.1,member.2]
  · have past : t ≤ 0 := le_of_not_ge future
    rw [uIoc_of_ge past] at member
    rw [abs_of_nonpos member.2,abs_of_nonpos past,abs_of_nonpos (by linarith [member.1] : t-s ≤ 0)]
    constructor <;> linarith [member.1,member.2]

 theorem variation_integrable (K B : E →L[ℂ] E) (r t : ℝ) :
    IntervalIntegrable (fun s=>time (K+r • B) s*((-Complex.I) • B)*time K (t-s)) volume 0 t :=
  (((time_continuous (K+r • B)).mul continuous_const).mul
    ((time_continuous K).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t

 theorem variationBetween_window (K B : E →L[ℂ] E) (r T P Q t : ℝ)
    (_hP : 0 ≤ P) (hQ : 0 ≤ Q) (within : |t| ≤ T)
    (base : ∀ s,|s| ≤ T → ‖time K s‖ ≤ P)
    (perturbed : ∀ s,|s| ≤ T → ‖time (K+r • B) s‖ ≤ Q) :
    ‖variationBetween K B r t‖ ≤ |t| *Q*‖B‖*P := by
  unfold variationBetween
  have bound (s : ℝ) (hs : s∈Ι (0:ℝ) t) :
      ‖time (K+r • B) s*((-Complex.I) • B)*time K (t-s)‖ ≤ Q*‖B‖*P := by
    have normB : ‖(-Complex.I) • B‖=‖B‖ := by rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
    have innerBound : ‖time (K+r • B) s*((-Complex.I) • B)‖ ≤ Q*‖B‖ := by
      apply (norm_mul_le _ _).trans
      rw [normB]
      exact mul_le_mul_of_nonneg_right (perturbed s ((interval_times hs).1.trans within)) (norm_nonneg B)
    exact (norm_mul_le _ _).trans (mul_le_mul innerBound
      (base (t-s) ((interval_times hs).2.trans within)) (norm_nonneg _) (mul_nonneg hQ (norm_nonneg B)))
  exact (intervalIntegral.norm_integral_le_of_norm_le_const bound).trans_eq (by rw [sub_zero];ring)

 theorem parameter_difference_window (K B : E →L[ℂ] E) (r T P Q t : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (within : |t| ≤ T)
    (base : ∀ s,|s| ≤ T → ‖time K s‖ ≤ P)
    (perturbed : ∀ s,|s| ≤ T → ‖time (K+r • B) s‖ ≤ Q) :
    ‖time (K+r • B) t-time K t‖ ≤ |r| *|t| *Q*‖B‖*P := by
  rw [parameter_difference,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (variationBetween_window K B r T P Q t hP hQ within base perturbed)
    (abs_nonneg r)).trans_eq (by ring)

 theorem variation_difference_identity (K B : E →L[ℂ] E) (r t : ℝ) :
    variationBetween K B r t-variation K B t=
      ∫ s in (0:ℝ)..t,(time (K+r • B) s-time K s)*((-Complex.I) • B)*time K (t-s) := by
  rw [variation,variationBetween,variationBetween,
    ←intervalIntegral.integral_sub (variation_integrable K B r t) (variation_integrable K B 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [zero_smul,add_zero,sub_mul]

 theorem variation_difference_window (K B : E →L[ℂ] E) (r T P Q t : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (within : |t| ≤ T)
    (base : ∀ s,|s| ≤ T → ‖time K s‖ ≤ P)
    (perturbed : ∀ s,|s| ≤ T → ‖time (K+r • B) s‖ ≤ Q) :
    ‖variationBetween K B r t-variation K B t‖ ≤ |r| *|t|^2*Q*‖B‖^2*P^2 := by
  rw [variation_difference_identity]
  have normB : ‖(-Complex.I) • B‖=‖B‖ := by rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
  have bound (s : ℝ) (hs : s∈Ι (0:ℝ) t) :
      ‖(time (K+r • B) s-time K s)*((-Complex.I) • B)*time K (t-s)‖ ≤ |r| *|t| *Q*‖B‖^2*P^2 := by
    have diff := parameter_difference_window K B r T P Q s hP hQ ((interval_times hs).1.trans within) base perturbed
    have diff' : ‖time (K+r • B) s-time K s‖ ≤ |r| *|t| *Q*‖B‖*P := by
      apply diff.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (interval_times hs).1 (abs_nonneg r)) hQ) (norm_nonneg B)) hP
    calc
      _ ≤ (‖time (K+r • B) s-time K s‖*‖(-Complex.I) • B‖)*‖time K (t-s)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ((|r| *|t| *Q*‖B‖*P)*‖B‖)*P := by
        rw [normB]
        exact mul_le_mul (mul_le_mul_of_nonneg_right diff' (norm_nonneg B))
          (base (t-s) ((interval_times hs).2.trans within)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact (intervalIntegral.norm_integral_le_of_norm_le_const bound).trans_eq (by rw [sub_zero];ring)

 theorem parameter_remainder_window (K B : E →L[ℂ] E) (r T P Q t : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (within : |t| ≤ T)
    (base : ∀ s,|s| ≤ T → ‖time K s‖ ≤ P)
    (perturbed : ∀ s,|s| ≤ T → ‖time (K+r • B) s‖ ≤ Q) :
    ‖time (K+r • B) t-time K t-r • variation K B t‖ ≤ (|t|^2*Q*‖B‖^2*P^2)*‖r‖^2 := by
  rw [parameter_difference,←smul_sub,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (variation_difference_window K B r T P Q t hP hQ within base perturbed)
    (abs_nonneg r)).trans_eq (by ring)

 theorem perturbed_time_window (C A B : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (r T t : ℝ)
    (_future : 0 ≤ T) (small : |r| ≤ 1) (within : |t| ≤ T) :
    ‖time (C+A+r • B) t‖ ≤ Real.exp ((‖A‖+‖B‖)*T) := by
  have shift : ‖r • B‖ ≤ ‖B‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right small (norm_nonneg B)).trans_eq (one_mul _)
  have normPert : ‖A+r • B‖ ≤ ‖A‖+‖B‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl shift)
  have bound := perturbed_time_bound C (A+r • B) symmetric t
  rw [←add_assoc] at bound
  exact bound.trans (Real.exp_le_exp.mpr (mul_le_mul normPert within (abs_nonneg t) (add_nonneg (norm_nonneg A) (norm_nonneg B))))

end Variation

open GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource CanonicalPhysicalLaplace
open GaussUnitaryHistory (Index)
abbrev Op := H →L[ℂ] H
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _

 theorem original_time_window (p : PhysicalMomentum) (F : Index) (cut : ℕ) (T t : ℝ)
    (future : 0 ≤ T) (within : |t| ≤ T) :
    ‖time (compression p F+cutoff cut) t‖ ≤ timeBound cut T := by
  apply (full_time_bound p F cut t).trans
  unfold timeBound
  rw [abs_of_nonneg future]
  apply Finset.sum_le_sum
  intro n _
  exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right within (norm_nonneg _)) n

 def remainderBound (cut : ℕ) (B : Op) (T : ℝ) : ℝ :=
  T^2*Real.exp ((‖cutoff cut‖+‖B‖)*T)*‖B‖^2*(timeBound cut T)^2

 theorem remainderBound_nonneg (cut : ℕ) (B : Op) (T : ℝ) : 0 ≤ remainderBound cut B T := by
  unfold remainderBound
  positivity

 theorem original_parameter_remainder (p : PhysicalMomentum) (F : Index) (cut : ℕ) (B : Op)
    (r T t : ℝ) (future : 0 ≤ T) (small : |r| ≤ 1) (within : |t| ≤ T) :
    ‖time (compression p F+cutoff cut+r • B) t-time (compression p F+cutoff cut) t-
      r • variation (compression p F+cutoff cut) B t‖ ≤ remainderBound cut B T*‖r‖^2 := by
  have source:=parameter_remainder_window (compression p F+cutoff cut) B r T
    (timeBound cut T) (Real.exp ((‖cutoff cut‖+‖B‖)*T)) t (timeBound_nonneg cut T) (Real.exp_pos _).le within
    (fun s hs=>original_time_window p F cut T s future hs)
    (fun s hs=>perturbed_time_window (compression p F) (cutoff cut) B (compression_selfAdjoint p F) r T s future small hs)
  apply source.trans
  unfold remainderBound
  have square : |t|^2 ≤ T^2 := pow_le_pow_left₀ (abs_nonneg t) within 2
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right square (Real.exp_pos _).le) (sq_nonneg ‖B‖)) (sq_nonneg _)) (sq_nonneg ‖r‖)

end LowEnergy.PreparationVacuumFieldPerturbation
