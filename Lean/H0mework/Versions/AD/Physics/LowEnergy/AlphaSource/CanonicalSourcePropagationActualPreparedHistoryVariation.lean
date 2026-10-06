import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualHistoryEuler
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationLocalHistoryDerivative

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationNativeEulerHistory
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumPropagationPencil PreparationVacuumFieldPerturbation SourceFiniteUnitary PreparationVacuumPhysicalHalfAxis
open SourcePropagationTimeDependentFeedback LocalHistoryDerivative
open Filter Set Metric MeasureTheory
open scoped BigOperators Topology ContDiff NNReal Interval
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceHistoryEvolution jointGenerator physicalTime jointCurrent

private theorem constant_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (duration : ℝ) (positive : 0 < duration)
    (paid : ∀ t∈Ioo (-duration) duration, HasDerivAt f 0 t)
    (t : ℝ) (inside : t∈Ioo (-duration) duration) : f t=f 0 :=
  isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
    (fun z hz=>(paid z hz).differentiableAt.differentiableWithinAt)
    (fun z hz=>(paid z hz).deriv) inside (by constructor <;> linarith)

private theorem product_cancel {R : Type*} [Ring R] (W A U : R) :
    0=-(W*A)*U+W*(A*U) := by
  simp only [neg_mul,mul_assoc,neg_add_cancel]

private theorem base_primal_derivative (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    HasDerivAt (fun s : ℝ=>physicalTime p F s 0)
      (((-Complex.I) • jointGenerator p F 0 0)*physicalTime p F t 0) t := by
  have generated:=time_operator_derivative (jointGenerator p F 0 0) t
  rw [←((time_commutes _ _ (Commute.refl (jointGenerator p F 0 0)) t).smul_left (-Complex.I)).eq] at generated
  unfold physicalTime
  exact generated

private theorem base_dual_derivative (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    HasDerivAt (fun s : ℝ=>physicalTime p F (-s) 0)
      (-(physicalTime p F (-t) 0*((-Complex.I) • jointGenerator p F 0 0))) t := by
  have generated:=(time_operator_derivative (jointGenerator p F 0 0) (-t)).scomp t ((hasDerivAt_id t).neg)
  unfold physicalTime
  convert! generated using 1
  simp only [neg_one_smul]

private theorem base_inverse (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    physicalTime p F t 0*physicalTime p F (-t) 0=1 := by
  unfold physicalTime
  rw [←SourceFiniteUnitary.time_add,add_neg_cancel,SourceFiniteUnitary.time_zero]

private theorem base_initial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    physicalTime p F 0 0=1 := by
  unfold physicalTime
  exact SourceFiniteUnitary.time_zero _

/-- At zero amplitude the generated nonlinear family is the original physical-time source. -/
theorem historyPrimal_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ)
    (inside : t∈Ioo (-(sourceHistoryEvolution p F history smooth).duration)
      (sourceHistoryEvolution p F history smooth).duration) :
    historyPrimal p F history smooth 0 t=physicalTime p F t 0 := by
  let data:=sourceHistoryEvolution p F history smooth
  have small : |(0 : ℝ)|<data.radius := by simpa using data.radius_positive
  have derivative (s : ℝ) (hs : s∈Ioo (-data.duration) data.duration) :
      HasDerivAt (fun r=>physicalTime p F (-r) 0*historyPrimal p F history smooth 0 r) 0 s := by
    have original:=historyPrimal_derivative p F history smooth 0 s small hs
    simp only [zero_smul] at original
    convert! (base_dual_derivative p F s).mul original using 1
    exact product_cancel (R:=Op) (physicalTime p F (-s) 0)
      ((-Complex.I) • jointGenerator p F 0 0) (historyPrimal p F history smooth 0 s)
  have constant:=constant_interval _ data.duration data.duration_positive derivative t inside
  have initial:=historyPrimal_initial p F history smooth 0 small
  simp only [neg_zero,base_initial,initial,one_mul] at constant
  have value:=congrArg (fun x : Op=>physicalTime p F t 0*x) constant
  rw [←mul_assoc,base_inverse,one_mul,mul_one] at value
  exact value

theorem historyDual_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ)
    (inside : t∈Ioo (-(sourceHistoryEvolution p F history smooth).duration)
      (sourceHistoryEvolution p F history smooth).duration) :
    historyDual p F history smooth 0 t=physicalTime p F (-t) 0 := by
  let data:=sourceHistoryEvolution p F history smooth
  have small : |(0 : ℝ)|<data.radius := by simpa using data.radius_positive
  have derivative (s : ℝ) (hs : s∈Ioo (-data.duration) data.duration) :
      HasDerivAt (fun r=>historyDual p F history smooth 0 r*physicalTime p F r 0) 0 s := by
    have original:=historyDual_derivative p F history smooth 0 s small hs
    simp only [zero_smul] at original
    convert! original.mul (base_primal_derivative p F s) using 1
    exact product_cancel (R:=Op) (historyDual p F history smooth 0 s)
      ((-Complex.I) • jointGenerator p F 0 0) (physicalTime p F s 0)
  have constant:=constant_interval _ data.duration data.duration_positive derivative t inside
  have initial:=historyDual_initial p F history smooth 0 small
  simp only [base_initial,initial,one_mul] at constant
  have value:=congrArg (fun x : Op=>x*physicalTime p F (-t) 0) constant
  rw [mul_assoc,base_inverse,mul_one,one_mul] at value
  exact value

private theorem curve_generator_budget {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : E → D) (history : ℝ → E) (sourceSmooth : ContDiffAt ℝ 1 f 0)
    (historySmooth : ContDiffAt ℝ 1 history 0) :
    ∃ timeRadius > (0 : ℝ), ∃ amplitudeRadius > (0 : ℝ), ∃ price ≥ (0 : ℝ),
      (ContinuousOn history (Ioo (-timeRadius) timeRadius)) ∧
      (∀ amplitude : ℝ, |amplitude|<amplitudeRadius →
        ContinuousOn (fun t=>f (amplitude • history t)) (Ioo (-timeRadius) timeRadius)) ∧
      ∀ amplitude : ℝ, |amplitude|<amplitudeRadius → ∀ t∈Ioo (-timeRadius) timeRadius,
        ‖amplitude⁻¹ • (f (amplitude • history t)-f 0)‖≤price := by
  obtain ⟨K,domain,near,lipschitz⟩:=sourceSmooth.exists_lipschitzOnWith
  obtain ⟨sourceRadius,positiveSource,sourceBall⟩:=Metric.mem_nhds_iff.mp near
  obtain ⟨timeDomain,timeNear,timeSmooth⟩:=historySmooth.contDiffOn (m:=1) le_rfl (by simp)
  let H:=‖history 0‖+1
  have positiveH : 0<H := by dsimp [H];positivity
  have nearBound : ∀ᶠ t in 𝓝 (0 : ℝ), ‖history t‖<H :=
    historySmooth.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [H];linarith))
  have together : ∀ᶠ t in 𝓝 (0 : ℝ), t∈timeDomain ∧ ‖history t‖<H :=
    Filter.Eventually.and timeNear nearBound
  obtain ⟨timeRadius,positiveTime,timeBall⟩:=Metric.eventually_nhds_iff.mp together
  let amplitudeRadius:=sourceRadius/H
  have positiveAmplitude : 0<amplitudeRadius := div_pos positiveSource positiveH
  have validTime (t : ℝ) (ht : t∈Ioo (-timeRadius) timeRadius) : t∈timeDomain ∧ ‖history t‖<H :=
    timeBall (by simpa only [Real.dist_eq,sub_zero,abs_lt,Set.mem_Ioo] using ht)
  have validField (amplitude : ℝ) (ha : |amplitude|<amplitudeRadius)
      (t : ℝ) (ht : t∈Ioo (-timeRadius) timeRadius) : amplitude • history t∈domain := by
    apply sourceBall
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs]
    have h : |amplitude| * H<sourceRadius := (lt_div_iff₀ positiveH).mp ha
    exact (mul_le_mul_of_nonneg_left (validTime t ht).2.le (abs_nonneg amplitude)).trans_lt h
  have historyContinuous : ContinuousOn history (Ioo (-timeRadius) timeRadius) :=
    timeSmooth.continuousOn.mono (fun t ht=>(validTime t ht).1)
  refine ⟨timeRadius,positiveTime,amplitudeRadius,positiveAmplitude,K*H,by positivity,historyContinuous,?_,?_⟩
  · intro amplitude small
    exact lipschitz.continuousOn.comp (continuousOn_const.smul historyContinuous)
      (validField amplitude small)
  · intro amplitude small t inside
    have zeroMember : (0 : E)∈domain := sourceBall (by simpa only [mem_ball_zero_iff,norm_zero] using positiveSource)
    have sourceBound:=lipschitz.norm_sub_le (validField amplitude small t inside) zeroMember
    rw [sub_zero,norm_smul,Real.norm_eq_abs] at sourceBound
    by_cases zero : amplitude=0
    · simp only [zero,inv_zero,zero_smul,norm_zero]
      positivity
    · calc
        ‖amplitude⁻¹ • (f (amplitude • history t)-f 0)‖=
          |amplitude|⁻¹ * ‖f (amplitude • history t)-f 0‖ := by
            rw [norm_smul,Real.norm_eq_abs,abs_inv]
        _≤|amplitude|⁻¹ * (K*(|amplitude| * ‖history t‖)) :=
          mul_le_mul_of_nonneg_left sourceBound (inv_nonneg.mpr (abs_nonneg amplitude))
        _=K*‖history t‖ := by field_simp
        _≤K*H := mul_le_mul_of_nonneg_left (validTime t inside).2.le K.coe_nonneg

def historyGenerator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (amplitude t : ℝ) : Op :=
  (-Complex.I) • jointGenerator p F 0 (amplitude • history t)

def historyGeneratorVariation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (t : ℝ) : Op :=
  (-Complex.I) • jointCurrent p F 0 0 (history t)

theorem historyGenerator_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (t : ℝ) :
    HasDerivAt (fun amplitude=>historyGenerator p F history amplitude t)
      (historyGeneratorVariation p F history t) 0 :=
  physicalDrive_generated p F history t

/-- Every bound in the parameter derivative is returned by the same source and history. -/
theorem historyGenerator_budget (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) :
    ∃ timeRadius > (0 : ℝ), ∃ amplitudeRadius > (0 : ℝ), ∃ price ≥ (0 : ℝ),
      ContinuousOn history (Ioo (-timeRadius) timeRadius) ∧
      (∀ amplitude : ℝ, |amplitude|<amplitudeRadius →
        ContinuousOn (historyGenerator p F history amplitude) (Ioo (-timeRadius) timeRadius)) ∧
      ∀ amplitude : ℝ, |amplitude|<amplitudeRadius → ∀ t∈Ioo (-timeRadius) timeRadius,
        ‖amplitude⁻¹ • (historyGenerator p F history amplitude t-historyGenerator p F history 0 t)‖≤price := by
  have actual := curve_generator_budget (fun h : Field289=>(-Complex.I) • jointGenerator p F 0 h)
    history (((jointGenerator_C2 p F 0).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).const_smul (-Complex.I)) smooth
  have functionValue (amplitude : ℝ) : historyGenerator p F history amplitude =
      (fun t=>(-Complex.I) • jointGenerator p F 0 (amplitude • history t)) := rfl
  simp_rw [functionValue]
  simpa only [zero_smul] using actual

theorem historyGenerator_secant (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (t : ℝ) :
    Tendsto (fun amplitude : ℝ=>amplitude⁻¹ •
      (historyGenerator p F history amplitude t-historyGenerator p F history 0 t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (historyGeneratorVariation p F history t)) := by
  have generated:=hasDerivAt_iff_tendsto_slope_zero.mp (historyGenerator_generated p F history t)
  simpa only [zero_add] using generated

theorem historyPrimal_parameter_continuous (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ)
    (inside : t∈Ioo (-(sourceHistoryEvolution p F history smooth).duration)
      (sourceHistoryEvolution p F history smooth).duration) :
    Tendsto (fun amplitude=>historyPrimal p F history smooth amplitude t) (𝓝 (0 : ℝ))
      (𝓝 (historyPrimal p F history smooth 0 t)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have small : ∀ᶠ amplitude in 𝓝 (0 : ℝ), |amplitude|<(sourceHistoryEvolution p F history smooth).radius :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using
      (sourceHistoryEvolution p F history smooth).radius_positive))
  have bound : ∀ᶠ amplitude in 𝓝 (0 : ℝ),
      dist (historyPrimal p F history smooth amplitude t) (historyPrimal p F history smooth 0 t) ≤
        (sourceHistoryEvolution p F history smooth).price * |amplitude| := small.mono (fun a ha=>by
    simpa only [dist_eq_norm] using historyPrimal_difference_bound p F history smooth a t ha inside)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _=>dist_nonneg)) bound
  simpa only [abs_zero,mul_zero] using
    (tendsto_const_nhds.mul (continuous_abs.tendsto (0 : ℝ)))

theorem historyDual_parameter_continuous (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ)
    (inside : t∈Ioo (-(sourceHistoryEvolution p F history smooth).duration)
      (sourceHistoryEvolution p F history smooth).duration) :
    Tendsto (fun amplitude=>historyDual p F history smooth amplitude t) (𝓝 (0 : ℝ))
      (𝓝 (historyDual p F history smooth 0 t)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have small : ∀ᶠ amplitude in 𝓝 (0 : ℝ), |amplitude|<(sourceHistoryEvolution p F history smooth).radius :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using
      (sourceHistoryEvolution p F history smooth).radius_positive))
  have bound : ∀ᶠ amplitude in 𝓝 (0 : ℝ),
      dist (historyDual p F history smooth amplitude t) (historyDual p F history smooth 0 t) ≤
        (sourceHistoryEvolution p F history smooth).price * |amplitude| := small.mono (fun a ha=>by
    simpa only [dist_eq_norm] using historyDual_difference_bound p F history smooth a t ha inside)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _=>dist_nonneg)) bound
  simpa only [abs_zero,mul_zero] using
    (tendsto_const_nhds.mul (continuous_abs.tendsto (0 : ℝ)))

structure HistoryParameterWindow (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) where
  duration : ℝ
  duration_positive : 0<duration
  radius : ℝ
  radius_positive : 0<radius
  price : ℝ
  price_nonnegative : 0≤price
  time_inside : Ioo (-duration) duration ⊆
    Ioo (-(sourceHistoryEvolution p F history smooth).duration) (sourceHistoryEvolution p F history smooth).duration
  amplitude_inside : ∀ a : ℝ, |a|<radius → |a|<(sourceHistoryEvolution p F history smooth).radius
  generator_continuous : ∀ a : ℝ, |a|<radius →
    ContinuousOn (historyGenerator p F history a) (Ioo (-duration) duration)
  generator_bound : ∀ a : ℝ, |a|<radius → ∀ t∈Ioo (-duration) duration,
    ‖a⁻¹ • (historyGenerator p F history a t-historyGenerator p F history 0 t)‖≤price

theorem historyParameterWindow_nonempty (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) :
    Nonempty (HistoryParameterWindow p F history smooth) := by
  obtain ⟨T,positiveT,R,positiveR,price,nonnegative,_,continuousGenerator,boundGenerator⟩:=
    historyGenerator_budget p F history smooth
  let data:=sourceHistoryEvolution p F history smooth
  let duration:=min T data.duration
  let radius:=min R data.radius
  have positiveDuration : 0<duration := lt_min positiveT data.duration_positive
  have positiveRadius : 0<radius := lt_min positiveR data.radius_positive
  have beforeSource : Ioo (-duration) duration ⊆ Ioo (-data.duration) data.duration := by
    intro t ht
    constructor <;> dsimp [duration] at ht ⊢ <;> linarith [min_le_right T data.duration,ht.1,ht.2]
  have beforeBudget : Ioo (-duration) duration ⊆ Ioo (-T) T := by
    intro t ht
    constructor <;> dsimp [duration] at ht ⊢ <;> linarith [min_le_left T data.duration,ht.1,ht.2]
  refine ⟨⟨duration,positiveDuration,radius,positiveRadius,price,nonnegative,beforeSource,
    (fun a ha=>ha.trans_le (min_le_right _ _)),?_,?_⟩⟩
  · intro a small
    exact (continuousGenerator a (small.trans_le (min_le_left _ _))).mono beforeBudget
  · intro a small t inside
    exact boundGenerator a (small.trans_le (min_le_left _ _)) t (beforeBudget inside)

noncomputable def sourceHistoryWindow (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) :
    HistoryParameterWindow p F history smooth :=
  Classical.choice (historyParameterWindow_nonempty p F history smooth)

attribute [local irreducible] sourceHistoryWindow

private theorem window_time_interval (duration t : ℝ) (positive : 0<duration)
    (nonnegative : 0≤t) (inside : t<duration) : uIcc (0 : ℝ) t ⊆ Ioo (-duration) duration := by
  rw [uIcc_of_le nonnegative]
  intro s hs
  constructor <;> linarith [hs.1,hs.2]

private theorem window_time_bound (t s : ℝ) (nonnegative : 0≤t) (inside : s∈uIcc (0 : ℝ) t) : |s|≤t := by
  rw [uIcc_of_le nonnegative] at inside
  rw [abs_of_nonneg inside.1]
  exact inside.2

def generatedPrimalVariation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (t : ℝ) : Op :=
  physicalTime p F t 0*∫ s in (0 : ℝ)..t,
    physicalTime p F (-s) 0*historyGeneratorVariation p F history s*physicalTime p F s 0

theorem historyPrimal_parameter_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<(sourceHistoryWindow p F history smooth).duration) :
    HasDerivAt (fun amplitude=>historyPrimal p F history smooth amplitude t)
      (generatedPrimalVariation p F history t) 0 := by
  let data:=sourceHistoryEvolution p F history smooth
  let window:=sourceHistoryWindow p F history smooth
  have timeInside:=window_time_interval window.duration t window.duration_positive nonnegative inside
  have nearAmplitude : ∀ᶠ a in 𝓝 (0 : ℝ), |a|<window.radius :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using window.radius_positive))
  have hA : ∀ᶠ a in 𝓝 (0 : ℝ), ContinuousOn (historyGenerator p F history a) (uIcc 0 t) :=
    nearAmplitude.mono (fun a ha=>(window.generator_continuous a ha).mono timeInside)
  have hU : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t,
      HasDerivAt (historyPrimal p F history smooth a)
        (historyGenerator p F history a s*historyPrimal p F history smooth a s) s := by
    filter_upwards [nearAmplitude] with a ha
    intro s hs
    exact historyPrimal_derivative p F history smooth a s (window.amplitude_inside a ha)
      (window.time_inside (timeInside hs))
  have hU0 : ∀ᶠ a in 𝓝 (0 : ℝ), historyPrimal p F history smooth a 0=1 :=
    nearAmplitude.mono (fun a ha=>historyPrimal_initial p F history smooth a (window.amplitude_inside a ha))
  have hUlim (s : ℝ) (hs : s∈uIcc 0 t) :=
    historyPrimal_parameter_continuous p F history smooth s (window.time_inside (timeInside hs))
  have hsec (s : ℝ) (_hs : s∈uIcc 0 t) := historyGenerator_secant p F history s
  have hInv : historyPrimal p F history smooth 0 t*physicalTime p F (-t) 0=1 := by
    rw [historyPrimal_zero p F history smooth t (window.time_inside (timeInside (by simp))),base_inverse]
  let M:=actualGrowth p F t
  have positiveM : 0≤M:=actualGrowth_nonnegative p F t nonnegative
  have hW : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t, ‖physicalTime p F (-s) 0‖≤M :=
    Filter.Eventually.of_forall (fun _ s hs=>actual_time_window p F t (-s)
      (by simpa only [abs_neg] using window_time_bound t s nonnegative hs))
  have hQ : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t,
      ‖a⁻¹ • (historyGenerator p F history a s-historyGenerator p F history 0 s)‖≤window.price :=
    nearAmplitude.mono (fun a ha s hs=>window.generator_bound a ha s (timeInside hs))
  have hUB : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t,
      ‖historyPrimal p F history smooth a s‖≤M+data.price*window.radius := by
    filter_upwards [nearAmplitude] with a ha
    intro s hs
    have difference:=historyPrimal_difference_bound p F history smooth a s
      (window.amplitude_inside a ha) (window.time_inside (timeInside hs))
    have base:=historyPrimal_zero p F history smooth s (window.time_inside (timeInside hs))
    calc
      ‖historyPrimal p F history smooth a s‖≤
        ‖historyPrimal p F history smooth a s-historyPrimal p F history smooth 0 s‖+
          ‖historyPrimal p F history smooth 0 s‖ := norm_le_norm_sub_add _ _
      _≤data.price*|a|+M := add_le_add difference (by rw [base];exact actual_time_window p F t s (window_time_bound t s nonnegative hs))
      _≤M+data.price*window.radius := by nlinarith [data.price.coe_nonneg]
  have majorant:=product_majorant positiveM window.price_nonnegative
    (add_nonneg positiveM (mul_nonneg data.price.coe_nonneg window.radius_positive.le)) hW hQ hUB
  have baseValue (s : ℝ) : historyGenerator p F history 0 s=(-Complex.I) • jointGenerator p F 0 0 := by
    simp only [historyGenerator,zero_smul]
  simp_rw [baseValue] at hsec majorant
  have actual:=parameter_hasDerivAt_left (D:=historyGeneratorVariation p F history) hA hU
    (fun s _=>base_dual_derivative p F s) hU0 (by simpa only [neg_zero] using base_initial p F) hInv hUlim hsec majorant
  convert! actual using 1
  rw [generatedPrimalVariation,historyPrimal_zero p F history smooth t
    (window.time_inside (timeInside (by simp)))]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [historyPrimal_zero p F history smooth s (window.time_inside (timeInside hs))]

def generatedDualVariation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (t : ℝ) : Op :=
  -(∫ s in (0 : ℝ)..t,
    physicalTime p F (-s) 0*historyGeneratorVariation p F history s*physicalTime p F s 0)*physicalTime p F (-t) 0

theorem historyDual_parameter_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (history : ℝ → Field289) (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ)
    (nonnegative : 0≤t) (inside : t<(sourceHistoryWindow p F history smooth).duration) :
    HasDerivAt (fun amplitude=>historyDual p F history smooth amplitude t)
      (generatedDualVariation p F history t) 0 := by
  let data:=sourceHistoryEvolution p F history smooth
  let window:=sourceHistoryWindow p F history smooth
  have timeInside:=window_time_interval window.duration t window.duration_positive nonnegative inside
  have nearAmplitude : ∀ᶠ a in 𝓝 (0 : ℝ), |a|<window.radius :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by simpa using window.radius_positive))
  have hA : ∀ᶠ a in 𝓝 (0 : ℝ), ContinuousOn (historyGenerator p F history a) (uIcc 0 t) :=
    nearAmplitude.mono (fun a ha=>(window.generator_continuous a ha).mono timeInside)
  have hV : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t,
      HasDerivAt (historyDual p F history smooth a)
        (-(historyDual p F history smooth a s*historyGenerator p F history a s)) s := by
    filter_upwards [nearAmplitude] with a ha
    intro s hs
    convert! historyDual_derivative p F history smooth a s (window.amplitude_inside a ha)
      (window.time_inside (timeInside hs)) using 1
  have hV0 : ∀ᶠ a in 𝓝 (0 : ℝ), historyDual p F history smooth a 0=1 :=
    nearAmplitude.mono (fun a ha=>historyDual_initial p F history smooth a (window.amplitude_inside a ha))
  have hVlim (s : ℝ) (hs : s∈uIcc 0 t) :=
    historyDual_parameter_continuous p F history smooth s (window.time_inside (timeInside hs))
  have hsec (s : ℝ) (_hs : s∈uIcc 0 t) := historyGenerator_secant p F history s
  have hInv : physicalTime p F t 0*historyDual p F history smooth 0 t=1 := by
    rw [historyDual_zero p F history smooth t (window.time_inside (timeInside (by simp))),base_inverse]
  let M:=actualGrowth p F t
  have positiveM : 0≤M:=actualGrowth_nonnegative p F t nonnegative
  have hX : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t, ‖physicalTime p F s 0‖≤M :=
    Filter.Eventually.of_forall (fun _ s hs=>actual_time_window p F t s (window_time_bound t s nonnegative hs))
  have hQ : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t,
      ‖a⁻¹ • (historyGenerator p F history a s-historyGenerator p F history 0 s)‖≤window.price :=
    nearAmplitude.mono (fun a ha s hs=>window.generator_bound a ha s (timeInside hs))
  have hVB : ∀ᶠ a in 𝓝 (0 : ℝ), ∀ s∈uIcc 0 t,
      ‖historyDual p F history smooth a s‖≤M+data.price*window.radius := by
    filter_upwards [nearAmplitude] with a ha
    intro s hs
    have difference:=historyDual_difference_bound p F history smooth a s
      (window.amplitude_inside a ha) (window.time_inside (timeInside hs))
    have base:=historyDual_zero p F history smooth s (window.time_inside (timeInside hs))
    calc
      ‖historyDual p F history smooth a s‖≤
        ‖historyDual p F history smooth a s-historyDual p F history smooth 0 s‖+
          ‖historyDual p F history smooth 0 s‖ := norm_le_norm_sub_add _ _
      _≤data.price*|a|+M := add_le_add difference (by
        rw [base]
        exact actual_time_window p F t (-s)
          (by simpa only [abs_neg] using window_time_bound t s nonnegative hs))
      _≤M+data.price*window.radius := by nlinarith [data.price.coe_nonneg]
  have majorant:=product_majorant (add_nonneg positiveM (mul_nonneg data.price.coe_nonneg window.radius_positive.le))
    window.price_nonnegative positiveM hVB hQ hX
  have baseValue (s : ℝ) : historyGenerator p F history 0 s=(-Complex.I) • jointGenerator p F 0 0 := by
    simp only [historyGenerator,zero_smul]
  simp_rw [baseValue] at hsec majorant
  have actual:=parameter_hasDerivAt_right (D:=historyGeneratorVariation p F history) hA hV
    (fun s _=>base_primal_derivative p F s) hV0 (base_initial p F) hInv hVlim hsec majorant
  convert! actual using 1
  rw [generatedDualVariation,historyDual_zero p F history smooth t
    (window.time_inside (timeInside (by simp)))]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [historyDual_zero p F history smooth s (window.time_inside (timeInside hs))]

theorem generatedPrimalVariation_ordered (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) :
    generatedPrimalVariation q.p q.F history t=orderedPrimal q history t := by
  unfold generatedPrimalVariation orderedPrimal historyGeneratorVariation physicalTime rightCurrent
  rfl

theorem generatedDualVariation_ordered (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) :
    generatedDualVariation (q.p+q.k) q.F history t=orderedDual q history t := by
  unfold generatedDualVariation orderedDual historyGeneratorVariation physicalTime leftCurrent
  change -(∫ s in (0 : ℝ)..t,
    time (jointGenerator (q.p+q.k) q.F 0 0) (-s)*
      ((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0 (history s))*
      time (jointGenerator (q.p+q.k) q.F 0 0) s)*time (jointGenerator (q.p+q.k) q.F 0 0) (-t)=
    (∫ s in (0 : ℝ)..t,
      time (jointGenerator (q.p+q.k) q.F 0 0) (-s)*
        (-((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0 (history s)))*
        time (jointGenerator (q.p+q.k) q.F 0 0) s)*time (jointGenerator (q.p+q.k) q.F 0 0) (-t)
  simp only [mul_neg,neg_mul,intervalIntegral.integral_neg]

theorem actualPrimal_ordered_direction (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<(sourceHistoryWindow q.p q.F history smooth).duration) :
    HasDerivAt (fun a=>historyPrimal q.p q.F history smooth a t) (orderedPrimal q history t) 0 := by
  rw [←generatedPrimalVariation_ordered]
  exact historyPrimal_parameter_generated q.p q.F history smooth t nonnegative inside

theorem actualDual_ordered_direction (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (smooth : ContDiffAt ℝ 1 history 0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<(sourceHistoryWindow (q.p+q.k) q.F history smooth).duration) :
    HasDerivAt (fun a=>historyDual (q.p+q.k) q.F history smooth a t) (orderedDual q history t) 0 := by
  rw [←generatedDualVariation_ordered]
  exact historyDual_parameter_generated (q.p+q.k) q.F history smooth t nonnegative inside

end LowEnergy.SourcePropagationNativeEulerHistory
