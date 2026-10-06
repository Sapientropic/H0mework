import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylFourierAction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWeylOperator
open PreparationVacuumWeyl PreparationVacuumWeylDomain CanonicalPreparationSquareCutoff
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform RealInnerProductSpace

-- This analytic carrier weight is removed exactly in temperedAction_readback.
def polynomialWeight (xi : PhysicalMomentum) : ℂ := (1+inner ℝ xi xi : ℝ)

theorem polynomialWeight_temperate : Function.HasTemperateGrowth polynomialWeight := by
  have same : polynomialWeight=(fun xi : PhysicalMomentum => ((1+‖xi‖^2 : ℝ) : ℂ)) := by
    ext xi
    rw [polynomialWeight,real_inner_self_eq_norm_sq]
  rw [same]
  fun_prop

theorem polynomialWeight_norm (xi : PhysicalMomentum) : ‖polynomialWeight xi‖=1+‖xi‖^2 := by
  rw [polynomialWeight,real_inner_self_eq_norm_sq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ)<1+‖xi‖^2)]

theorem polynomialWeight_nonzero (xi : PhysicalMomentum) : polynomialWeight xi≠0 := by
  rw [polynomialWeight,real_inner_self_eq_norm_sq]
  exact Complex.ofReal_ne_zero.mpr (by positivity)

def dividedAction (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) : ℂ :=
  fourierAction f xi/polynomialWeight xi

def sourceOutputBound (f : 𝓢(PhysicalMomentum,ℂ)) : ℝ :=
  sourceKernelBound*Real.pi*(zerothMoment f+firstMoment f)

theorem dividedAction_bound (f : 𝓢(PhysicalMomentum,ℂ)) (xi : PhysicalMomentum) :
    ‖dividedAction f xi‖ ≤ sourceOutputBound f := by
  rw [dividedAction,norm_div,polynomialWeight_norm,div_le_iff₀ (by positivity)]
  apply (fourierAction_source_growth f xi).trans
  have radius : ‖xi‖≤1+‖xi‖^2 := by nlinarith [sq_nonneg (‖xi‖-1/2)]
  have zeroMoment := mul_le_mul_of_nonneg_right radius (zerothMoment_nonnegative f)
  have oneMoment : firstMoment f≤(1+‖xi‖^2)*firstMoment f := by
    exact le_mul_of_one_le_left (firstMoment_nonnegative f) (by nlinarith [sq_nonneg ‖xi‖])
  calc
    _ ≤ (sourceKernelBound*Real.pi)*
        ((1+‖xi‖^2)*zerothMoment f+(1+‖xi‖^2)*firstMoment f) :=
      mul_le_mul_of_nonneg_left (add_le_add zeroMoment oneMoment)
        (mul_nonneg sourceKernelBound_nonnegative Real.pi_pos.le)
    _ = sourceOutputBound f*(1+‖xi‖^2) := by rw [sourceOutputBound]; ring

theorem dividedAction_memLp (f : 𝓢(PhysicalMomentum,ℂ)) :
    MemLp (dividedAction f) ⊤ (volume : Measure PhysicalMomentum) :=
  memLp_top_of_bound
    ((fourierAction_measurable f).aestronglyMeasurable.mul
      polynomialWeight_temperate.1.continuous.measurable.inv.aestronglyMeasurable)
    (sourceOutputBound f) (Eventually.of_forall (dividedAction_bound f))

def dividedActionLp (f : 𝓢(PhysicalMomentum,ℂ)) : Lp (α := PhysicalMomentum) ℂ ⊤ volume :=
  (dividedAction_memLp f).toLp (dividedAction f)

def temperedAction (f : 𝓢(PhysicalMomentum,ℂ)) : 𝓢'(PhysicalMomentum,ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ polynomialWeight
    (Lp.toTemperedDistribution (dividedActionLp f))

theorem temperedAction_readback (f g : 𝓢(PhysicalMomentum,ℂ)) :
    temperedAction f g=∫ xi : PhysicalMomentum,g xi*fourierAction f xi := by
  rw [temperedAction,TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(dividedAction_memLp f).coeFn_toLp] with xi hxi
  change (SchwartzMap.smulLeftCLM ℂ polynomialWeight g) xi*(dividedActionLp f) xi=_
  rw [SchwartzMap.smulLeftCLM_apply_apply polynomialWeight_temperate]
  change polynomialWeight xi • g xi*((dividedAction_memLp f).toLp (dividedAction f)) xi=_
  rw [hxi]
  simp only [dividedAction,smul_eq_mul]
  field_simp [polynomialWeight_nonzero xi]

def actualVacuumTemperedAction (f : GaussDensityCore.ScalarTest) : 𝓢'(PhysicalMomentum,ℂ) :=
  temperedAction (sourceVacuumInputFrequency f)

theorem actualVacuumTemperedAction_readback (f : GaussDensityCore.ScalarTest)
    (g : 𝓢(PhysicalMomentum,ℂ)) :
    actualVacuumTemperedAction f g=
      ∫ xi : PhysicalMomentum,g xi*actualVacuumFactorAction f xi := temperedAction_readback _ _

end LowEnergy.PreparationVacuumWeylOperator
