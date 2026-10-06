import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A real differentiable family of full matrices generates its actual
exponential parameter derivative as an ordered Duhamel integral. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
open MeasureTheory Set Filter Topology
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance flowReal : NormedAlgebra ℝ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance flowRational : NormedAlgebra ℚ (Matrix ι ι ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

def flow (A : Matrix ι ι ℂ) (time : ℝ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((time : ℂ) • A)

theorem flow_zero (A : Matrix ι ι ℂ) : flow A 0=1 := by
  simp [flow]

theorem flow_add (A : Matrix ι ι ℂ) (t s : ℝ) : flow A (t+s)=flow A t*flow A s := by
  simp only [flow,Complex.ofReal_add,add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left (t : ℂ)).smul_right (s : ℂ))

theorem flow_inverse (A : Matrix ι ι ℂ) (t : ℝ) : flow A (-t)*flow A t=1 := by
  rw [← flow_add,neg_add_cancel,flow_zero]

theorem flow_derivative (A : Matrix ι ι ℂ) (t : ℝ) :
    HasDerivAt (flow A) (flow A t*A) t := by
  convert! hasDerivAt_exp_smul_const A t using 1

theorem flow_commute (A : Matrix ι ι ℂ) (t : ℝ) : Commute (flow A t) A :=
  ((Commute.refl A).smul_left (t : ℂ)).exp_left

theorem flow_continuous (A : Matrix ι ι ℂ) : Continuous (flow A) :=
  continuous_iff_continuousAt.mpr fun t => (flow_derivative A t).continuousAt

theorem flow_joint_continuous : Continuous (fun pair : Matrix ι ι ℂ×ℝ => flow pair.1 pair.2) := by
  unfold flow
  exact NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_fst)

theorem transition_derivative (A B : Matrix ι ι ℂ) (t s : ℝ) :
    HasDerivAt (fun r => flow A (t-r)*flow B r)
      (flow A (t-s)*(B-A)*flow B s) s := by
  have first := (flow_derivative A (t-s)).scomp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have generated := first.mul (flow_derivative B s)
  convert! generated using 1
  simp only [Function.comp_apply,zero_sub,neg_one_smul,neg_mul,mul_sub,mul_assoc]
  rw [(flow_commute B s).eq]
  noncomm_ring

theorem flow_difference (A B : Matrix ι ι ℂ) (t : ℝ) :
    flow B t-flow A t=∫ s in (0 : ℝ)..t, flow A (t-s)*(B-A)*flow B s := by
  have continuousIntegrand : Continuous (fun s : ℝ => flow A (t-s)*(B-A)*flow B s) :=
    (((flow_continuous A).comp (continuous_const.sub continuous_id)).mul continuous_const).mul (flow_continuous B)
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => transition_derivative A B t s) (continuousIntegrand.intervalIntegrable 0 t)
  simpa only [sub_self,sub_zero,flow_zero,one_mul,mul_one] using generated.symm

def duhamel (A N : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  ∫ s in (0 : ℝ)..t, flow A (t-s)*N*flow A s

def dividedIntegral (A : Matrix ι ι ℂ) (t : ℝ) (pair : Matrix ι ι ℂ×Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ s in (0 : ℝ)..t, flow A (t-s)*pair.2*flow pair.1 s

theorem dividedIntegral_continuous (A : Matrix ι ι ℂ) (t : ℝ) : Continuous (dividedIntegral A t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (((flow_continuous A).comp (continuous_const.sub continuous_snd)).mul continuous_fst.snd).mul
    (flow_joint_continuous.comp (continuous_fst.fst.prodMk continuous_snd))

theorem flow_slope (family : ℝ → Matrix ι ι ℂ) (epsilon t : ℝ) :
    slope (fun e => flow (family e) t) 0 epsilon=
      dividedIntegral (family 0) t (family epsilon,slope family 0 epsilon) := by
  simp only [slope_def_module,sub_zero]
  rw [flow_difference,dividedIntegral,← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem flow_parameter (family : ℝ → Matrix ι ι ℂ) (direction : Matrix ι ι ℂ)
    (derivative : HasDerivAt family direction 0) (t : ℝ) :
    HasDerivAt (fun epsilon => flow (family epsilon) t) (duhamel (family 0) direction t) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have values : Tendsto family (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (family 0)) :=
    derivative.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have slopes := derivative.tendsto_slope
  have joined := values.prodMk_nhds slopes
  have generated := (dividedIntegral_continuous (family 0) t).continuousAt.tendsto.comp joined
  exact generated.congr' (Eventually.of_forall (fun epsilon => (flow_slope family epsilon t).symm))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
