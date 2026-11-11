import H0mework.Versions.V2.Arithmetic.RieszResponse.ResponseRead
import H0mework.Arithmetic.RieszResponse.Integration

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal

/-- The homogeneous weak Euler source generates the entire original dilation orbit. -/
theorem homogeneous_dilation_action (coefficient : ℂ) (value : BurnolL2)
 (homogeneous : GapEuler.euler (value : TemperedDistribution ℝ ℂ) +
  coefficient • (value : TemperedDistribution ℝ ℂ)=0) (shift : ℝ) :
 burnolMultiplicativeDilation shift value=Complex.exp (-coefficient*(shift:ℂ)) • value := by
 apply LinearMap.ker_eq_bot.mp
  (Lp.ker_toTemperedDistributionCLM_eq_bot (F:=ℂ) (μ:=volume))
 ext test
 let read : ℝ→ℂ := fun h => (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test
 have derivative (h : ℝ) : HasDerivAt read ((0:ℂ)-coefficient*read h) h := by
  have actual := Dilation.original_weak_derivative value test h
  have evaluated := congrArg (fun source : TemperedDistribution ℝ ℂ =>
   source (coPoissonSchwartzEnergyTranslation (-h) test)) homogeneous
  simp only [add_apply,smul_apply,smul_eq_mul,zero_apply] at evaluated
  rw [← OriginalRieszFiniteResponse.original_read value test h] at evaluated
  have eulerValue : GapEuler.euler
   (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test=
   (0:ℂ)-coefficient*read h := by
   rw [OriginalRieszFiniteResponse.original_euler_action]
   dsimp only [read]
   linear_combination evaluated
  rw [eulerValue] at actual
  exact actual
 have finite := _root_.OriginalRieszFiniteResponse.Integration.finite_response read
  (fun _=>0) coefficient derivative continuous_const shift
 have base : read 0=(value : TemperedDistribution ℝ ℂ) test := by
  dsimp only [read]
  rw [OriginalRieszFiniteResponse.original_read,neg_zero,coPoissonSchwartzEnergyTranslation_zero]
 have generated : read shift=Complex.exp (-coefficient*(shift:ℂ))*
  (value : TemperedDistribution ℝ ℂ) test := by
  simpa only [mul_zero,intervalIntegral.integral_zero,add_zero,base] using finite
 change read shift=(Lp.toTemperedDistributionCLM ℂ volume 2
  (Complex.exp (-coefficient*(shift:ℂ)) • value)) test
 rw [map_smul]
 exact generated

/-- Positive real Euler parameter is incompatible with a nonzero L2 homogeneous source. -/
theorem homogeneous_L2_unique (coefficient : ℂ) (positive : 0<coefficient.re)
 (value : BurnolL2)
 (homogeneous : GapEuler.euler (value : TemperedDistribution ℝ ℂ) +
  coefficient • (value : TemperedDistribution ℝ ℂ)=0) : value=0 := by
 have generated := homogeneous_dilation_action coefficient value homogeneous 1
 have norms := congrArg norm generated
 rw [(burnolMultiplicativeDilation 1).norm_map,norm_smul,Complex.norm_exp] at norms
 simp only [Complex.ofReal_one,mul_one,Complex.neg_re] at norms
 by_contra nonzero
 have positiveNorm : 0<‖value‖ := norm_pos_iff.mpr nonzero
 have decay : Real.exp (-coefficient.re)<1 := Real.exp_lt_one_iff.mpr (by linarith)
 have smaller : Real.exp (-coefficient.re)*‖value‖<‖value‖ := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right decay positiveNorm
 linarith

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
