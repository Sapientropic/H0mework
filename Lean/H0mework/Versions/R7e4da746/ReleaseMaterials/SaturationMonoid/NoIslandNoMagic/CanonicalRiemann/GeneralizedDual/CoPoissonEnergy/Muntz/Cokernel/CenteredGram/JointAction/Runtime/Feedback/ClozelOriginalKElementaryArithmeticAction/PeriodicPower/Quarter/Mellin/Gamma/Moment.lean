import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularCounting
import H0mework.Arithmetic.BurnolMellin.GaussianSuperpositionKernel

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Moment
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology InnerProductSpace

def gaussianPower (s:ℂ) (x:ℝ):ℂ :=
  (x:ℂ)^(s-1)*burnolGaussianRaw 1 x

private def gammaKernel (s:ℂ) (u:ℝ):ℂ :=
  (u:ℂ)^(s/2-1)*Complex.exp (-((Real.pi:ℂ)*(u:ℂ)))

private theorem square_pull (s:ℂ) (x:ℝ) (positive:0<x):
    (2*x) • gammaKernel s (x^2)=2*gaussianPower s x:=by
  have power:((x^2:ℝ):ℂ)^(s/2-1)=(x:ℂ)^(s-2):=by
    rw [show ((x^2:ℝ):ℂ)=((x^(2:ℝ):ℝ):ℂ) by rw [Real.rpow_two],
      ←Complex.cpow_mul_ofReal_nonneg positive.le 2]
    congr 1
    norm_num
    ring
  have next:(x:ℂ)*(x:ℂ)^(s-2)=(x:ℂ)^(s-1):=by
    rw [show s-1=(s-2)+1 by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
    ring
  simp only [gammaKernel,Complex.real_smul,power,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  calc
    2*(x:ℂ)*((x:ℂ)^(s-2)*Complex.exp (-((Real.pi:ℂ)*((x^2:ℝ):ℂ))))=
        2*((x:ℂ)*(x:ℂ)^(s-2))*Complex.exp (-((Real.pi:ℂ)*((x^2:ℝ):ℂ))) := by ring
    _=2*gaussianPower s x:=by
      rw [next]
      simp only [gaussianPower,burnolGaussianRaw,mul_one,Complex.ofReal_mul,
        mul_assoc]

theorem actual_gaussian_power_integrable (s:ℂ) (positive:0<s.re):
    IntegrableOn (gaussianPower s) (Ioi 0):=by
  have kernel:IntegrableOn (gammaKernel s) (Ioi 0):=
    burnolGaussianMellinScaleKernel_integrableOn s positive Real.pi_pos
  have square:IntegrableOn (fun x:ℝ=>(|(2:ℝ)| * x^((2:ℝ)-1)) • gammaKernel s (x^(2:ℝ)))
      (Ioi 0):=(integrableOn_Ioi_comp_rpow_iff (gammaKernel s) (by norm_num : (2:ℝ)≠0)).mpr kernel
  have twice:IntegrableOn (fun x:ℝ=>(2:ℂ)*gaussianPower s x) (Ioi 0):=by
    apply square.congr_fun _ measurableSet_Ioi
    intro x positiveX
    simpa only [abs_of_pos (by norm_num : (0:ℝ)<2),show (2:ℝ)-1=1 by norm_num,
      Real.rpow_one,Real.rpow_two] using square_pull s x positiveX
  have normalized:=twice.const_mul (1/2:ℂ)
  apply normalized.congr
  filter_upwards with x
  change (1/2:ℂ)*(2*gaussianPower s x)=gaussianPower s x
  ring

/-- Both reciprocal power readings use the original Gaussian and its actual Gamma normalization. -/
theorem actual_gaussian_power_integral (s:ℂ) (positive:0<s.re):
    (∫x:ℝ in Ioi 0,gaussianPower s x)=Gammaℝ s/2:=by
  have kernel:(∫u:ℝ in Ioi 0,gammaKernel s u)=Gammaℝ s:=by
    have source:=gammaReal_mul_positive_cpow_neg_eq_gaussianSuperposition s positive (by norm_num : (0:ℝ)<1)
    simpa only [Complex.ofReal_one,one_cpow,mul_one,one_pow,gammaKernel] using source.symm
  have square:=integral_comp_rpow_Ioi (gammaKernel s) (by norm_num : (2:ℝ)≠0)
  rw [kernel] at square
  have converted:(∫x:ℝ in Ioi 0,(|(2:ℝ)| * x^((2:ℝ)-1)) • gammaKernel s (x^(2:ℝ)))=
      2*(∫x:ℝ in Ioi 0,gaussianPower s x):=by
    rw [←integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x positiveX=>by
      simpa only [abs_of_pos (by norm_num : (0:ℝ)<2),show (2:ℝ)-1=1 by norm_num,
        Real.rpow_one,Real.rpow_two]
        using square_pull s x positiveX)
  rw [converted] at square
  linear_combination square/2

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Moment
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
