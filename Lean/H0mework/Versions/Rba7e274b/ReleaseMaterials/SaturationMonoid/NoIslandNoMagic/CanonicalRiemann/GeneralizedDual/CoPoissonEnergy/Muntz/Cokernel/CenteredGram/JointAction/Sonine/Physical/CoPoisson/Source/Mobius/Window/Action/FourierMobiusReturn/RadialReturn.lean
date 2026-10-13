import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.RawReturn
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology

theorem exp_Iic_substitution (g : ℝ→ℂ) :
    (∫ u : ℝ in Iic 0,(Real.exp u:ℂ)*g (Real.exp u))=∫ y : ℝ in Ioc 0 1,g y := by
  have source := integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Iic (a:=(0:ℝ))) (fun u _=>(Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ eq=>Real.exp_injective eq) g
  have image : Real.exp '' Iic 0=Ioc (0:ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨u,inside,rfl⟩
      exact ⟨Real.exp_pos _,by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr inside⟩
    · intro inside
      refine ⟨Real.log y,Real.log_nonpos inside.1.le inside.2,Real.exp_log inside.1⟩
  rw [image] at source
  simpa only [abs_of_pos (Real.exp_pos _),Complex.real_smul] using source.symm

 theorem original_R_radial_time (coordinate : BurnolCompletedMellinCoordinate) (value : ℝ→ℂ)
    (x : ℝ) (positive : 0<x) :
    (-(∫ tau : ℝ in Ioi 0,Complex.exp ((-star coordinate.value/2)*(tau:ℂ))*value (Real.exp (-tau/2)*x)))=
      -(2:ℂ)*(x:ℂ)^(-star coordinate.value)*∫ t : ℝ in Ioc 0 x,(t:ℂ)^(star coordinate.value-1)*value t := by
  let radial : ℝ→ℂ := fun u=>(u:ℂ)^(star coordinate.value-1)*value (u*x)
  have half := integral_comp_mul_left_Ioi
    (fun tau : ℝ=>Complex.exp ((-star coordinate.value/2)*(tau:ℂ))*value (Real.exp (-tau/2)*x))
    0 (by norm_num : (0:ℝ)<2)
  have reflected := integral_comp_neg_Ioi (0:ℝ)
    (fun u : ℝ=>Complex.exp ((star coordinate.value)*(u:ℂ))*value (Real.exp u*x))
  have expRead : ∀ u : ℝ,(Real.exp u:ℂ)*radial (Real.exp u)=
      Complex.exp (star coordinate.value*(u:ℂ))*value (Real.exp u*x) := by
    intro u
    unfold radial
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp,Complex.ofReal_exp,
      ← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  have changed := exp_Iic_substitution radial
  simp only [expRead] at changed
  have scalar : (∫ tau : ℝ in Ioi 0,Complex.exp ((-star coordinate.value/2)*(tau:ℂ))*value (Real.exp (-tau/2)*x))=
      (2:ℂ)*∫ u : ℝ in Ioc 0 1,radial u := by
    have halfRead : (fun u : ℝ=>Complex.exp ((-star coordinate.value/2)*((2*u:ℝ):ℂ))*value (Real.exp (-(2*u)/2)*x))=
        fun u : ℝ=>Complex.exp (star coordinate.value*((-u:ℝ):ℂ))*value (Real.exp (-u)*x) := by
      funext u
      have arg : (-star coordinate.value/2)*((2*u:ℝ):ℂ)=star coordinate.value*((-u:ℝ):ℂ) := by push_cast;ring
      rw [arg,show -(2*u)/2=-u by ring]
    rw [halfRead,reflected] at half
    simp only [neg_zero,Complex.real_smul] at half
    rw [changed] at half
    norm_num only [inv_eq_one_div,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at half
    linear_combination -2*half
  rw [scalar]
  have scaling := intervalIntegral.smul_integral_comp_mul_right
    (f:=fun t : ℝ=>(t:ℂ)^(star coordinate.value-1)*value t) (a:=0) (b:=1) x
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    show (0:ℝ)*x=0 by ring,show (1:ℝ)*x=x by ring,intervalIntegral.integral_of_le positive.le] at scaling
  simp only [Complex.real_smul] at scaling
  have pulled : (∫ u : ℝ in Ioc 0 1,((u*x:ℝ):ℂ)^(star coordinate.value-1)*value (u*x))=
      (x:ℂ)^(star coordinate.value-1)*(∫ u : ℝ in Ioc 0 1,radial u) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u inside
    unfold radial
    dsimp only
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg inside.1.le positive.le]
    ring
  rw [pulled] at scaling
  have inverse : (x:ℂ)^(-star coordinate.value)*((x:ℂ)*(x:ℂ)^(star coordinate.value-1))=1 := by
    have shifted : (x:ℂ)*(x:ℂ)^(star coordinate.value-1)=(x:ℂ)^(star coordinate.value) := by
      calc
        _ = (x:ℂ)^(1:ℂ)*(x:ℂ)^(star coordinate.value-1) := by rw [Complex.cpow_one]
        _ = (x:ℂ)^((1:ℂ)+(star coordinate.value-1)) := (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')).symm
        _ = _ := by congr 1;ring
    rw [shifted,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),neg_add_cancel,Complex.cpow_zero]
  have multiplied := congrArg (fun z : ℂ=>(x:ℂ)^(-star coordinate.value)*z) scaling
  have reduced : (∫ u : ℝ in Ioc 0 1,radial u)=(x:ℂ)^(-star coordinate.value)*∫ t : ℝ in Ioc 0 x,(t:ℂ)^(star coordinate.value-1)*value t := by
    calc
      _ = ((x:ℂ)^(-star coordinate.value)*((x:ℂ)*(x:ℂ)^(star coordinate.value-1)))*(∫ u : ℝ in Ioc 0 1,radial u) := by rw [inverse,one_mul]
      _ = _ := by
        convert! multiplied using 1
        ring
  calc
    _ = -(2:ℂ)*((x:ℂ)^(-star coordinate.value)*(∫ t : ℝ in Ioc 0 x,(t:ℂ)^(star coordinate.value-1)*value t)) := by rw [← reduced];ring
    _ = _ := by ring


end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
