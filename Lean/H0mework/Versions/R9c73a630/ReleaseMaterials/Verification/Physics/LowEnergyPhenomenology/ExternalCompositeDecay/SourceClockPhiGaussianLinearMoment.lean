import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWeightedVarianceGaussian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.GaussianProfileFirstMoment
open MeasureTheory ProbabilityTheory
private abbrev γ:=gaussianReal 0 1
private abbrev γ₂:=γ.prod γ

def noiseCoordinate(axis:Bool)(x:ℝ×ℝ):ℝ:=if axis then x.2 else x.1

private theorem gaussian_mgf(a:ℝ):(∫x:ℝ,Real.exp (a*x) ∂γ)=Real.exp (a^2/2):=by
  have h:=congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) a
  simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using h
private theorem gaussian_linear_mgf(a:ℝ):
    Integrable (fun x:ℝ=>x*Real.exp (a*x)) γ ∧ (∫x:ℝ,x*Real.exp (a*x) ∂γ)=a*Real.exp (a^2/2):=by
  have ha:a∈interior (integrableExpSet (fun x:ℝ=>x) γ):=by
    simp only [integrableExpSet_fun_id_gaussianReal,interior_univ,Set.mem_univ]
  constructor
  · simpa only [pow_one] using integrable_pow_mul_exp_of_mem_interior_integrableExpSet ha 1
  · have hd:=hasDerivAt_mgf ha
    have hpoly:HasDerivAt (fun x:ℝ=>x^2/2) a a:=by
      convert (hasDerivAt_pow 2 a).div_const 2 using 1 <;> first | rfl | ring
    have he:=hpoly.exp
    have heq:mgf (fun x:ℝ=>x) γ=(fun x:ℝ=>Real.exp (x^2/2)):=funext gaussian_mgf
    rw [heq] at hd
    have h:=hd.unique he
    simpa only [mul_comm] using h

/-- The actual first coordinate moment is obtained from the Gaussian MGF derivative; the two plane coordinates remain independent. -/
theorem actual_gaussian_plane_linear_exponential(axis:Bool)(m a b:ℝ):
    Integrable (fun x:ℝ×ℝ=>noiseCoordinate axis x*Real.exp (m+a*x.1+b*x.2)) γ₂ ∧
    (∫x:ℝ×ℝ,noiseCoordinate axis x*Real.exp (m+a*x.1+b*x.2) ∂γ₂)=
      (if axis then b else a)*(∫x:ℝ×ℝ,Real.exp (m+a*x.1+b*x.2) ∂γ₂):=by
  have h0(x:ℝ×ℝ):Real.exp (m+a*x.1+b*x.2)=Real.exp m*(Real.exp (a*x.1)*Real.exp (b*x.2)):=by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hi0:(∫x:ℝ×ℝ,Real.exp (m+a*x.1+b*x.2) ∂γ₂)=Real.exp m*(Real.exp (a^2/2)*Real.exp (b^2/2)):=by
    simp_rw [h0]
    rw [integral_const_mul]
    erw [integral_prod_mul (μ:=γ) (ν:=γ) (fun x:ℝ=>Real.exp (a*x)) (fun x:ℝ=>Real.exp (b*x))]
    rw [gaussian_mgf,gaussian_mgf]
  have ha:=gaussian_linear_mgf a
  have hb:=gaussian_linear_mgf b
  have hae:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) a
  have hbe:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) b
  cases axis
  · have hx(x:ℝ×ℝ):noiseCoordinate false x*Real.exp (m+a*x.1+b*x.2)=
        Real.exp m*((x.1*Real.exp (a*x.1))*Real.exp (b*x.2)):=by rw [h0];simp only [noiseCoordinate,Bool.false_eq_true,ite_false];ring
    refine ⟨((ha.1.mul_prod hbe).const_mul (Real.exp m)).congr (Filter.Eventually.of_forall (fun x=>(hx x).symm)),?_⟩
    simp_rw [hx]
    rw [integral_const_mul]
    erw [integral_prod_mul (μ:=γ) (ν:=γ) (fun x:ℝ=>x*Real.exp (a*x)) (fun x:ℝ=>Real.exp (b*x))]
    rw [ha.2,gaussian_mgf,hi0]
    simp only [Bool.false_eq_true,ite_false]
    ring
  · have hx(x:ℝ×ℝ):noiseCoordinate true x*Real.exp (m+a*x.1+b*x.2)=
        Real.exp m*(Real.exp (a*x.1)*(x.2*Real.exp (b*x.2))):=by rw [h0];simp only [noiseCoordinate,ite_true];ring
    refine ⟨((hae.mul_prod hb.1).const_mul (Real.exp m)).congr (Filter.Eventually.of_forall (fun x=>(hx x).symm)),?_⟩
    simp_rw [hx]
    rw [integral_const_mul]
    erw [integral_prod_mul (μ:=γ) (ν:=γ) (fun x:ℝ=>Real.exp (a*x)) (fun x:ℝ=>x*Real.exp (b*x))]
    rw [gaussian_mgf,hb.2,hi0]
    simp only [ite_true]
    ring

theorem actual_noise_square(axis:Bool):Integrable (fun x:ℝ×ℝ=>noiseCoordinate axis x^2) γ₂ ∧
    (∫x:ℝ×ℝ,noiseCoordinate axis x^2 ∂γ₂)=1:=by
  have hi:Integrable (fun x:ℝ=>x^2) γ:=(memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have hm:(∫x:ℝ,x^2 ∂γ)=1:=by
    convert! SourceClockPhiGaussianComplexIBP.standard_gaussian_square_moment using 1
  cases axis
  · refine ⟨hi.comp_fst γ,?_⟩
    calc
      _=(∫x:ℝ,x^2 ∂γ):=by
        simpa only [noiseCoordinate,Bool.false_eq_true,ite_false,probReal_univ,one_smul] using
          integral_fun_fst (μ:=γ) (ν:=γ) (fun x:ℝ=>x^2)
      _=1:=hm
  · refine ⟨hi.comp_snd γ,?_⟩
    calc
      _=(∫x:ℝ,x^2 ∂γ):=by
        simpa only [noiseCoordinate,ite_true,probReal_univ,one_smul] using
          integral_fun_snd (μ:=γ) (ν:=γ) (fun x:ℝ=>x^2)
      _=1:=hm
end LowEnergy.GaussianProfileFirstMoment
