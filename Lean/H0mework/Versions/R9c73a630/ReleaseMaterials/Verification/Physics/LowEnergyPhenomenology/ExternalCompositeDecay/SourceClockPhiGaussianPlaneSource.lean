import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatHamiltonianCoefficient
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianComplexIBP
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedDiffusionSource
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceClockPhiGaussianPlaneSource
open MeasureTheory ProbabilityTheory GaussCoreHilbert GaussCoreDifferential GaussFockPair
open SourceQuantumConfigurationHilbert
private abbrev γ := gaussianReal 0 1

theorem actual_rotated_heat_exponential_moment (V t q θ:ℝ) (hV:0<V) (ht:0<t):
    Integrable (fun z:ℝ×ℝ=>Real.exp (q*(-Real.log ((V+18*t)/V)/6+
      Real.sqrt (Real.log ((V+18*t)/V)/9)*(z.1*Real.cos θ+z.2*Real.sin θ)))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,Real.exp (q*(-Real.log ((V+18*t)/V)/6+
      Real.sqrt (Real.log ((V+18*t)/V)/9)*(z.1*Real.cos θ+z.2*Real.sin θ))) ∂γ.prod γ)=
      Real.rpow ((V+18*t)/V) (q*(q-3)/18):=by
  have hp:=SourceClockPhiHeatClockPrice.clock_positive_price V t hV ht
  let R:ℝ:=(V+18*t)/V
  let L:ℝ:=Real.log R
  let m:ℝ:= -L/6
  let w:ℝ:=Real.sqrt (L/9)
  have hR:0<R:=div_pos hp.1 hV
  have hL:0<L:=hp.2.1
  have hw:w^2=L/9:=Real.sq_sqrt (by positivity)
  have hc:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (q*w*Real.cos θ)
  have hs:=integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (q*w*Real.sin θ)
  have hf(z:ℝ×ℝ):Real.exp (q*(m+w*(z.1*Real.cos θ+z.2*Real.sin θ)))=
      Real.exp (q*m)*(Real.exp ((q*w*Real.cos θ)*z.1)*Real.exp ((q*w*Real.sin θ)*z.2)):=by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  change Integrable (fun z:ℝ×ℝ=>Real.exp (q*(m+w*(z.1*Real.cos θ+z.2*Real.sin θ)))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,Real.exp (q*(m+w*(z.1*Real.cos θ+z.2*Real.sin θ))) ∂γ.prod γ)=Real.rpow R (q*(q-3)/18)
  constructor
  · simpa only [hf] using (hc.mul_prod hs).const_mul (Real.exp (q*m))
  · simp_rw [hf]
    rw [integral_const_mul]
    erw [integral_prod_mul (μ:=γ) (ν:=γ)
      (fun x:ℝ=>Real.exp ((q*w*Real.cos θ)*x)) (fun x:ℝ=>Real.exp ((q*w*Real.sin θ)*x))]
    have hmgf(a:ℝ):(∫x:ℝ,Real.exp (a*x) ∂γ)=Real.exp (a^2/2):=by
      have h:=congrFun (mgf_fun_id_gaussianReal (μ:=0) (v:=1)) a
      simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using h
    rw [hmgf,hmgf,←Real.exp_add,←Real.exp_add,Real.rpow_eq_pow,Real.rpow_def_of_pos hR]
    congr 1
    have hθ:=Real.cos_sq_add_sin_sq θ
    have hsquare:(q*w*Real.cos θ)^2+(q*w*Real.sin θ)^2=q^2*w^2:=by
      nlinarith [show (q*w)^2*(Real.cos θ^2+Real.sin θ^2)=(q*w)^2 by rw [hθ,mul_one]]
    rw [show q*m+((q*w*Real.cos θ)^2/2+(q*w*Real.sin θ)^2/2)=q*m+(q^2*w^2)/2 by linarith [hsquare],hw]
    dsimp only [m,L]
    ring

private theorem plane_quadratic (a b c d e f:ℂ):
    Integrable (fun z:ℝ×ℝ=>a+(z.1:ℂ)*b+(z.2:ℂ)*c+((z.1^2:ℝ):ℂ)*d+
      ((z.1*z.2:ℝ):ℂ)*e+((z.2^2:ℝ):ℂ)*f) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,a+(z.1:ℂ)*b+(z.2:ℂ)*c+((z.1^2:ℝ):ℂ)*d+
      ((z.1*z.2:ℝ):ℂ)*e+((z.2^2:ℝ):ℂ)*f ∂γ.prod γ)=a+d+f:=by
  have h1:Integrable (fun x:ℝ=>x) γ:=(memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have h2:Integrable (fun x:ℝ=>x^2) γ:=(memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have hi1:Integrable (fun z:ℝ×ℝ=>(z.1:ℂ)) (γ.prod γ):=(h1.comp_fst γ).ofReal
  have hi2:Integrable (fun z:ℝ×ℝ=>(z.2:ℂ)) (γ.prod γ):=(h1.comp_snd γ).ofReal
  have hi11:Integrable (fun z:ℝ×ℝ=>((z.1^2:ℝ):ℂ)) (γ.prod γ):=(h2.comp_fst γ).ofReal
  have hi12:Integrable (fun z:ℝ×ℝ=>((z.1*z.2:ℝ):ℂ)) (γ.prod γ):=(h1.mul_prod h1).ofReal
  have hi22:Integrable (fun z:ℝ×ℝ=>((z.2^2:ℝ):ℂ)) (γ.prod γ):=(h2.comp_snd γ).ofReal
  have r1:(∫z:ℝ×ℝ,z.1 ∂γ.prod γ)=0:=by
    simpa only [integral_id_gaussianReal,probReal_univ,one_smul] using
      (integral_fun_fst (μ:=γ) (ν:=γ) (fun x:ℝ=>x))
  have r2:(∫z:ℝ×ℝ,z.2 ∂γ.prod γ)=0:=by
    simpa only [integral_id_gaussianReal,probReal_univ,one_smul] using
      (integral_fun_snd (μ:=γ) (ν:=γ) (fun x:ℝ=>x))
  have sq:(∫x:ℝ,x^2 ∂γ)=1:=by
    convert! SourceClockPhiGaussianComplexIBP.standard_gaussian_square_moment using 1
  have r11:(∫z:ℝ×ℝ,z.1^2 ∂γ.prod γ)=1:=by
    calc _=(∫x:ℝ,x^2 ∂γ):=by
           simpa only [probReal_univ,one_smul] using (integral_fun_fst (μ:=γ) (ν:=γ) (fun x:ℝ=>x^2))
         _=1:=sq
  have r22:(∫z:ℝ×ℝ,z.2^2 ∂γ.prod γ)=1:=by
    calc _=(∫x:ℝ,x^2 ∂γ):=by
           simpa only [probReal_univ,one_smul] using (integral_fun_snd (μ:=γ) (ν:=γ) (fun x:ℝ=>x^2))
         _=1:=sq
  have r12:(∫z:ℝ×ℝ,z.1*z.2 ∂γ.prod γ)=0:=by
    simpa only [integral_id_gaussianReal,zero_mul] using
      (integral_prod_mul (μ:=γ) (ν:=γ) (fun x:ℝ=>x) (fun x:ℝ=>x))
  have i1:(∫z:ℝ×ℝ,(z.1:ℂ) ∂γ.prod γ)=0:=by
    simpa only [r1,Complex.ofReal_zero] using! (integral_ofReal (𝕜:=ℂ) (μ:=γ.prod γ) (f:=fun z:ℝ×ℝ=>z.1))
  have i2:(∫z:ℝ×ℝ,(z.2:ℂ) ∂γ.prod γ)=0:=by
    simpa only [r2,Complex.ofReal_zero] using! (integral_ofReal (𝕜:=ℂ) (μ:=γ.prod γ) (f:=fun z:ℝ×ℝ=>z.2))
  have i11:(∫z:ℝ×ℝ,((z.1^2:ℝ):ℂ) ∂γ.prod γ)=1:=by
    calc _=Complex.ofReal (∫z:ℝ×ℝ,z.1^2 ∂γ.prod γ):=by
           exact integral_complex_ofReal (μ:=γ.prod γ) (f:=fun z:ℝ×ℝ=>z.1^2)
         _=1:=by exact_mod_cast r11
  have i22:(∫z:ℝ×ℝ,((z.2^2:ℝ):ℂ) ∂γ.prod γ)=1:=by
    calc _=Complex.ofReal (∫z:ℝ×ℝ,z.2^2 ∂γ.prod γ):=by
           exact integral_complex_ofReal (μ:=γ.prod γ) (f:=fun z:ℝ×ℝ=>z.2^2)
         _=1:=by exact_mod_cast r22
  have i12:(∫z:ℝ×ℝ,((z.1*z.2:ℝ):ℂ) ∂γ.prod γ)=0:=by
    simpa only [r12,Complex.ofReal_zero] using! (integral_ofReal (𝕜:=ℂ) (μ:=γ.prod γ) (f:=fun z:ℝ×ℝ=>z.1*z.2))
  constructor
  · exact (((((integrable_const a).add (hi1.mul_const b)).add (hi2.mul_const c)).add
      (hi11.mul_const d)).add (hi12.mul_const e)).add (hi22.mul_const f)
  · erw [integral_add (((((integrable_const a).add (hi1.mul_const b)).add (hi2.mul_const c)).add
      (hi11.mul_const d)).add (hi12.mul_const e)) (hi22.mul_const f)]
    erw [integral_add ((((integrable_const a).add (hi1.mul_const b)).add (hi2.mul_const c)).add
      (hi11.mul_const d)) (hi12.mul_const e)]
    erw [integral_add (((integrable_const a).add (hi1.mul_const b)).add (hi2.mul_const c)) (hi11.mul_const d)]
    erw [integral_add ((integrable_const a).add (hi1.mul_const b)) (hi2.mul_const c)]
    erw [integral_add (integrable_const a) (hi1.mul_const b)]
    simp only [integral_const,probReal_univ,one_smul,integral_mul_const,i1,i2,i11,i12,i22,zero_mul,one_mul,add_zero]

theorem actual_gaussian_affine_source_pair (A B C D E F:QuantumTest)
    (M:QuantumTest→ₗ[ℂ]QuantumTest):
    Integrable (fun z:ℝ×ℝ=>sourcePair (A+(z.1:ℂ) • B+(z.2:ℂ) • C)
      (M (D+(z.1:ℂ) • E+(z.2:ℂ) • F))) (γ.prod γ) ∧
    (∫z:ℝ×ℝ,sourcePair (A+(z.1:ℂ) • B+(z.2:ℂ) • C)
      (M (D+(z.1:ℂ) • E+(z.2:ℂ) • F)) ∂γ.prod γ)=
        sourcePair A (M D)+sourcePair B (M E)+sourcePair C (M F):=by
  have hp:=plane_quadratic (sourcePair A (M D))
    (sourcePair B (M D)+sourcePair A (M E))
    (sourcePair C (M D)+sourcePair A (M F))
    (sourcePair B (M E)) (sourcePair B (M F)+sourcePair C (M E)) (sourcePair C (M F))
  have he(z:ℝ×ℝ):sourcePair (A+(z.1:ℂ) • B+(z.2:ℂ) • C)
      (M (D+(z.1:ℂ) • E+(z.2:ℂ) • F))=
      sourcePair A (M D)+(z.1:ℂ)*(sourcePair B (M D)+sourcePair A (M E))+
      (z.2:ℂ)*(sourcePair C (M D)+sourcePair A (M F))+
      ((z.1^2:ℝ):ℂ)*sourcePair B (M E)+
      ((z.1*z.2:ℝ):ℂ)*(sourcePair B (M F)+sourcePair C (M E))+
      ((z.2^2:ℝ):ℂ)*sourcePair C (M F):=by
    simp only [sourcePair,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_mul]
    ring
  simpa only [he] using hp
end LowEnergy.SourceClockPhiGaussianPlaneSource
