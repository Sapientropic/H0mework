import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianPlaneSource
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceClockPhiFourGaussianAffineSource
open MeasureTheory ProbabilityTheory GaussCoreHilbert GaussCoreDifferential GaussFockPair
open SourceQuantumConfigurationHilbert
private abbrev γ := gaussianReal 0 1
private abbrev γ2 := γ.prod γ
private abbrev γ4 := γ2.prod γ2
private def coord (i : Fin 4) (z : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ :=
  ![z.1.1,z.1.2,z.2.1,z.2.2] i
private def coeff (i : Fin 5) (z : (ℝ×ℝ)×(ℝ×ℝ)) : ℂ :=
  ![1,(z.1.1:ℂ),(z.1.2:ℂ),(z.2.1:ℂ),(z.2.2:ℂ)] i
private theorem coord_integrable (i : Fin 4) : Integrable (coord i) γ4 := by
  have h : Integrable (fun x : ℝ => x) γ :=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  fin_cases i
  · exact (h.comp_fst γ).comp_fst γ2
  · exact (h.comp_snd γ).comp_fst γ2
  · exact (h.comp_fst γ).comp_snd γ2
  · exact (h.comp_snd γ).comp_snd γ2
private theorem coord_square_integrable (i : Fin 4) : Integrable (fun z => (coord i z)^2) γ4 := by
  have h : Integrable (fun x : ℝ => x^2) γ :=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  fin_cases i
  · exact (h.comp_fst γ).comp_fst γ2
  · exact (h.comp_snd γ).comp_fst γ2
  · exact (h.comp_fst γ).comp_snd γ2
  · exact (h.comp_snd γ).comp_snd γ2
private theorem coeff_pair_integrable (i j : Fin 5) :
    Integrable (fun z => coeff i z * coeff j z) γ4 := by
  have hcoord (k : Fin 4) : Integrable (fun z => (coord k z : ℂ)) γ4 := (coord_integrable k).ofReal
  have hsquare (k : Fin 4) : Integrable (fun z => ((coord k z)^2 : ℝ)) γ4 := coord_square_integrable k
  have hid : Integrable (fun x : ℝ => x) γ :=
    (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have hwithin : Integrable (fun z : ℝ×ℝ => (z.1:ℂ)*(z.2:ℂ)) γ2 := by
    have h : Integrable (fun z : ℝ×ℝ => Complex.ofReal (z.1*z.2)) γ2 := (hid.mul_prod hid).ofReal
    convert! h using 1
    funext z
    exact (Complex.ofReal_mul z.1 z.2).symm
  have hcross (a b : ℝ×ℝ → ℂ) (ha : Integrable a γ2) (hb : Integrable b γ2) :
      Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => a z.1*b z.2) γ4 := ha.mul_prod hb
  fin_cases i <;> fin_cases j
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (1:ℂ)*(1:ℂ)) γ4
    simpa only [one_mul] using (integrable_const (1:ℂ) : Integrable (fun _ : (ℝ×ℝ)×(ℝ×ℝ) => (1:ℂ)) γ4)
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (1:ℂ)*(z.1.1:ℂ)) γ4
    simpa [coord] using hcoord 0
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (1:ℂ)*(z.1.2:ℂ)) γ4
    simpa [coord] using hcoord 1
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (1:ℂ)*(z.2.1:ℂ)) γ4
    simpa [coord] using hcoord 2
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (1:ℂ)*(z.2.2:ℂ)) γ4
    simpa [coord] using hcoord 3
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1:ℂ)*(1:ℂ)) γ4
    simpa [coord] using hcoord 0
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1:ℂ)*(z.1.1:ℂ)) γ4
    have h : Integrable (fun z => Complex.ofReal ((coord 0 z)^2)) γ4 := (hsquare 0).ofReal
    convert! h using 1
    funext z
    simp [coord,pow_two]
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1:ℂ)*(z.1.2:ℂ)) γ4
    exact hwithin.comp_fst γ2
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1:ℂ)*(z.2.1:ℂ)) γ4
    exact hcross _ _ (hid.comp_fst γ).ofReal (hid.comp_fst γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.1:ℂ)*(z.2.2:ℂ)) γ4
    exact hcross _ _ (hid.comp_fst γ).ofReal (hid.comp_snd γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.2:ℂ)*(1:ℂ)) γ4
    simpa [coord] using hcoord 1
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.2:ℂ)*(z.1.1:ℂ)) γ4
    simpa only [mul_comm] using hwithin.comp_fst γ2
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.2:ℂ)*(z.1.2:ℂ)) γ4
    have h : Integrable (fun z => Complex.ofReal ((coord 1 z)^2)) γ4 := (hsquare 1).ofReal
    convert! h using 1
    funext z
    simp [coord,pow_two]
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.2:ℂ)*(z.2.1:ℂ)) γ4
    exact hcross _ _ (hid.comp_snd γ).ofReal (hid.comp_fst γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.1.2:ℂ)*(z.2.2:ℂ)) γ4
    exact hcross _ _ (hid.comp_snd γ).ofReal (hid.comp_snd γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.1:ℂ)*(1:ℂ)) γ4
    simpa [coord] using hcoord 2
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.1:ℂ)*(z.1.1:ℂ)) γ4
    simpa only [mul_comm] using! hcross _ _ (hid.comp_fst γ).ofReal (hid.comp_fst γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.1:ℂ)*(z.1.2:ℂ)) γ4
    simpa only [mul_comm] using! hcross _ _ (hid.comp_snd γ).ofReal (hid.comp_fst γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.1:ℂ)*(z.2.1:ℂ)) γ4
    have h : Integrable (fun z => Complex.ofReal ((coord 2 z)^2)) γ4 := (hsquare 2).ofReal
    convert! h using 1
    funext z
    simp [coord,pow_two]
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.1:ℂ)*(z.2.2:ℂ)) γ4
    exact hwithin.comp_snd γ2
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.2:ℂ)*(1:ℂ)) γ4
    simpa [coord] using hcoord 3
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.2:ℂ)*(z.1.1:ℂ)) γ4
    simpa only [mul_comm] using! hcross _ _ (hid.comp_fst γ).ofReal (hid.comp_snd γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.2:ℂ)*(z.1.2:ℂ)) γ4
    simpa only [mul_comm] using! hcross _ _ (hid.comp_snd γ).ofReal (hid.comp_snd γ).ofReal
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.2:ℂ)*(z.2.1:ℂ)) γ4
    simpa only [mul_comm] using hwithin.comp_snd γ2
  · change Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (z.2.2:ℂ)*(z.2.2:ℂ)) γ4
    have h : Integrable (fun z => Complex.ofReal ((coord 3 z)^2)) γ4 := (hsquare 3).ofReal
    convert! h using 1
    funext z
    simp [coord,pow_two]
private theorem coeff_pair_integral (i j : Fin 5) :
    (∫z, coeff i z * coeff j z ∂γ4) = if i=j then 1 else 0 := by
  have hm : (∫x : ℝ, x ∂γ) = 0 := integral_id_gaussianReal
  have hsq : (∫x : ℝ, (x:ℂ)*(x:ℂ) ∂γ) = 1 := by
    have h := SourceClockPhiGaussianComplexIBP.standard_gaussian_square_moment
    calc
      _ = Complex.ofReal (∫x : ℝ, x^2 ∂γ) := by
        simp only [←pow_two,←Complex.ofReal_pow]
        exact integral_complex_ofReal
      _ = 1 := by exact_mod_cast h
  have hmc : (∫x : ℝ, (x:ℂ) ∂γ) = 0 := by
    simpa only [hm,Complex.ofReal_zero] using! (integral_ofReal (𝕜:=ℂ) (μ:=γ) (f:=fun x:ℝ=>x))
  have rfst : (∫z : ℝ×ℝ, (z.1:ℂ) ∂γ2) = 0 := by
    simpa only [probReal_univ,one_smul,hmc] using integral_fun_fst (μ:=γ) (ν:=γ) (fun x:ℝ=>(x:ℂ))
  have rsnd : (∫z : ℝ×ℝ, (z.2:ℂ) ∂γ2) = 0 := by
    simpa only [probReal_univ,one_smul,hmc] using integral_fun_snd (μ:=γ) (ν:=γ) (fun x:ℝ=>(x:ℂ))
  have sqfst : (∫z : ℝ×ℝ, (z.1:ℂ)*(z.1:ℂ) ∂γ2) = 1 := by
    simpa only [probReal_univ,one_smul,hsq] using integral_fun_fst (μ:=γ) (ν:=γ) (fun x:ℝ=>(x:ℂ)*(x:ℂ))
  have sqsnd : (∫z : ℝ×ℝ, (z.2:ℂ)*(z.2:ℂ) ∂γ2) = 1 := by
    simpa only [probReal_univ,one_smul,hsq] using integral_fun_snd (μ:=γ) (ν:=γ) (fun x:ℝ=>(x:ℂ)*(x:ℂ))
  have cross : (∫z : ℝ×ℝ, (z.1:ℂ)*(z.2:ℂ) ∂γ2) = 0 := by
    simpa only [hmc,zero_mul] using integral_prod_mul (μ:=γ) (ν:=γ) (fun x:ℝ=>(x:ℂ)) (fun x:ℝ=>(x:ℂ))
  have hfst (f : ℝ×ℝ → ℂ) : (∫z : (ℝ×ℝ)×(ℝ×ℝ), f z.1 ∂γ4) = ∫x, f x ∂γ2 := by
    simpa only [probReal_univ,one_smul] using integral_fun_fst (μ:=γ2) (ν:=γ2) f
  have hsnd (f : ℝ×ℝ → ℂ) : (∫z : (ℝ×ℝ)×(ℝ×ℝ), f z.2 ∂γ4) = ∫x, f x ∂γ2 := by
    simpa only [probReal_univ,one_smul] using integral_fun_snd (μ:=γ2) (ν:=γ2) f
  have hprod (f g : ℝ×ℝ → ℂ) :
      (∫z : (ℝ×ℝ)×(ℝ×ℝ), f z.1*g z.2 ∂γ4) = (∫x,f x ∂γ2)*(∫x,g x ∂γ2) :=
    integral_prod_mul f g
  fin_cases i <;> fin_cases j
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (1:ℂ)*(1:ℂ) ∂γ4) = 1
    simp only [integral_const,probReal_univ,one_smul,mul_one]
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (1:ℂ)*(z.1.1:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hfst (fun z => (z.1:ℂ))).trans rfst)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (1:ℂ)*(z.1.2:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hfst (fun z => (z.2:ℂ))).trans rsnd)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (1:ℂ)*(z.2.1:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hsnd (fun z => (z.1:ℂ))).trans rfst)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (1:ℂ)*(z.2.2:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hsnd (fun z => (z.2:ℂ))).trans rsnd)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.1:ℂ)*(1:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hfst (fun z => (z.1:ℂ))).trans rfst)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.1:ℂ)*(z.1.1:ℂ) ∂γ4) = 1
    simpa only [] using
        ((hfst (fun z => (z.1:ℂ)*(z.1:ℂ))).trans sqfst)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.1:ℂ)*(z.1.2:ℂ) ∂γ4) = 0
    simpa only [] using
        ((hfst (fun z => (z.1:ℂ)*(z.2:ℂ))).trans cross)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.1:ℂ)*(z.2.1:ℂ) ∂γ4) = 0
    simpa only [rfst,rfst,zero_mul] using
        hprod (fun z => (z.1:ℂ)) (fun z => (z.1:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.1:ℂ)*(z.2.2:ℂ) ∂γ4) = 0
    simpa only [rfst,rsnd,zero_mul] using
        hprod (fun z => (z.1:ℂ)) (fun z => (z.2:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.2:ℂ)*(1:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hfst (fun z => (z.2:ℂ))).trans rsnd)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.2:ℂ)*(z.1.1:ℂ) ∂γ4) = 0
    simpa only [mul_comm] using
        ((hfst (fun z => (z.1:ℂ)*(z.2:ℂ))).trans cross)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.2:ℂ)*(z.1.2:ℂ) ∂γ4) = 1
    simpa only [] using
        ((hfst (fun z => (z.2:ℂ)*(z.2:ℂ))).trans sqsnd)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.2:ℂ)*(z.2.1:ℂ) ∂γ4) = 0
    simpa only [rsnd,rfst,zero_mul] using
        hprod (fun z => (z.2:ℂ)) (fun z => (z.1:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.1.2:ℂ)*(z.2.2:ℂ) ∂γ4) = 0
    simpa only [rsnd,rsnd,zero_mul] using
        hprod (fun z => (z.2:ℂ)) (fun z => (z.2:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.1:ℂ)*(1:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hsnd (fun z => (z.1:ℂ))).trans rfst)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.1:ℂ)*(z.1.1:ℂ) ∂γ4) = 0
    simpa only [rfst,rfst,zero_mul,mul_comm] using
        hprod (fun z => (z.1:ℂ)) (fun z => (z.1:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.1:ℂ)*(z.1.2:ℂ) ∂γ4) = 0
    simpa only [rsnd,rfst,zero_mul,mul_comm] using
        hprod (fun z => (z.2:ℂ)) (fun z => (z.1:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.1:ℂ)*(z.2.1:ℂ) ∂γ4) = 1
    simpa only [] using
        ((hsnd (fun z => (z.1:ℂ)*(z.1:ℂ))).trans sqfst)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.1:ℂ)*(z.2.2:ℂ) ∂γ4) = 0
    simpa only [] using
        ((hsnd (fun z => (z.1:ℂ)*(z.2:ℂ))).trans cross)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.2:ℂ)*(1:ℂ) ∂γ4) = 0
    simpa only [mul_one,one_mul] using
        ((hsnd (fun z => (z.2:ℂ))).trans rsnd)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.2:ℂ)*(z.1.1:ℂ) ∂γ4) = 0
    simpa only [rfst,rsnd,zero_mul,mul_comm] using
        hprod (fun z => (z.1:ℂ)) (fun z => (z.2:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.2:ℂ)*(z.1.2:ℂ) ∂γ4) = 0
    simpa only [rsnd,rsnd,zero_mul,mul_comm] using
        hprod (fun z => (z.2:ℂ)) (fun z => (z.2:ℂ))
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.2:ℂ)*(z.2.1:ℂ) ∂γ4) = 0
    simpa only [mul_comm] using
        ((hsnd (fun z => (z.1:ℂ)*(z.2:ℂ))).trans cross)
  · change (∫z : (ℝ×ℝ)×(ℝ×ℝ), (z.2.2:ℂ)*(z.2.2:ℂ) ∂γ4) = 1
    simpa only [] using
        ((hsnd (fun z => (z.2:ℂ)*(z.2:ℂ))).trans sqsnd)
theorem actual_gaussian_affine_four_source_pair (A B : Fin 5 → QuantumTest)
    (M : QuantumTest →ₗ[ℂ] QuantumTest) :
    Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      sourcePair (∑i : Fin 5, coeff i z • A i) (M (∑j : Fin 5, coeff j z • B j))) γ4 ∧
    (∫z : (ℝ×ℝ)×(ℝ×ℝ),
      sourcePair (∑i : Fin 5, coeff i z • A i) (M (∑j : Fin 5, coeff j z • B j)) ∂γ4) =
        ∑i : Fin 5, sourcePair (A i) (M (B i)) := by
  have he (z : (ℝ×ℝ)×(ℝ×ℝ)) :
      sourcePair (∑i : Fin 5, coeff i z • A i) (M (∑j : Fin 5, coeff j z • B j)) =
        ∑i : Fin 5, ∑j : Fin 5, (coeff i z * coeff j z)*sourcePair (A i) (M (B j)) := by
    simp only [sourcePair,map_sum,map_smul]
    rw [sum_inner]
    simp only [inner_sum,inner_smul_left,inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc : (starRingEnd ℂ) (coeff i z) = coeff i z := by
      fin_cases i <;> change star (_:ℂ) = _ <;> simp [coeff,Complex.conj_ofReal]
    rw [hc]
    ring
  have hi (i j : Fin 5) : Integrable
      (fun z : (ℝ×ℝ)×(ℝ×ℝ) => (coeff i z * coeff j z)*sourcePair (A i) (M (B j))) γ4 :=
    (coeff_pair_integrable i j).mul_const _
  have hs : Integrable (fun z : (ℝ×ℝ)×(ℝ×ℝ) =>
      ∑i : Fin 5, ∑j : Fin 5, (coeff i z * coeff j z)*sourcePair (A i) (M (B j))) γ4 :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  constructor
  · simpa only [he] using hs
  · simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    simp_rw [integral_mul_const,coeff_pair_integral]
    simp
theorem actual_gaussian_affine_four_expanded_source_pair
    (A B C D E F G H I J:QuantumTest)(M:QuantumTest→ₗ[ℂ]QuantumTest):
    Integrable (fun x:(ℝ×ℝ)×(ℝ×ℝ)=>sourcePair
      (A+(x.1.1:ℂ) • B+(x.1.2:ℂ) • C+(x.2.1:ℂ) • D+(x.2.2:ℂ) • E)
      (M (F+(x.1.1:ℂ) • G+(x.1.2:ℂ) • H+(x.2.1:ℂ) • I+(x.2.2:ℂ) • J))) γ4 ∧
    (∫x:(ℝ×ℝ)×(ℝ×ℝ),sourcePair
      (A+(x.1.1:ℂ) • B+(x.1.2:ℂ) • C+(x.2.1:ℂ) • D+(x.2.2:ℂ) • E)
      (M (F+(x.1.1:ℂ) • G+(x.1.2:ℂ) • H+(x.2.1:ℂ) • I+(x.2.2:ℂ) • J)) ∂γ4)=
        sourcePair A (M F)+sourcePair B (M G)+sourcePair C (M H)+sourcePair D (M I)+sourcePair E (M J) := by
  have h:=actual_gaussian_affine_four_source_pair ![A,B,C,D,E] ![F,G,H,I,J] M
  simpa [coeff,Fin.sum_univ_succ,add_assoc] using h
end LowEnergy.SourceClockPhiFourGaussianAffineSource
