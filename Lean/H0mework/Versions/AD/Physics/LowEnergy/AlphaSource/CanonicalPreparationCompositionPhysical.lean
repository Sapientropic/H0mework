import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionFamily
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumRemainder
open PreparationVacuumWeyl PreparationVacuumWeylDecay CanonicalPreparationSquareCutoff PreparationActualFactor
open CanonicalPreparationCutoff
open MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

theorem sourceFourier_inversion (p z : PhysicalMomentum) :
    (∫ k : PhysicalMomentum,𝐞 ⟪z,k⟫ • partialFourier p k)=symbolSlice p z := by
  have pair : (𝓕⁻ (𝓕 (sourceSchwartzSlice p) : 𝓢(PhysicalMomentum,ℂ)) : 𝓢(PhysicalMomentum,ℂ))=
      sourceSchwartzSlice p := by simp only [FourierTransform.fourierInv_fourier_eq]
  have inversion := congrArg (fun f : 𝓢(PhysicalMomentum,ℂ) => f z) pair
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at inversion
  simpa only [real_inner_comm z,sourceSchwartzSlice_fourier,sourceSchwartzSlice_apply] using inversion

theorem compositionFamily_zero (z p : PhysicalMomentum) :
    compositionFamily 0 z p=(symbolSlice p z)^2 := by
  have split : compositionIntegrand 0 z p=
      (fun w : PhysicalMomentum × PhysicalMomentum =>
        (𝐞 ⟪z,w.1⟫ • partialFourier p w.1)*(𝐞 ⟪z,w.2⟫ • partialFourier p w.2)) := by
    ext w
    simp only [compositionIntegrand,zero_mul,zero_smul,add_zero,sub_zero,
      inner_add_right,Real.fourierChar.map_add_eq_mul,Circle.smul_def,Circle.coe_mul,smul_eq_mul]
    ring
  rw [compositionFamily,split]
  have separated := integral_prod_mul (μ := (volume : Measure PhysicalMomentum))
    (ν := (volume : Measure PhysicalMomentum))
    (fun k : PhysicalMomentum => 𝐞 ⟪z,k⟫ • partialFourier p k)
    (fun k : PhysicalMomentum => 𝐞 ⟪z,k⟫ • partialFourier p k)
  calc
    _ = (∫ k : PhysicalMomentum,𝐞 ⟪z,k⟫ • partialFourier p k)*
        (∫ k : PhysicalMomentum,𝐞 ⟪z,k⟫ • partialFourier p k) := separated
    _ = _ := by rw [sourceFourier_inversion,pow_two]

theorem compositionFamily_even (t : ℝ) (z p : PhysicalMomentum) :
    compositionFamily (-t) z p=compositionFamily t z p := by
  have swap : compositionIntegrand (-t) z p=compositionIntegrand t z p ∘ Prod.swap := by
    ext w
    simp only [compositionIntegrand,Function.comp_apply,Prod.swap,neg_mul,neg_smul,
      sub_neg_eq_add,add_comm w.2 w.1]
    rw [←sub_eq_add_neg,mul_comm]
  rw [compositionFamily,swap]
  change (∫ w : PhysicalMomentum × PhysicalMomentum,
      compositionIntegrand t z p (Prod.swap w) ∂volume.prod volume)=compositionFamily t z p
  rw [integral_prod_swap]
  rfl

theorem compositionFamily_conjugate (t : ℝ) (z p : PhysicalMomentum) :
    conj (compositionFamily t z p)=compositionFamily (-t) z p := by
  have negative : (fun w => conj (compositionIntegrand t z p w))=
      (fun w : PhysicalMomentum × PhysicalMomentum => compositionIntegrand (-t) z p (-w)) := by
    ext w
    simp only [compositionIntegrand,Circle.smul_def,smul_eq_mul,map_mul,
      Circle.starRingEnd_addChar,partialFourier_conjugate,Prod.fst_neg,Prod.snd_neg,
      neg_mul,smul_neg,neg_smul,neg_neg,inner_neg_right,←neg_add]
  rw [compositionFamily,←integral_conj,negative]
  have invariance := Measure.integral_comp_smul (volume.prod volume)
    (compositionIntegrand (-t) z p) (-1)
  rw [Module.finrank_prod,finrank_euclideanSpace_fin] at invariance
  norm_num at invariance
  exact invariance

theorem compositionFamily_real (t : ℝ) (z p : PhysicalMomentum) :
    conj (compositionFamily t z p)=compositionFamily t z p := by
  rw [compositionFamily_conjugate,compositionFamily_even]

def physicalPartialFourier (p k : PhysicalMomentum) : ℂ :=
  ∫ x : PhysicalMomentum,Complex.exp ((-⟪x,k⟫ : ℂ)*Complex.I) • symbolSlice p x

theorem physicalPartialFourier_readback (p k : PhysicalMomentum) :
    physicalPartialFourier p k=partialFourier p ((2*Real.pi)⁻¹ • k) := by
  rw [physicalPartialFourier,partialFourier,Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  have phase : -2*Real.pi*⟪x,(2*Real.pi)⁻¹ • k⟫ = -⟪x,k⟫ := by
    rw [inner_smul_right]
    field_simp [Real.pi_ne_zero]
  rw [phase]
  simp only [Complex.ofReal_neg]

def physicalCompositionIntegrand (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  Complex.exp ((⟪z,w.1+w.2⟫ : ℂ)*Complex.I) •
    (physicalPartialFourier (p+(t/2) • w.2) w.1*
      physicalPartialFourier (p-(t/2) • w.1) w.2)

theorem physicalCompositionIntegrand_scaled (t : ℝ) (z p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) :
    physicalCompositionIntegrand t z p ((2*Real.pi) • w)=compositionIntegrand t z p w := by
  have inverse : (2*Real.pi)⁻¹*(2*Real.pi)=1 := inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have half : (t/2)*(2*Real.pi)=t*Real.pi := by ring
  have positivePhase : ⟪z,(2*Real.pi) • w.1+(2*Real.pi) • w.2⟫=
      2*Real.pi*⟪z,w.1+w.2⟫ := by rw [←smul_add,inner_smul_right]
  change Complex.exp ((⟪z,(2*Real.pi) • w.1+(2*Real.pi) • w.2⟫ : ℂ)*Complex.I) •
    (physicalPartialFourier (p+(t/2) • ((2*Real.pi) • w.2)) ((2*Real.pi) • w.1)*
      physicalPartialFourier (p-(t/2) • ((2*Real.pi) • w.1)) ((2*Real.pi) • w.2))=_
  simp only [compositionIntegrand,physicalPartialFourier_readback,smul_smul,inverse,one_smul,half,positivePhase,
    Circle.smul_def,Real.fourierChar_apply]

def physicalCompositionFamily (t : ℝ) (z p : PhysicalMomentum) : ℂ :=
  ((2*Real.pi)^200)⁻¹ •
    ∫ w : PhysicalMomentum × PhysicalMomentum,physicalCompositionIntegrand t z p w ∂volume.prod volume

theorem original_physical_composition_readback (t : ℝ) (z p : PhysicalMomentum) :
    physicalCompositionFamily t z p=compositionFamily t z p := by
  have dimension : Module.finrank ℝ (PhysicalMomentum × PhysicalMomentum)=200 := by
    rw [Module.finrank_prod,finrank_euclideanSpace_fin]
  have scaled := Measure.integral_comp_smul_of_nonneg (volume.prod volume)
    (physicalCompositionIntegrand t z p) (2*Real.pi) (hR := by positivity)
  rw [dimension] at scaled
  rw [physicalCompositionFamily,←scaled]
  exact integral_congr_ae (Eventually.of_forall (physicalCompositionIntegrand_scaled t z p))

theorem original_physical_composition_integrable (t : ℝ) (z p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) :
    Integrable (physicalCompositionIntegrand t z p) (volume.prod volume) := by
  apply (integrable_comp_smul_iff (volume.prod volume) (physicalCompositionIntegrand t z p) (R := 2*Real.pi)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mp
  exact (compositionIntegrand_integrable t z p unitInterval).congr
    (Eventually.of_forall (fun w => (physicalCompositionIntegrand_scaled t z p w).symm))

def sourceFullCompositionDefect (z : FlatConfiguration) (p : PhysicalMomentum) : ℂ :=
  compositionFamily 1 (flatPosition.symm z) p-compositionFamily 0 (flatPosition.symm z) p

theorem sourceFullCompositionDefect_readback (z : FlatConfiguration) (p : PhysicalMomentum) :
    sourceFullCompositionDefect z p=
      compositionFamily 1 (flatPosition.symm z) p-(b1 (z,p) : ℂ)^2 := by
  rw [sourceFullCompositionDefect,compositionFamily_zero]
  simp only [symbolSlice,flatPosition.apply_symm_apply]

theorem sourceFullCompositionDefect_real (z : FlatConfiguration) (p : PhysicalMomentum) :
    conj (sourceFullCompositionDefect z p)=sourceFullCompositionDefect z p := by
  simp only [sourceFullCompositionDefect,map_sub,compositionFamily_real]

end LowEnergy.PreparationVacuumRemainder
