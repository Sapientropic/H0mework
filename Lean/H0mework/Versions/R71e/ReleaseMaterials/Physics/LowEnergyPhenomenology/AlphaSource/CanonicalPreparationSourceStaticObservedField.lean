import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticNativeForcing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedStaticResidue
open PreparationVacuumObservedPoleTensor PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumQuantumSlowResidue
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalPoleAmputation
open PreparationVacuumPhysicalCharacteristic
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceJointFieldResidue sourceActualNativeResidue sourceAmputatedFieldVertex
  sourcePoleEulerInitial sourcePoleMaterialPairGap

/-- The full field generates a positive real static approach, including its retained third and fast channels. -/
theorem sourceStatic_causal_eventually (n : PhysicalMomentum) (spatial : 0<spatialSquare n) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,(eta:ℂ)∈sourceCausalDomain n := by
  have near : ∀ᶠ eta : ℝ in 𝓝 0,eta^2<spatialSquare n/3 :=
    (continuous_pow 2).continuousAt.eventually_lt_const (by simpa using (div_pos spatial (by norm_num : (0:ℝ)<3)))
  filter_upwards [self_mem_nhdsWithin,near.filter_mono nhdsWithin_le_nhds] with eta positive small
  refine ⟨by simpa using positive,?_⟩
  have a : (-(25/18:ℝ))*eta^2+(25/54:ℝ)*spatialSquare n≠0 := by nlinarith
  have b : (10/99:ℝ)*eta^2+(12/335:ℝ)*spatialSquare n≠0 := by positivity
  have c : (20/27:ℝ)*eta^2+(8/15:ℝ)*spatialSquare n≠0 := by positivity
  have ac : -(25/18:ℂ)*(eta:ℂ)^2+(25/54:ℂ)*(spatialSquare n:ℂ)≠0 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_ofNat] using Complex.ofReal_ne_zero.mpr a
  have bc : (10/99:ℂ)*(eta:ℂ)^2+(12/335:ℂ)*(spatialSquare n:ℂ)≠0 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_ofNat] using Complex.ofReal_ne_zero.mpr b
  have cc : (20/27:ℂ)*(eta:ℂ)^2+(8/15:ℂ)*(spatialSquare n:ℂ)≠0 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_ofNat] using Complex.ofReal_ne_zero.mpr c
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  rw [sourceCausalPrincipal_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num : (128:ℂ)≠0) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr positive.ne')))
    (mul_ne_zero (mul_ne_zero two fifteen) ac)) (mul_ne_zero (mul_ne_zero two fifteen) bc))
    (mul_ne_zero (mul_ne_zero two fifteen) cc)

private theorem denominator_nonzero (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 2) :
    sourceCanonicalDenominator n 0 i≠0 := by
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  have norm : (spatialSquare n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr spatial.ne'
  fin_cases i <;> norm_num [sourceCanonicalDenominator,two,fifteen,norm]

/-- The static source coefficient retains the two independently generated detector channels. -/
def sourceStaticObserved (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℂ :=
  -sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)*
    ((sourceCanonicalDenominator n 0 0)⁻¹*sourceSlowRead (sourceStaticNative q n l r) 0+
     (sourceCanonicalDenominator n 0 1)⁻¹*sourceSlowRead (sourceStaticNative q n l r) 1)

/-- Actual full-Gamma field observation has a generated static coefficient after its already-paid delta-cubed limit. -/
theorem sourceStaticObserved_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)^2*sourceAmputatedFieldVertex q pL pR a b
      (sourceJointFieldResidue q n (eta:ℂ) l r))
      (𝓝[>] 0) (𝓝 (sourceStaticObserved q n l r a b pL pR)) := by
  have denominator (i : Fin 2) : Tendsto (fun eta : ℝ=>(sourceCanonicalDenominator n (eta:ℂ) i)⁻¹)
      (𝓝[>] 0) (𝓝 ((sourceCanonicalDenominator n 0 i)⁻¹)) := by
    have continuous : Continuous (fun eta : ℝ=>sourceCanonicalDenominator n (eta:ℂ) i) := by
      unfold sourceCanonicalDenominator
      split_ifs <;> fun_prop
    exact (continuous.continuousAt.inv₀ (denominator_nonzero n spatial i)).tendsto.mono_left nhdsWithin_le_nhds
  have component (i : Fin 5) := (tendsto_pi_nhds.mp (sourceStaticSlow_generated q n l r)) i
  have result:=(tendsto_const_nhds (x:= -sourcePoleMaterialPairGap q pL pR a b*
      sourceOriginWeight (sourcePoleEulerInitial q pL pR a b))).mul
    (((denominator 0).mul (component 0)).add ((denominator 1).mul (component 1)))
  apply result.congr'
  filter_upwards [sourceStatic_causal_eventually n spatial] with eta legal
  rw [sourceObservedField_tensor q n ⟨(eta:ℂ),legal⟩ l r a b pL pR nonrealL nonrealR]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

/-- The spatial inverse-square factor is read from the original two static denominators. -/
theorem sourceStaticObserved_spatial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    sourceStaticObserved q n l r a b pL pR=
      (-sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)/
        (rootTwo*rootFifteen*(spatialSquare n:ℂ)))*
      ((54/25:ℂ)*sourceSlowRead (sourceStaticNative q n l r) 0+
       (335/12:ℂ)*sourceSlowRead (sourceStaticNative q n l r) 1) := by
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  have norm : (spatialSquare n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr spatial.ne'
  unfold sourceStaticObserved
  norm_num [sourceCanonicalDenominator]
  field_simp [two,fifteen,norm]

end LowEnergy.PreparationVacuumObservedStaticResidue
