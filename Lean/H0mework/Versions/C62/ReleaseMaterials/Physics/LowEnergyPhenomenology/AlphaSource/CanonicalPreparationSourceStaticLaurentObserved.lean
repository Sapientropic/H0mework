import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticLaurentForcing

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticSimpleCoupling
open PreparationVacuumObservedPoleTensor PreparationVacuumObservedStaticResidue
open PreparationVacuumNativeSlowCoupling PreparationVacuumFullSlowFieldResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumQuantumSlowResidue PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalCharacteristic
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceJointFieldResidue sourceActualNativeResidue sourceAmputatedFieldVertex
  sourcePoleEulerInitial sourcePoleMaterialPairGap sourceSlowRead sourceStaticNative sourceNativeSimple

def sourceStaticDenominatorSlope (i : Fin 2) : ℂ :=
  rootTwo*rootFifteen*(if i=0 then -(25/18:ℂ) else 10/99)

theorem sourceStaticDenominator_even (n : PhysicalMomentum) (eta : ℂ) (i : Fin 2) :
    sourceCanonicalDenominator n eta i=sourceCanonicalDenominator n 0 i+eta^2*sourceStaticDenominatorSlope i := by
  unfold sourceCanonicalDenominator sourceStaticDenominatorSlope
  split_ifs <;> ring

private theorem static_denominator_ne (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 2) :
    sourceCanonicalDenominator n 0 i≠0 := by
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  have norm : (spatialSquare n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr spatial.ne'
  fin_cases i <;> norm_num [sourceCanonicalDenominator,two,fifteen,norm]

private theorem denominator_continuous (n : PhysicalMomentum) (i : Fin 2) :
    Continuous (fun eta : ℝ=>sourceCanonicalDenominator n (eta:ℂ) i) := by
  unfold sourceCanonicalDenominator
  split_ifs <;> fun_prop

private theorem inverse_static_limit (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 2) :
    Tendsto (fun eta : ℝ=>(sourceCanonicalDenominator n (eta:ℂ) i)⁻¹) (𝓝[>] 0)
      (𝓝 ((sourceCanonicalDenominator n 0 i)⁻¹)) :=
  ((denominator_continuous n i).continuousAt.inv₀ (static_denominator_ne n spatial i)).tendsto.mono_left nhdsWithin_le_nhds

/-- The actual even field denominator contributes no first-order static correction. -/
theorem sourceStaticInverse_slope_zero (n : PhysicalMomentum) (spatial : 0<spatialSquare n) (i : Fin 2) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)⁻¹*((sourceCanonicalDenominator n (eta:ℂ) i)⁻¹-
      (sourceCanonicalDenominator n 0 i)⁻¹)) (𝓝[>] 0) (𝓝 0) := by
  have scalar : Tendsto (fun eta : ℝ=>(eta:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have h:=(((scalar.neg.mul_const (sourceStaticDenominatorSlope i)).mul
    (inverse_static_limit n spatial i)).mul_const ((sourceCanonicalDenominator n 0 i)⁻¹))
  simp only [neg_zero,zero_mul] at h
  have away : ∀ᶠ eta : ℝ in 𝓝[>] 0,sourceCanonicalDenominator n (eta:ℂ) i≠0 :=
    ((denominator_continuous n i).continuousAt.eventually_ne (static_denominator_ne n spatial i)).filter_mono nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,away] with eta positive nonzero
  have equation:=sourceStaticDenominator_even n (eta:ℂ) i
  simp only [equation]
  have nonzeroExpanded : sourceCanonicalDenominator n 0 i+(eta:ℂ)^2*sourceStaticDenominatorSlope i≠0 := by
    rwa [←equation]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt positive),static_denominator_ne n spatial i,nonzeroExpanded]
  ring

/-- The genuine field denominator supplies an exact quadratic error gate on its generated legal domain. -/
theorem sourceStaticInverse_exact_error (n : PhysicalMomentum) (spatial : 0<spatialSquare n)
    (i : Fin 2) (eta : ℝ) (nonzero : sourceCanonicalDenominator n (eta:ℂ) i≠0) :
    ‖(sourceCanonicalDenominator n (eta:ℂ) i)⁻¹-(sourceCanonicalDenominator n 0 i)⁻¹‖=
      |eta|^2*‖sourceStaticDenominatorSlope i‖/
        (‖sourceCanonicalDenominator n (eta:ℂ) i‖*‖sourceCanonicalDenominator n 0 i‖) := by
  have equation:=sourceStaticDenominator_even n (eta:ℂ) i
  have difference : (sourceCanonicalDenominator n (eta:ℂ) i)⁻¹-(sourceCanonicalDenominator n 0 i)⁻¹=
      -((eta:ℂ)^2*sourceStaticDenominatorSlope i)*
        ((sourceCanonicalDenominator n (eta:ℂ) i)⁻¹*(sourceCanonicalDenominator n 0 i)⁻¹) := by
    field_simp [nonzero,static_denominator_ne n spatial i]
    rw [equation]
    ring
  rw [difference]
  simp only [norm_mul,norm_neg,norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Complete static simple coupling: actual B0, full B1 retainer cross terms, and the genuine time reader jet. -/
def sourceSimpleObserved (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℂ :=
  -sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)*
    ((sourceCanonicalDenominator n 0 0)⁻¹*sourceSlowRead (sourceNativeSimple q n l r) 0+
      (sourceCanonicalDenominator n 0 1)⁻¹*sourceSlowRead (sourceNativeSimple q n l r) 1)

private theorem scalar_laurent (eta D D0 X X2 : ℂ) (nonzero : eta≠0) :
    D*(eta*(X-eta⁻¹^2*X2))+(eta⁻¹*(D-D0))*X2=eta*(D*X-eta⁻¹^2*(D0*X2)) := by
  field_simp [nonzero]
  ring

/-- The same full-Gamma observation generates the actual simple static coefficient after its full double coefficient is removed. -/
theorem sourceSimpleObserved_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*(sourceAmputatedFieldVertex q pL pR a b
      (sourceJointFieldResidue q n (eta:ℂ) l r)-((eta:ℂ)⁻¹)^2*sourceStaticObserved q n l r a b pL pR))
      (𝓝[>] 0) (𝓝 (sourceSimpleObserved q n l r a b pL pR)) := by
  have simple (i : Fin 5) := (tendsto_pi_nhds.mp (sourceSlow_simple_generated q n l r)) i
  have channel (i : Fin 2) := ((inverse_static_limit n spatial i).mul (simple ⟨i.val,by omega⟩)).add
    ((sourceStaticInverse_slope_zero n spatial i).mul_const
      (sourceSlowRead (sourceStaticNative q n l r) ⟨i.val,by omega⟩))
  have h:=(tendsto_const_nhds (x:= -sourcePoleMaterialPairGap q pL pR a b*
    sourceOriginWeight (sourcePoleEulerInitial q pL pR a b))).mul ((channel 0).add (channel 1))
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [sourceStatic_causal_eventually n spatial,self_mem_nhdsWithin] with eta legal positive
  rw [sourceObservedField_tensor q n ⟨(eta:ℂ),legal⟩ l r a b pL pR nonrealL nonrealR]
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  rw [scalar_laurent _ _ _ _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt positive)),
    scalar_laurent _ _ _ _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt positive))]
  unfold sourceStaticObserved
  have index0 : (⟨(0:Fin 2).val,by omega⟩:Fin 5)=0 := rfl
  have index1 : (⟨(1:Fin 2).val,by omega⟩:Fin 5)=1 := rfl
  simp only [index0,index1]
  ring

/-- Both exact spatial source denominators survive into the coupling numerator. -/
theorem sourceSimpleObserved_spatial (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (spatial : 0<spatialSquare n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    sourceSimpleObserved q n l r a b pL pR=
      (-sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)/
        (rootTwo*rootFifteen*(spatialSquare n:ℂ)))*
      ((54/25:ℂ)*sourceSlowRead (sourceNativeSimple q n l r) 0+
       (335/12:ℂ)*sourceSlowRead (sourceNativeSimple q n l r) 1) := by
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  have norm : (spatialSquare n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr spatial.ne'
  unfold sourceSimpleObserved
  norm_num [sourceCanonicalDenominator]
  field_simp [two,fifteen,norm]

end LowEnergy.PreparationVacuumStaticSimpleCoupling
