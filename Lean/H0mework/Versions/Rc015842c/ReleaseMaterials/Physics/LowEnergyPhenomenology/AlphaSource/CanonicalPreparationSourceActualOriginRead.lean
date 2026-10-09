import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeReaderJet

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeSlowCoupling
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumCausalPoleResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumSharedPoleCarrier PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumOriginalGreenFeedback
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourcePoleCurrentHalf sourcePoleCurrentWindow fullNativeOrigin

def sourceOriginWeight (f : Fin 289→ℂ) : ℂ := (3/10:ℂ)*rootTwo*(f 21-f 34)
def sourceOriginPair (w : ℂ) : Fin 289→ℂ := Pi.single 0 w+Pi.single 1 w

private theorem origin_pair_continuous : Continuous sourceOriginPair := by
  apply continuous_pi
  intro i
  simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

private theorem origin_weight_continuous : Continuous sourceOriginWeight := by
  unfold sourceOriginWeight
  fun_prop

/-- The original finite-window source identity returns to the actual half-axis current. -/
theorem sourceActualHalf_origin (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (positive : 0<lambda.re) :
    fullNativeOrigin.transpose*ᵥsourcePoleCurrentHalf q pL pR l r lambda=
      sourceOriginPair (sourceOriginWeight (sourcePoleCurrentHalf q pL pR l r lambda)) := by
  have current : Tendsto (fun T=>actualCurrent q pL pR l r lambda T) atTop
      (𝓝 (sourcePoleCurrentHalf q pL pR l r lambda)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact sourcePoleCurrentWindow_halfAxis q pL pR l r lambda positive i
  have read : Continuous (fun f : Fin 289→ℂ=>fullNativeOrigin.transpose*ᵥf) :=
    continuous_const.matrix_mulVec continuous_id
  have first:=(read.tendsto _).comp current
  have second:=((origin_pair_continuous.comp origin_weight_continuous).tendsto _).comp current
  have same : (fun T=>fullNativeOrigin.transpose*ᵥactualCurrent q pL pR l r lambda T)=
      (fun T=>sourceOriginPair (sourceOriginWeight (actualCurrent q pL pR l r lambda T))) := by
    funext T
    exact actual_origin_kernel_read q pL pR l r lambda T
  simpa only [Function.comp_def,same] using tendsto_nhds_unique first (by simpa only [Function.comp_def,←same] using second)

private theorem read_transfer (M : Matrix (Fin 289) (Fin 289) ℂ)
    (U V : Matrix RestStateIndex RestStateIndex ℂ) (F : RestStateIndex→RestStateIndex→Fin 289→ℂ)
    (l r : RestStateIndex) :
    M*ᵥ(fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b i)*V) l r)=
      fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>(M*ᵥF a b) i)*V) l r := by
  funext i
  simp only [Matrix.mulVec,Matrix.mul_apply,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pair_transfer (U V : Matrix RestStateIndex RestStateIndex ℂ)
    (F : RestStateIndex→RestStateIndex→Fin 289→ℂ) (l r : RestStateIndex) :
    (fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>
      sourceOriginPair (sourceOriginWeight (F a b)) i)*V) l r)=
      sourceOriginPair (sourceOriginWeight (fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b i)*V) l r)) := by
  have weighted : U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>sourceOriginWeight (F a b))*V=
      ((3/10:ℂ)*rootTwo) • (U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b 21)*V-
        U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b 34)*V) := by
    change U*(((3/10:ℂ)*rootTwo) • ((show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b 21)-
      (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b 34)))*V=_
    simp only [mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul]
  have weights:=congrFun (congrFun weighted l) r
  simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul] at weights
  funext i
  by_cases h0 : i=0
  · have h1 : i≠1 := by omega
    simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply,if_pos h0,if_neg h1,add_zero]
    exact weights
  · by_cases h1 : i=1
    · simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply,if_neg h0,if_pos h1,zero_add]
      exact weights
    · simp only [sourceOriginPair,Pi.add_apply,Pi.single_apply,if_neg h0,if_neg h1,add_zero]
      change ((U*(0 : Matrix RestStateIndex RestStateIndex ℂ))*V) l r=0
      simp only [mul_zero,zero_mul,Matrix.zero_apply]

/-- The original read and the common eight-state return commute on the same actual current. -/
theorem sourceReturnedHalf_origin (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (positive : 0<lambda.re) :
    fullNativeOrigin.transpose*ᵥreturnedHalfCurrent q pL pR l r lambda=
      sourceOriginPair (sourceOriginWeight (returnedHalfCurrent q pL pR l r lambda)) := by
  unfold returnedHalfCurrent
  rw [read_transfer]
  simp only [sourceActualHalf_origin q pL pR _ _ lambda positive]
  exact pair_transfer _ _ _ l r

private theorem pair_smul (z w : ℂ) : z • sourceOriginPair w=sourceOriginPair (z*w) := by
  funext i
  simp only [sourceOriginPair,Pi.smul_apply,Pi.add_apply,Pi.single_apply]
  split_ifs <;> simp only [smul_eq_mul,mul_add,mul_zero]

/-- The first-order origin forcing is generated from the two actual gauge entries. -/
def sourceOriginCurrentResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  sourceOriginPair ((3/10:ℂ)*rootTwo*
    (sourceGaugeCurrentResidue q n zeta l r 1 0-sourceGaugeCurrentResidue q n zeta l r 2 1))

theorem sourceActualOrigin_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>fullNativeOrigin.transpose*ᵥ
      ((d:ℂ) • returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta)))
      (𝓝[>] 0) (𝓝 (sourceOriginCurrentResidue q n zeta l r)) := by
  have first:=sourceGaugeCurrent_residue q n zeta positive l r 1 0 nonrealL nonrealR
  have second:=sourceGaugeCurrent_residue q n zeta positive l r 2 1 nonrealL nonrealR
  have weight:=(tendsto_const_nhds (x:=((3/10:ℂ)*rootTwo))).mul (first.sub second)
  have result:=origin_pair_continuous.continuousAt.tendsto.comp weight
  apply result.congr'
  filter_upwards [self_mem_nhdsWithin] with d positiveDelta
  have positiveLambda : 0<((d:ℂ)*zeta).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using mul_pos positiveDelta positive
  simp only [Function.comp_def]
  rw [Matrix.mulVec_smul,sourceReturnedHalf_origin q _ _ l r _ positiveLambda,pair_smul]
  congr 1
  change (3/10:ℂ)*rootTwo*((d:ℂ)*_-(d:ℂ)*_)=(d:ℂ)*((3/10:ℂ)*rootTwo*(_-_))
  have slot21 : PreparationVacuumMixedFieldReturn.gaugeSlot 1 0=(21:Fin 289) := rfl
  have slot34 : PreparationVacuumMixedFieldReturn.gaugeSlot 2 1=(34:Fin 289) := rfl
  rw [slot21,slot34]
  ring

end LowEnergy.PreparationVacuumNativeSlowCoupling
