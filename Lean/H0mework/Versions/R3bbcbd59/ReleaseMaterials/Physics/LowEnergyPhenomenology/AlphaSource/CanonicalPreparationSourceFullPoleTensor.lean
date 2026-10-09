import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceReaderMomentum

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullPoleContinuation
open PreparationVacuumActionFieldLift
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumMixedPrincipal
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator
attribute [local irreducible] sourcePoleRead sourcePoleActionEuler jointResolvent physicalTime rawReader
  PreparationVacuumOriginalGreenFeedback.sourceField staticNativeField actualCurrent

/-- Full amplitude-zero material kernel, including all native readers and both independent material legs. -/
def actualJointKernel (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) : H→L[ℂ] H:=
  physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0*rawReader (fieldUnit i) pR q.F 0*
    jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

theorem actualJointKernel_original (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0=actualJointKernel q pL pR t i:=by
  have same : pR+(pL-pR)=pL:=by abel
  unfold fiveKernel actualJointKernel
  rw [same]

def actualCurrentTensor (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    Matrix RestStateIndex RestStateIndex ℂ:=fun l r=>sourcePoleActionEuler q pL pR l r 0 t i

def returnedCurrentTensor (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    Matrix RestStateIndex RestStateIndex ℂ:= -sourceTensor q.epsilon q.precision 0 0 (actualJointKernel q pL pR t i)

theorem returnedCurrentTensor_actual (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    returnedCurrentTensor q pL pR t i=
      movingOverlap pL*actualCurrentTensor q pL pR t i*(movingOverlap pR).conjTranspose:=by
  have actual : actualCurrentTensor q pL pR t i= -sourceTensor q.epsilon q.precision pL pR (actualJointKernel q pL pR t i):=by
    ext l r
    exact (sourcePoleActionEuler_source q pL pR l r t i).trans
      (congrArg (fun A : H→L[ℂ] H=> -sourcePoleRead q.epsilon q.precision pL pR l r A)
        (actualJointKernel_original q pL pR t i))
  rw [actual,mul_neg,neg_mul,sourceTensor_same_carrier]
  rfl

theorem actualJointKernel_continuous (q : PhysicalResponsePoint) (i : Fin 289)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>actualJointKernel q x.1 x.2.1 x.2.2 i):=by
  have leftInput : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>(x.1,-x.2.2)):=
    continuous_fst.prodMk continuous_snd.snd.neg
  have rightInput : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>(x.2.1,x.2.2)):=
    continuous_snd.fst.prodMk continuous_snd.snd
  have leftTime:=(actualJointTime_continuous q.F).comp leftInput
  have rightTime:=(actualJointTime_continuous q.F).comp rightInput
  have leftR:=(actualJointResolvent_continuous q.F q.z nonrealL).comp
    (continuous_fst : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>x.1))
  have rightR:=(actualJointResolvent_continuous q.F q.w nonrealR).comp
    (continuous_snd.fst : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>x.2.1))
  have reader:=(rawReader_momentum_continuous (fieldUnit i) q.F).comp
    (continuous_snd.fst : Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>x.2.1))
  exact (((leftTime.mul leftR).mul reader).mul rightR).mul rightTime

theorem returnedCurrentTensor_continuous (q : PhysicalResponsePoint) (i : Fin 289)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>returnedCurrentTensor q x.1 x.2.1 x.2.2 i):=by
  apply continuous_pi
  intro l
  apply continuous_pi
  intro r
  exact ((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.comp
    (actualJointKernel_continuous q i nonrealL nonrealR)).neg

def returnedCurrentWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (T : ℝ) : Fin 289→ℂ:=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*returnedCurrentTensor q pL pR t i l r

theorem returnedCurrentWindow_actual (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    returnedCurrentWindow q pL pR l r lambda T i=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (movingOverlap pL*actualCurrentTensor q pL pR t i*(movingOverlap pR).conjTranspose) l r:=by
  simp only [returnedCurrentWindow,returnedCurrentTensor_actual]

private def matrixTransfer (U V : Matrix RestStateIndex RestStateIndex ℂ) (l r : RestStateIndex) :
    Matrix RestStateIndex RestStateIndex ℂ→ₗ[ℂ] ℂ where
  toFun M:=(U*M*V) l r
  map_add' A B:=by simp only [mul_add,add_mul,Matrix.add_apply]
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,Matrix.smul_apply,smul_eq_mul,RingHom.id_apply]

/-- Exact bilateral return of the original integrated current, before taking any field limit. -/
theorem returnedCurrentWindow_tensor (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    returnedCurrentWindow q pL pR l r lambda T i=
      (movingOverlap pL*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCurrent q pL pR a b lambda T i)*(movingOverlap pR).conjTranspose) l r:=by
  let f : ℝ→Matrix RestStateIndex RestStateIndex ℂ:=fun t=>laplaceWeight lambda t • actualCurrentTensor q pL pR t i
  have current : Continuous (fun t : ℝ=>actualCurrentTensor q pL pR t i):=by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    exact sourcePoleActionEuler_continuous q pL pR a b i
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  have integrable : IntervalIntegrable f volume (0:ℝ) T:= (weight.smul current).intervalIntegrable (0:ℝ) T
  have returned : (∫t in (0:ℝ)..T,f t)=(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCurrent q pL pR a b lambda T i):=by
    ext a b
    have h:=(matrixTransfer 1 1 a b).toContinuousLinearMap.intervalIntegral_comp_comm integrable
    simp only [matrixTransfer,one_mul,mul_one] at h
    change (∫t in (0:ℝ)..T,laplaceWeight lambda t*actualCurrentTensor q pL pR t i a b)=
      (∫t in (0:ℝ)..T,f t) a b at h
    unfold actualCurrent sourcePoleCurrentWindow
    exact h.symm
  have h:=(matrixTransfer (movingOverlap pL) (movingOverlap pR).conjTranspose l r).toContinuousLinearMap.intervalIntegral_comp_comm integrable
  change (∫t in (0:ℝ)..T,matrixTransfer (movingOverlap pL) (movingOverlap pR).conjTranspose l r (f t))=
    matrixTransfer (movingOverlap pL) (movingOverlap pR).conjTranspose l r (∫t in (0:ℝ)..T,f t) at h
  rw [returned] at h
  simpa only [f,map_smul,smul_eq_mul,matrixTransfer,LinearMap.coe_mk,AddHom.coe_mk,←returnedCurrentWindow_actual] using h

theorem returnedCurrentWindow_continuous (q : PhysicalResponsePoint) (l r : RestStateIndex) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>returnedCurrentWindow q p.1 p.2 l r lambda T):=by
  have args : Continuous (fun x : (PhysicalMomentum×PhysicalMomentum)×ℝ=>(x.1.1,x.1.2,x.2)):=
    continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  apply continuous_pi
  intro i
  have whole:=(returnedCurrentTensor_continuous q i nonrealL nonrealR).comp args
  have entry:= (continuous_apply r).comp ((continuous_apply l).comp whole)
  have weight : Continuous (fun x : (PhysicalMomentum×PhysicalMomentum)×ℝ=>laplaceWeight lambda x.2):=by
    unfold laplaceWeight
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (weight.mul entry) 0 T

theorem returnedCurrentWindow_zero (q : PhysicalResponsePoint) (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    returnedCurrentWindow q 0 0 l r lambda T=actualCurrent q 0 0 l r lambda T:=by
  funext i
  simp only [returnedCurrentWindow_actual,movingOverlap_zero,Matrix.conjTranspose_one,one_mul,mul_one]
  unfold actualCurrent sourcePoleCurrentWindow actualCurrentTensor
  rfl

private theorem staticGreen_residue :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • sourceGreen (staticRegularPoint κ)) staticApproach
      (𝓝 (fullNativeOrigin*staticInverse*fullNativeOrigin.transpose)):=by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have column:=(continuous_apply i).continuousAt.tendsto.comp (staticNativeField_residue (Pi.single j 1))
  simp only [Function.comp_def,Pi.smul_apply,smul_eq_mul,staticNativeField,PreparationVacuumOriginalGreenFeedback.sourceField,
    staticResidue,Matrix.mulVec_mulVec] at column
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,mul_assoc] using column

private theorem varyingField_residue (forcing : staticDomain→Fin 289→ℂ) (limit : Fin 289→ℂ)
    (generated : Tendsto forcing staticApproach (𝓝 limit)) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • staticNativeField κ (forcing κ)) staticApproach
      (𝓝 (staticResidue limit)):=by
  have result:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    (staticGreen_residue.prodMk_nhds generated)
  simpa only [Function.comp_def,Matrix.smul_mulVec,staticNativeField,PreparationVacuumOriginalGreenFeedback.sourceField,
    staticResidue,Matrix.mulVec_mulVec,mul_assoc] using result

/-- The left source momentum is generated by the same physical transfer used by the static field point. -/
def actualAxisWindow (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) : Fin 289→ℂ:=
  returnedCurrentWindow q (sourceAxisLeft 0 κ.val) 0 l r 0 T

theorem actualAxisWindow_tendsto (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (actualAxisWindow q l r T) staticApproach (𝓝 (actualCurrent q 0 0 l r 0 T)):=by
  have left : Tendsto (fun κ : staticDomain=>sourceAxisLeft 0 κ.val) staticApproach (𝓝 (0:PhysicalMomentum)):=by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Tendsto (fun κ : staticDomain=> (0:ℝ)-κ.val) staticApproach (𝓝 (0:ℝ))
      simpa only [zero_sub,neg_zero] using staticVal_tendsto.neg
    · change Tendsto (fun _ : staticDomain=> (0:ℝ)-0) staticApproach (𝓝 0)
      simpa only [sub_self] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=staticApproach))
    · change Tendsto (fun _ : staticDomain=> (0:ℝ)-0) staticApproach (𝓝 0)
      simpa only [sub_self] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=staticApproach))
  have inputs:=left.prodMk_nhds (tendsto_const_nhds (x:=(0:PhysicalMomentum)))
  have result:=(returnedCurrentWindow_continuous q l r 0 T nonrealL nonrealR).continuousAt.tendsto.comp inputs
  unfold actualAxisWindow
  simpa only [Function.comp_def,returnedCurrentWindow_zero] using result

/-- Original uncleared full field, with the actual transferred material current returned to its common eight-state carrier. -/
def actualAxisField (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) : Fin 289→ℂ:=
  staticNativeField κ (actualAxisWindow q l r T κ)

theorem actualAxisField_whole (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) :
    originalJacobi (staticMomentum κ.val)*ᵥactualAxisField q l r T κ=
      actualAxisWindow q l r T κ-originalRowLift (staticMomentum κ.val)*ᵥ
        (nullProjection*ᵥ(originalReadback (staticMomentum κ.val)*ᵥactualAxisWindow q l r T κ)):=
  staticNativeField_whole κ (actualAxisWindow q l r T κ)

theorem actualAxisField_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • actualAxisField q l r T κ) staticApproach
      (𝓝 (staticResidue (actualCurrent q 0 0 l r 0 T))):=
  varyingField_residue _ _ (actualAxisWindow_tendsto q l r T nonrealL nonrealR)

theorem actualAxisField_coupled_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • actualAxisField q l r T κ) staticApproach
      (𝓝 (fullNativeOrigin*ᵥ
        (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*actualOriginWeight q 0 0 l r 0 T)+
         Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*actualOriginWeight q 0 0 l r 0 T)))):=by
  simpa only [actualCurrent_staticResidue] using actualAxisField_residue q l r T nonrealL nonrealR

end LowEnergy.PreparationVacuumFullPoleContinuation
