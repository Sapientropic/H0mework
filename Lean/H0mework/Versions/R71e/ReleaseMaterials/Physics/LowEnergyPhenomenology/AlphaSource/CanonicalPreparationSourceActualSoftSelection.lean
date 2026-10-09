import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSoftNativeFrame
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColourPhysicalBalance

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumSoftPoleSelection
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumFullPoleContinuation PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumSharedPoleCarrier PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumWholeOrigin
open PreparationVacuumGaugeSourceInjection PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumPhysicalNativeColourReturn PreparationVacuumPhysicalConstraint114
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open Filter MeasureTheory Set
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open PreparationVacuumPropagationPencil SourcePropagationNativeActionHessian
open scoped Matrix BigOperators Topology
attribute [local irreducible] actualCurrent returnedCurrentTensor sourcePoleActionEuler

/-- Both material momenta and the independent Laplace frequency vary on the same eight-state carrier. -/
theorem returnedCurrentWindow_joint_continuous (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun p : (PhysicalMomentum  ×  PhysicalMomentum  ×  ℂ) =>returnedCurrentWindow q p.1 p.2.1 l r p.2.2 T):=by
  have args : Continuous (fun x : (PhysicalMomentum × PhysicalMomentum × ℂ) × ℝ=>(x.1.1,x.1.2.1,x.2)):=
    continuous_fst.fst.prodMk (continuous_fst.snd.fst.prodMk continuous_snd)
  apply continuous_pi
  intro i
  have whole:=(returnedCurrentTensor_continuous q i nonrealL nonrealR).comp args
  have entry:= (continuous_apply r).comp ((continuous_apply l).comp whole)
  have weight : Continuous (fun x : (PhysicalMomentum × PhysicalMomentum × ℂ) × ℝ=>laplaceWeight x.1.2.2 x.2):=by
    unfold laplaceWeight
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (weight.mul entry) 0 T

def actualSoftCurrent (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ) (e : scaleDomain) : Fin 289→ℂ:=
  returnedCurrentWindow q (sheetLeft e.val n 0) 0 l r
    (sheetLambda e.val (sourceSheet branch n unit e.val)) T

theorem actualSoftCurrent_same_carrier (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ) (e : scaleDomain) (i : Fin 289) :
    actualSoftCurrent q branch n unit l r T e i=
      (movingOverlap (sheetLeft e.val n 0)*
        (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>
          sheetCurrent q e.val (sourceSheet branch n unit e.val) n 0 a b T i)*
        (movingOverlap 0).conjTranspose) l r:=
  returnedCurrentWindow_tensor q _ 0 l r _ T i

theorem actualSoftCurrent_tendsto (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (actualSoftCurrent q branch n unit l r T) scaleApproach (𝓝 (actualCurrent q 0 0 l r 0 T)):=by
  have left : Tendsto (fun e : scaleDomain=>sheetLeft e.val n 0) scaleApproach (𝓝 (0:PhysicalMomentum)):=by
    have h:=(scaleVal_tendsto.pow 2).smul (tendsto_const_nhds (x:=n))
    simpa only [sheetLeft,zero_sub,zero_pow (by decide : 2≠0),zero_smul,neg_zero] using h.neg
  have lambda : Tendsto (fun e : scaleDomain=>sheetLambda e.val (sourceSheet branch n unit e.val))
      scaleApproach (𝓝 (0:ℂ)):=by
    have h:=tendsto_pi_nhds.mp (sourceRay_soft_limit branch n unit) 0
    simpa only [frequencyRay,physicalFrequencyMomentum,sheetLambda,sourceFrequency,mul_comm,Fin.cases_zero,Pi.zero_apply] using h
  have args:=left.prodMk_nhds ((tendsto_const_nhds (x:=(0:PhysicalMomentum))).prodMk_nhds lambda)
  have result:=(returnedCurrentWindow_joint_continuous q l r T nonrealL nonrealR).tendsto (0,0,0) |>.comp args
  unfold actualSoftCurrent
  simpa only [Function.comp_def,returnedCurrentWindow_zero] using result

/-- The original frequency residue, with its source-generated physical normalization. -/
def actualSoftResidue (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ) (e : scaleDomain) : Fin 289→ℂ:=
  (e.val:ℂ)^2 • nativeInsertion e.val (sourceSheet branch n unit e.val) n
    (sourceResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
      nativeModeForcing e.val (sourceSheet branch n unit e.val) n (actualSoftCurrent q branch n unit l r T e))

theorem actualSoftResidue_limit (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
      actualSoftResidue q branch n unit l r T e) scaleApproach
      (𝓝 (leadingNativeResponse branch (actualCurrent q 0 0 l r 0 T))):=by
  have limit:=softResponse_limit branch n unit _ _ (actualSoftCurrent_tendsto q branch n unit l r T nonrealL nonrealR)
  have same (e : scaleDomain) : (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
      actualSoftResidue q branch n unit l r T e=
      softResponse e.val (sourceSheet branch n unit e.val) n (actualSoftCurrent q branch n unit l r T e):=
    native_soft_normalization e.val _ n (ne_of_gt e.property.1) _
  simpa only [same] using limit

private theorem branchRead_origin (branch : Fin 2) (forcing : Fin 289→ℂ) :
    nativeBranchRead branch forcing=(slowFastFrame.transpose*ᵥ(fullNativeOrigin.transpose*ᵥforcing))
      (fiveIndex (residueIndex branch)):=by
  have active : fullKernelFrame.transpose*activeProjection=fullKernelFrame.transpose:=by
    have h:=congrArg Matrix.transpose fullKernel_active
    simpa only [Matrix.transpose_mul,activeProjection,projectionMatrix,Matrix.diagonal_transpose] using h
  have returned : fullKernelFrame.transpose*ᵥ(activeForcing 0 forcing)=fullNativeOrigin.transpose*ᵥforcing:=by
    unfold activeForcing
    rw [Matrix.mulVec_mulVec (originalReadback 0*ᵥforcing),active]
    simp only [fullNativeOrigin,Matrix.transpose_mul,originalReadback,neg_zero,Matrix.mulVec_mulVec]
  rw [nativeBranchRead,returned]

private theorem slowFast_weight (branch : Fin 2) (w : ℂ) :
    (slowFastFrame.transpose*ᵥ(Pi.single 0 w+Pi.single 1 w)) (fiveIndex (residueIndex branch))=
      if branch=0 then w else 0:=by
  simp only [Matrix.mulVec_add,Matrix.mulVec_single,Pi.add_apply]
  fin_cases branch <;>
    norm_num [residueIndex,fiveIndex,slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,
      Powers.value,coefficientValue,Matrix.single_apply,Matrix.transpose_apply,Fin.ext_iff,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]

theorem actualCurrent_branchRead (q : PhysicalResponsePoint) (branch : Fin 2) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    nativeBranchRead branch (actualCurrent q pL pR l r lambda T)=
      if branch=0 then actualOriginWeight q pL pR l r lambda T else 0:=by
  rw [branchRead_origin,actual_origin_kernel_read,slowFast_weight]
  rfl

theorem actualCurrent_leadingNativeResponse (q : PhysicalResponsePoint) (branch : Fin 2)
    (pL pR : PhysicalMomentum) (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    leadingNativeResponse branch (actualCurrent q pL pR l r lambda T)=
      if branch=0 then ((softCoefficient branch:ℂ)*actualOriginWeight q pL pR l r lambda T) • nativeBranchVector branch else 0:=by
  rw [leadingNativeResponse,actualCurrent_branchRead]
  split_ifs <;> simp

private theorem source_scale : ((gaugeScale/2:ℝ):ℂ)=(3/10:ℂ)*rootTwo:=by
  unfold rootTwo gaugeScale spinScale
  push_cast
  ring

/-- The surviving source weight is produced by the complete Gauss charge derivative, genuine material returns and configuration deviation. -/
def actualGaussWeight (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) : ℂ:=
  ∫t in (0:ℝ)..T,sourceConstraintChargeFirst q 0 0 l r t+
    Complex.I*sourceColourContactRemainderRead q 0 0 l r t-sourceDeviationJointRead q 0 0 l r t

theorem actualOriginWeight_completeGauss (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    actualOriginWeight q 0 0 l r 0 T=actualGaussWeight q l r T:=by
  have generated:=sourceActualModeWindow_completeGauss q 0 0 l r 0 T nonrealL nonrealR
  change ((gaugeScale/2:ℝ):ℂ)*(sourcePoleCurrentWindow q 0 0 l r 0 T 21-sourcePoleCurrentWindow q 0 0 l r 0 T 34)=_ at generated
  rw [source_scale] at generated
  unfold actualOriginWeight actualCurrent actualGaussWeight
  simpa only [laplaceWeight,zero_mul,neg_zero,Complex.exp_zero,one_mul] using generated

/-- The full native soft tensor selects its held-current coupling from the source itself, retaining both propagating field branches. -/
theorem actualSoftResidue_source_selection (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) •
      actualSoftResidue q branch n unit l r T e) scaleApproach
      (𝓝 (if branch=0 then ((softCoefficient branch:ℂ)*actualGaussWeight q l r T) • nativeBranchVector branch else 0)):=by
  have generated:=actualSoftResidue_limit q branch n unit l r T nonrealL nonrealR
  rw [actualCurrent_leadingNativeResponse,actualOriginWeight_completeGauss q l r T nonrealL nonrealR] at generated
  exact generated

def returnedSheetCurrent (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  returnedCurrentWindow q (sheetLeft epsilon n 0) 0 l r (sheetLambda epsilon s) T

def returnedSheetField (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  nativeResponse epsilon s n (returnedSheetCurrent q epsilon s n l r T)

private theorem returnedSheetCurrent_continuous (q : PhysicalResponsePoint) (epsilon : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun s=>returnedSheetCurrent q epsilon s n l r T):=by
  have frequency : Continuous (fun s : ℝ=>sheetLambda epsilon s):=by
    unfold sheetLambda sourceFrequency
    fun_prop
  have path : Continuous (fun s : ℝ=>(sheetLeft epsilon n 0,(0:PhysicalMomentum),sheetLambda epsilon s)):=
    continuous_const.prodMk (continuous_const.prodMk frequency)
  unfold returnedSheetCurrent
  exact (returnedCurrentWindow_joint_continuous q l r T nonrealL nonrealR).comp path

private theorem nativeResponse_pole_limit (e : scaleDomain) (s : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay e.val s n∈complementRegular) (forcing : ℝ→Fin 289→ℂ)
    (continuous : ContinuousAt forcing s)
    (pole : Tendsto (fun t=>((t-s:ℝ):ℂ) • (extendedTensor e.val t n)⁻¹) (𝓝[≠] s)
      (𝓝 (sourceResidue e.val s n))) :
    Tendsto (fun t=>((t-s:ℝ):ℂ) • nativeResponse e.val t n (forcing t)) (𝓝[≠] s)
      (𝓝 (nativeInsertion e.val s n (sourceResidue e.val s n*ᵥnativeModeForcing e.val s n (forcing s)))):=by
  have path : Tendsto (fun t=>(t,forcing t)) (𝓝[≠] s) (𝓝 (s,forcing s)):=
    (tendsto_id.prodMk_nhds continuous.tendsto).mono_left nhdsWithin_le_nhds
  have reader := (nativeModeForcing_continuous_at e.val s n regular (forcing s)).tendsto.comp path
  have multiply : Continuous (fun pair : Matrix (Fin 5) (Fin 5) ℂ × (Fin 5→ℂ)=>pair.1*ᵥpair.2):=
    continuous_fst.matrix_mulVec continuous_snd
  have modal := (multiply.tendsto (sourceResidue e.val s n,nativeModeForcing e.val s n (forcing s))).comp (pole.prodMk_nhds reader)
  have insertion := (nativeInsertion_continuous_at e.val s n regular _).tendsto.comp
    ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds modal)
  have background := (nativeRegularResponse_continuous_at e.val s n regular (forcing s)).tendsto.comp path
  have scale : Tendsto (fun t : ℝ=>((t-s:ℝ):ℂ)) (𝓝[≠] s) (𝓝 (0:ℂ)):=by
    have h : Continuous (fun t : ℝ=>((t-s:ℝ):ℂ)):=by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using
      (h.tendsto s).mono_left (nhdsWithin_le_nhds : 𝓝[≠] s≤𝓝 s)
  have result:=insertion.add (scale.smul background)
  simp only [Function.comp_apply,id_eq,zero_smul,add_zero] at result
  apply result.congr'
  filter_upwards [] with t
  simp only [nativeResponse,smul_add,Matrix.smul_mulVec,nativeInsertion_smul]


theorem returnedSheetField_residue (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun t=>((t-sourceSheet branch n unit e.val:ℝ):ℂ) • returnedSheetField q e.val t n l r T)
        (𝓝[≠] (sourceSheet branch n unit e.val))
        (𝓝 (nativeInsertion e.val (sourceSheet branch n unit e.val) n
          (sourceResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
            nativeModeForcing e.val (sourceSheet branch n unit e.val) n (actualSoftCurrent q branch n unit l r T e)))):=by
  filter_upwards [sourceSheet_inverse_residue branch n unit,
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e pole bounds
  have inside : |sourceSheet branch n unit e.val|≤1:=by
    apply abs_le.mpr
    split_ifs at bounds <;> constructor <;> linarith
  have regular : frequencyRay e.val (sourceSheet branch n unit e.val) n∈complementRegular:=
    (rayPoint e ⟨sourceSheet branch n unit e.val,inside⟩ n (unit_direction_bound n unit)).property
  exact nativeResponse_pole_limit e _ n regular _
    (returnedSheetCurrent_continuous q e.val n l r T nonrealL nonrealR).continuousAt pole

theorem returnedSheetField_frequency_residue (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun omega=>((omega-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        returnedSheetField q e.val (omega/e.val^2) n left right T)
        (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
        (𝓝 (actualSoftResidue q branch n unit left right T e)):=by
  filter_upwards [returnedSheetField_residue q branch n unit left right T nonrealL nonrealR] with e limit
  let s:=sourceSheet branch n unit e.val
  let a:=e.val^2
  have nonzero : a≠0:=pow_ne_zero 2 e.property.1.ne'
  have divided : a*s/a=s:=by field_simp
  have reparam : Tendsto (fun omega : ℝ=>omega/a) (𝓝[≠] (a*s)) (𝓝[≠] s):=by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun omega : ℝ=>omega/a) (𝓝[≠] (a*s)) (𝓝 ((a*s)/a)):=
        ((continuous_id.div_const a).tendsto (a*s)).mono_left nhdsWithin_le_nhds
      simpa only [divided] using h
    · filter_upwards [self_mem_nhdsWithin] with omega outside
      change omega/a≠s
      intro equal
      apply outside
      change omega=a*s
      exact ((div_eq_iff nonzero).mp equal).trans (mul_comm s a)
  have result : Tendsto (fun omega : ℝ=>(a:ℂ) •
      (((omega/a-s:ℝ):ℂ) • returnedSheetField q e.val (omega/a) n left right T)) (𝓝[≠] (a*s))
      (𝓝 ((a:ℂ) • nativeInsertion e.val s n (sourceResidue e.val s n*ᵥnativeModeForcing e.val s n (actualSoftCurrent q branch n unit left right T e)))):=tendsto_const_nhds.smul (limit.comp reparam)
  unfold actualSoftResidue
  rw [←Complex.ofReal_pow]
  apply result.congr'
  filter_upwards [] with omega
  have scalar : a*(omega/a-s)=omega-a*s:=by field_simp
  rw [smul_smul,←Complex.ofReal_mul,scalar]
  rfl

/-- The selected source tensor is the uncleared original full field on its generated punctured domain. -/
theorem returnedSheetField_original (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,∀ᶠ t in 𝓝[≠] (sourceSheet branch n unit e.val),
      ∃point : regularSource,point.val=frequencyRay e.val t n ∧
        returnedSheetField q e.val t n left right T=
          sourceField point (returnedSheetCurrent q e.val t n left right T):=by
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_simple branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_equation branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e simple equation bounds
  let center:=sourceSheet branch n unit e.val
  have inside : |center|<1:=by
    apply abs_lt.mpr
    change (if branch=0 then (1/2:ℝ) else (4/5:ℝ))<center ∧ center<(if branch=0 then (2/3:ℝ) else (9/10:ℝ)) at bounds
    split_ifs at bounds <;> constructor <;> linarith
  have slopes:=simple.2.tendsto_slope.eventually_ne simple.1
  have interval := ((continuous_abs.continuousAt : ContinuousAt (fun t : ℝ=>|t|) center).eventually_lt_const inside).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
  filter_upwards [slopes,interval] with t slope insideT
  have realNonzero : physicalDeterminant e.val t n≠0:=by
    intro zero
    apply slope
    simp only [slope_def_module,zero,equation,sub_self,smul_zero]
  let s : slopeDomain:=⟨t,insideT.le⟩
  have regular : IsUnit (normalizedEffective e s n (unit_direction_bound n unit)).det:=by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    have same:=extendedTensor_actual e s n (unit_direction_bound n unit)
    rw [←same] at zero
    apply realNonzero
    exact congrArg Complex.re zero
  exact ⟨dynamicPoint e s n (unit_direction_bound n unit) regular,rfl,
    nativeResponse_original e s n (unit_direction_bound n unit) regular _⟩


set_option backward.isDefEq.respectTransparency false in
private theorem read_transfer (M : Matrix (Fin 289) (Fin 289) ℂ)
    (U V : Matrix RestStateIndex RestStateIndex ℂ) (F : RestStateIndex→RestStateIndex→Fin 289→ℂ)
    (l r : RestStateIndex) :
    M*ᵥ(fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>F a b i)*V) l r)=fun i=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>(M*ᵥF a b) i)*V) l r:=by
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

def returnedSheetCosource (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=fun i=>
  (movingOverlap (sheetLeft epsilon n 0)*
    (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>sheetCosource q epsilon s n 0 a b T i)*
    (movingOverlap 0).conjTranspose) l r

theorem returnedSheetCurrent_ward (q : PhysicalResponsePoint) (epsilon s : ℝ) (n : PhysicalMomentum)
    (l r : RestStateIndex) (T : ℝ) :
    originalReadback (frequencyRay epsilon s n)*ᵥreturnedSheetCurrent q epsilon s n l r T=
      returnedSheetCosource q epsilon s n l r T:=by
  have current : returnedSheetCurrent q epsilon s n l r T=fun i=>
      (movingOverlap (sheetLeft epsilon n 0)*
        (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>sheetCurrent q epsilon s n 0 a b T i)*
        (movingOverlap 0).conjTranspose) l r:=by
    funext i
    exact returnedCurrentWindow_tensor q _ 0 l r _ T i
  rw [current,read_transfer]
  simp only [sheetCurrent_ward]
  rfl

/-- All nine source constraints survive the common-carrier return and the physical sheet construction. -/
theorem returnedSheetField_whole (q : PhysicalResponsePoint) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,∀ᶠ t in 𝓝[≠] (sourceSheet branch n unit e.val),
      nativeFourierHessian nativeHessian (frequencyRay e.val t n)*ᵥreturnedSheetField q e.val t n l r T=
        returnedSheetCurrent q e.val t n l r T-originalRowLift (frequencyRay e.val t n)*ᵥ
          (nullProjection*ᵥreturnedSheetCosource q e.val t n l r T):=by
  filter_upwards [returnedSheetField_original q branch n unit l r T] with e near
  filter_upwards [near] with t result
  obtain ⟨point,coordinate,field⟩:=result
  rw [field,SourcePropagationNativeActionHessian.nativeActionFourierHessian_original,←coordinate,
    original_forced_field,coordinate,sourceCompatibility,returnedSheetCurrent_ward]


end LowEnergy.PreparationVacuumSoftPoleSelection
