import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeSchurResponse

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumNativePoleTensor
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet CanonicalGradedSpatialSource
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn PreparationVacuumElectromagneticIdentity
open PreparationVacuumGaugeSourceInjection
open SourcePropagationNativeActionHessian
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval

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
  have multiply : Continuous (fun pair : Matrix (Fin 5) (Fin 5) ℂ×(Fin 5→ℂ)=>pair.1*ᵥpair.2):=
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

/-- Material momenta remain the actual source pair. Frequency is the independent physical field read. -/
def sheetLeft (epsilon : ℝ) (n p : PhysicalMomentum) : PhysicalMomentum:=p-epsilon^2 • n

def sheetLambda (epsilon s : ℝ) : ℂ:= -Complex.I*(sourceFrequency epsilon s:ℂ)

def sheetCurrent (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  actualCurrent q (sheetLeft epsilon n p) p left right (sheetLambda epsilon s) T

def sheetCosource (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  actualCosource q (sheetLeft epsilon n p) p left right (sheetLambda epsilon s) T

def actualSheetField (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  nativeResponse epsilon s n (sheetCurrent q epsilon s n p left right T)

def actualSheetResidue (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  nativeInsertion epsilon s n (sourceResidue epsilon s n*ᵥ
    nativeModeForcing epsilon s n (sheetCurrent q epsilon s n p left right T))

private theorem actualCurrent_lambda_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Continuous (fun lambda=>actualCurrent q pL pR left right lambda T):=by
  apply continuous_pi
  intro i
  have weight : Continuous (fun x : ℂ×ℝ=>laplaceWeight x.1 x.2):=by unfold laplaceWeight;fun_prop
  have current : Continuous (fun x : ℂ×ℝ=>sourcePoleActionEuler q pL pR left right 0 x.2 i):=
    (sourcePoleActionEuler_continuous q pL pR left right i).comp continuous_snd
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (weight.mul current) 0 T

theorem sheetCurrent_continuous (q : PhysicalResponsePoint) (epsilon : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Continuous (fun s=>sheetCurrent q epsilon s n p left right T):=
  (actualCurrent_lambda_continuous q (sheetLeft epsilon n p) p left right T).comp
    (by unfold sheetLambda sourceFrequency;fun_prop)

theorem sheetMomentum_actual (epsilon s : ℝ) (n p : PhysicalMomentum) :
    actualMomentum (sheetLeft epsilon n p) p (sheetLambda epsilon s)=frequencyRay epsilon s n:=by
  have transfer : sourcePhysicalTransfer (sheetLeft epsilon n p) p=epsilon^2 • n:=by
    unfold sourcePhysicalTransfer sheetLeft
    abel
  rw [actualMomentum,transfer]
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change -Complex.I*((epsilon^2*s:ℝ):ℂ)= -Complex.I*((s*epsilon^2:ℝ):ℂ)
    rw [mul_comm (epsilon^2) s]
  · rfl

theorem sheetCurrent_ward (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) :
    originalReadback (frequencyRay epsilon s n)*ᵥsheetCurrent q epsilon s n p left right T=
      sheetCosource q epsilon s n p left right T:=by
  rw [←sheetMomentum_actual epsilon s n p]
  exact actual_current_ward q (sheetLeft epsilon n p) p left right (sheetLambda epsilon s) T

/-- Same actual quantum current produces the full289 native pole residue, with no supplied forcing limit. -/
theorem actualSheetField_residue (q : PhysicalResponsePoint) (branch : Fin 2) (n p : PhysicalMomentum)
    (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun t=>((t-sourceSheet branch n unit e.val:ℝ):ℂ) • actualSheetField q e.val t n p left right T)
        (𝓝[≠] (sourceSheet branch n unit e.val))
        (𝓝 (actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p left right T)):=by
  filter_upwards [sourceSheet_inverse_residue branch n unit,
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e pole bounds
  have inside : |sourceSheet branch n unit e.val|≤1:=by
    apply abs_le.mpr
    split_ifs at bounds <;> constructor <;> linarith
  have regular : frequencyRay e.val (sourceSheet branch n unit e.val) n∈complementRegular:=
    (rayPoint e ⟨sourceSheet branch n unit e.val,inside⟩ n (unit_direction_bound n unit)).property
  exact nativeResponse_pole_limit e _ n regular _ (sheetCurrent_continuous q e.val n p left right T).continuousAt pole

/-- The actual-current pole field is the original uncleared Green on its source-generated punctured domain. -/
theorem actualSheetField_original (q : PhysicalResponsePoint) (branch : Fin 2) (n p : PhysicalMomentum)
    (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,∀ᶠ t in 𝓝[≠] (sourceSheet branch n unit e.val),
      ∃point : regularSource,point.val=frequencyRay e.val t n ∧
        actualSheetField q e.val t n p left right T=
          sourceField point (sheetCurrent q e.val t n p left right T):=by
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

/-- The same complete physical pole response retains all nine actual quantum source constraints. -/
theorem actualSheetField_whole (q : PhysicalResponsePoint) (branch : Fin 2) (n p : PhysicalMomentum)
    (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,∀ᶠ t in 𝓝[≠] (sourceSheet branch n unit e.val),
      nativeFourierHessian nativeHessian (frequencyRay e.val t n)*ᵥactualSheetField q e.val t n p left right T=
        sheetCurrent q e.val t n p left right T-originalRowLift (frequencyRay e.val t n)*ᵥ
          (nullProjection*ᵥsheetCosource q e.val t n p left right T):=by
  filter_upwards [actualSheetField_original q branch n p unit left right T] with e near
  filter_upwards [near] with t result
  obtain ⟨point,coordinate,field⟩:=result
  rw [field,nativeActionFourierHessian_original,←coordinate,original_forced_field,coordinate,sourceCompatibility,
    sheetCurrent_ward]

def actualFrequencyResidue (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 289→ℂ:=
  ((epsilon^2:ℝ):ℂ) • actualSheetResidue q epsilon s n p left right T

/-- The complete original quantum-current response has this residue in the original Fourier frequency. -/
theorem actualSheetField_frequency_residue (q : PhysicalResponsePoint) (branch : Fin 2) (n p : PhysicalMomentum)
    (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun omega=>((omega-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        actualSheetField q e.val (omega/e.val^2) n p left right T)
        (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
        (𝓝 (actualFrequencyResidue q e.val (sourceSheet branch n unit e.val) n p left right T)):=by
  filter_upwards [actualSheetField_residue q branch n p unit left right T] with e limit
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
      (((omega/a-s:ℝ):ℂ) • actualSheetField q e.val (omega/a) n p left right T)) (𝓝[≠] (a*s))
      (𝓝 ((a:ℂ) • actualSheetResidue q e.val s n p left right T)):=tendsto_const_nhds.smul (limit.comp reparam)
  apply result.congr'
  filter_upwards [] with omega
  have scalar : a*(omega/a-s)=omega-a*s:=by field_simp
  rw [smul_smul,←Complex.ofReal_mul,scalar]
  rfl

end LowEnergy.PreparationVacuumNativePoleTensor
