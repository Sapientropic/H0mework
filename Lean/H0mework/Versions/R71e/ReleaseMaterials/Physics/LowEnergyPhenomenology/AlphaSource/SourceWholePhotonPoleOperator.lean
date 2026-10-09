import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativePolarizationScatteringTensor

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhotonFluxReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativePoleTensor PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationPhysicalVoltageCompleteReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumWholeOrigin
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] originalJacobi originalChange originalInverse originalReadback originalRowLift
  activeKernel fullKernelFrame slowFastFrame sourceGreen nativeResponse nativeInsertion nativeModeForcing
  nativeRegularResponse sourceResidue extendedTensor physicalDeterminant

/-- Every column is the original total whole-field Green response to its coordinate force. -/
def sourceWholePhotonGreen (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>nativeResponse epsilon s n (Pi.single j 1) i

private theorem insertion_add (epsilon s : ℝ) (n : PhysicalMomentum) (v w : Fin 5→ℂ) :
    nativeInsertion epsilon s n (v+w)=nativeInsertion epsilon s n v+nativeInsertion epsilon s n w := by
  have lift : fiveVector (v+w)=fiveVector v+fiveVector w := by
    funext i
    simp only [fiveVector,Pi.add_apply]
    split_ifs <;> simp
  simp only [nativeInsertion,lift,Matrix.mulVec_add]

private theorem forcing_add (epsilon s : ℝ) (n : PhysicalMomentum) (v w : Fin 289→ℂ) :
    nativeModeForcing epsilon s n (v+w)=nativeModeForcing epsilon s n v+nativeModeForcing epsilon s n w := by
  funext i
  simp only [nativeModeForcing,activeForcing,Matrix.mulVec_add,Pi.add_apply]

private theorem forcing_smul (epsilon s : ℝ) (n : PhysicalMomentum) (c : ℂ) (v : Fin 289→ℂ) :
    nativeModeForcing epsilon s n (c • v)=c • nativeModeForcing epsilon s n v := by
  funext i
  simp only [nativeModeForcing,activeForcing,Matrix.mulVec_smul,Pi.smul_apply]

/-- The same source residue acts on all289 forces before any external-state or current read. -/
def sourceWholePhotonResidueMap (epsilon s : ℝ) (n : PhysicalMomentum) :
    (Fin 289→ℂ)→ₗ[ℂ](Fin 289→ℂ) where
  toFun v:=nativeInsertion epsilon s n (sourceResidue epsilon s n*ᵥnativeModeForcing epsilon s n v)
  map_add' v w:=by rw [forcing_add,Matrix.mulVec_add,insertion_add]
  map_smul' c v:=by rw [forcing_smul,Matrix.mulVec_smul,nativeInsertion_smul];rfl

def sourceWholePhotonResidue (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  LinearMap.toMatrix' (sourceWholePhotonResidueMap epsilon s n)

theorem sourceWholePhotonResidue_apply (epsilon s : ℝ) (n : PhysicalMomentum) (v : Fin 289→ℂ) :
    sourceWholePhotonResidue epsilon s n*ᵥv=
      nativeInsertion epsilon s n (sourceResidue epsilon s n*ᵥnativeModeForcing epsilon s n v) :=
  LinearMap.toMatrix'_mulVec (sourceWholePhotonResidueMap epsilon s n) v

def sourcePhotonNullSource (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalRowLift (frequencyRay epsilon s n)*nullProjection*originalReadback (frequencyRay epsilon s n)

def sourcePhotonNullField (epsilon s : ℝ) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange (frequencyRay epsilon s n)*nullProjection*originalInverse (frequencyRay epsilon s n)

private theorem green_actual (e : scaleDomain) (s : slopeDomain) (n : PhysicalMomentum)
    (direction : ∀i,|n i|≤1) (regular : IsUnit (normalizedEffective e s n direction).det) :
    sourceWholePhotonGreen e.val s.val n=sourceGreen (dynamicPoint e s n direction regular) := by
  ext i j
  rw [sourceWholePhotonGreen,nativeResponse_original e s n direction regular]
  simp only [sourceField,Matrix.mulVec_single_one,Matrix.col_apply]

/-- The original source-generated punctured sheet supplies both inverse identities with their own varying null projectors. -/
theorem sourceWholePhotonGreen_equations (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀ᶠ s in 𝓝[≠] (sourceSheet branch n unit e.val),
      originalJacobi (frequencyRay e.val s n)*sourceWholePhotonGreen e.val s n=1-sourcePhotonNullSource e.val s n ∧
      sourceWholePhotonGreen e.val s n*originalJacobi (frequencyRay e.val s n)=1-sourcePhotonNullField e.val s n := by
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_simple branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_equation branch n unit),
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e simple equation bounds
  let center:=sourceSheet branch n unit e.val
  have inside : |center|<1 := by
    apply abs_lt.mpr
    change (if branch=0 then (1/2:ℝ) else (4/5:ℝ))<center ∧ center<(if branch=0 then (2/3:ℝ) else (9/10:ℝ)) at bounds
    split_ifs at bounds <;> constructor <;> linarith
  have slopes:=simple.2.tendsto_slope.eventually_ne simple.1
  have interval:=((continuous_abs.continuousAt : ContinuousAt (fun t : ℝ=>|t|) center).eventually_lt_const inside).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] center≤𝓝 center)
  filter_upwards [slopes,interval] with t slope insideT
  have nonzero : physicalDeterminant e.val t n≠0 := by
    intro zero
    apply slope
    simp only [slope_def_module,zero,equation,sub_self,smul_zero]
  let s : slopeDomain:=⟨t,insideT.le⟩
  have regular : IsUnit (normalizedEffective e s n (unit_direction_bound n unit)).det := by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    have actual:=extendedTensor_actual e s n (unit_direction_bound n unit)
    rw [←actual] at zero
    apply nonzero
    change (extendedTensor e.val t n).det=0 at zero
    simpa only [physicalDeterminant,Complex.zero_re] using congrArg Complex.re zero
  rw [green_actual e s n (unit_direction_bound n unit) regular]
  exact ⟨original_green_equation (dynamicPoint e s n (unit_direction_bound n unit) regular),
    sourceGreen_original_left (dynamicPoint e s n (unit_direction_bound n unit) regular)⟩

private theorem column_limit (e : scaleDomain) (s : ℝ) (n : PhysicalMomentum)
    (regular : frequencyRay e.val s n∈complementRegular) (v : Fin 289→ℂ)
    (pole : Tendsto (fun t : ℝ=>((t-s:ℝ):ℂ) • (extendedTensor e.val t n)⁻¹) (𝓝[≠] s)
      (𝓝 (sourceResidue e.val s n))) :
    Tendsto (fun t : ℝ=>((t-s:ℝ):ℂ) • nativeResponse e.val t n v) (𝓝[≠] s)
      (𝓝 (nativeInsertion e.val s n (sourceResidue e.val s n*ᵥnativeModeForcing e.val s n v))) := by
  have path : Tendsto (fun t : ℝ=>(t,v)) (𝓝[≠] s) (𝓝 (s,v)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds tendsto_const_nhds
  have reader := (nativeModeForcing_continuous_at e.val s n regular v).tendsto.comp path
  have multiply : Continuous (fun pair : Matrix (Fin 5) (Fin 5) ℂ × (Fin 5→ℂ)=>pair.1*ᵥpair.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have modal := (multiply.tendsto _).comp (pole.prodMk_nhds reader)
  have insertion := (nativeInsertion_continuous_at e.val s n regular _).tendsto.comp
    ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds modal)
  have background := (nativeRegularResponse_continuous_at e.val s n regular v).tendsto.comp path
  have scalar : Tendsto (fun t : ℝ=>((t-s:ℝ):ℂ)) (𝓝[≠] s) (𝓝 (0:ℂ)) := by
    have continuous : Continuous (fun t : ℝ=>((t-s:ℝ):ℂ)) := by fun_prop
    simpa only [sub_self,Complex.ofReal_zero] using (continuous.tendsto s).mono_left nhdsWithin_le_nhds
  have returned:=insertion.add (scalar.smul background)
  simp only [Function.comp_def,zero_smul,add_zero] at returned
  apply returned.congr'
  filter_upwards [] with t
  simp only [nativeResponse,smul_add,Matrix.smul_mulVec,nativeInsertion_smul,id_eq]

/-- This is the residue of the same complete original Green matrix, including all force columns. -/
theorem sourceWholePhotonGreen_residue (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun s : ℝ=>((s-sourceSheet branch n unit e.val:ℝ):ℂ) • sourceWholePhotonGreen e.val s n)
      (𝓝[≠] (sourceSheet branch n unit e.val))
      (𝓝 (sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n)) := by
  filter_upwards [sourceSheet_inverse_residue branch n unit,
    scaleVal_tendsto.eventually (sourceSheet_bounds branch n unit)] with e pole bounds
  have inside : |sourceSheet branch n unit e.val|≤1 := by
    apply abs_le.mpr
    split_ifs at bounds <;> constructor <;> linarith
  have regular : frequencyRay e.val (sourceSheet branch n unit e.val) n∈complementRegular :=
    (rayPoint e ⟨sourceSheet branch n unit e.val,inside⟩ n (unit_direction_bound n unit)).property
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have returned:=((continuous_apply i).tendsto _).comp
    (column_limit e (sourceSheet branch n unit e.val) n regular (Pi.single j 1) pole)
  simpa only [Function.comp_def,sourceWholePhotonGreen,sourceWholePhotonResidue,LinearMap.toMatrix'_apply,
    sourceWholePhotonResidueMap,LinearMap.coe_mk,AddHom.coe_mk,Matrix.smul_apply,Pi.smul_apply] using returned

private theorem active_null : activeProjection*nullProjection=0 := by
  unfold activeProjection nullProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases same : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.zero_apply]
    unfold activeFlag nullFlag
    simp only [decide_eq_true_eq]
    split_ifs <;> norm_num;omega
  · simp [same]

/-- The original forcing projection kills precisely the right null-source directions, without assuming a full inverse. -/
theorem sourceWholePhotonResidue_null (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourceWholePhotonResidue epsilon s n*sourcePhotonNullSource epsilon s n=0 := by
  have readback : originalReadback (frequencyRay epsilon s n)*originalRowLift (frequencyRay epsilon s n)=1 :=
    mul_eq_one_comm.mp (original_row_readback _)
  have projected : activeProjection*originalReadback (frequencyRay epsilon s n)*sourcePhotonNullSource epsilon s n=0 := by
    calc
      _=activeProjection*(originalReadback (frequencyRay epsilon s n)*originalRowLift (frequencyRay epsilon s n))*
          nullProjection*originalReadback (frequencyRay epsilon s n) := by unfold sourcePhotonNullSource;noncomm_ring
      _=0 := by rw [readback,mul_one,active_null,zero_mul]
  have forcing (v : Fin 289→ℂ) : nativeModeForcing epsilon s n (sourcePhotonNullSource epsilon s n*ᵥv)=0 := by
    have source : activeForcing (frequencyRay epsilon s n) (sourcePhotonNullSource epsilon s n*ᵥv)=0 := by
      simp only [activeForcing,Matrix.mulVec_mulVec,←mul_assoc,projected,Matrix.zero_mulVec]
    funext i
    simp only [nativeModeForcing,source,Matrix.mulVec_zero,Pi.zero_apply]
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [←Matrix.mulVec_mulVec,sourceWholePhotonResidue_apply,forcing,Matrix.mulVec_zero]
  have liftZero : fiveVector (0 : Fin 5→ℂ)=0 := by
    funext i
    simp only [fiveVector]
    split_ifs <;> rfl
  simp only [nativeInsertion,liftZero,Matrix.mulVec_zero,Matrix.zero_mulVec]

end LowEnergy.PreparationPhysicalNativePhotonFluxReturn
