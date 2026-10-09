import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceWholePhotonFlux

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhotonFluxReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalQuantumLockedCharge
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumNativePoleTensor
open PreparationVacuumFullOriginResponse PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalNativePhotonScatteringSheetReturn SourcePropagationNativeActionHessian
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] originalJacobi originalChange originalInverse originalRowLift originalReadback
  activeKernel fullKernelFrame slowFastFrame unrestrictedGreen rawEffectiveFrame nativeInsertion nativeModeForcing
  sourceResidue sourceWholePhotonGreen sourceWholePhotonResidue sourcePhotonNullField sourceNativePolarization

/-- The independent left reader is the original mode-forcing row divided by its generated nonzero pole pivot. -/
def sourcePhotonLeftReader (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (v : Fin 289→ℂ) : ℂ :=
  sourceNativePoleCoefficient branch epsilon s n (nativeModeForcing epsilon s n v)

theorem sourceWholePhotonResidue_factor (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀v : Fin 289→ℂ,
      sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n*ᵥv=
        sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n v •
          sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceNativePoleColumn_generated branch n unit] with e column
  intro v
  rw [sourceWholePhotonResidue_apply,column.2.2,nativeInsertion_smul]
  unfold sourcePhotonLeftReader sourceNativePolarization
  rfl

private theorem null_active : nullProjection*activeProjection=0 := by
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

private theorem active_complement : activeProjection*fullComplementProjection=fullComplementProjection := by
  unfold activeProjection fullComplementProjection projectionMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases flag : activeFlag i <;> simp [fullComplementFlag,flag]

private theorem raw_frame_active (p : Fin 4→ℂ) : activeProjection*rawEffectiveFrame p=rawEffectiveFrame p := by
  have green : activeProjection*unrestrictedGreen p=unrestrictedGreen p := by
    unfold unrestrictedGreen
    rw [←mul_assoc,←mul_assoc,active_complement]
  unfold rawEffectiveFrame
  simp only [mul_sub,←mul_assoc,PreparationVacuumStaticPoleResponse.fullKernel_active,green]

/-- The original native polarization lies in the active field image, so its varying whole null-field projector vanishes at the pole. -/
theorem sourceNativePolarization_null (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourcePhotonNullField epsilon s n*ᵥsourceNativePolarization branch epsilon s n=0 := by
  have frame : nullProjection*rawEffectiveFrame (frequencyRay epsilon s n)=0 := by
    calc
      _=nullProjection*(activeProjection*rawEffectiveFrame (frequencyRay epsilon s n)) := by rw [raw_frame_active]
      _=0 := by rw [←mul_assoc,null_active,zero_mul]
  unfold sourcePhotonNullField sourceNativePolarization nativeInsertion
  simp only [Matrix.mulVec_mulVec]
  have product : originalChange (frequencyRay epsilon s n)*nullProjection*originalInverse (frequencyRay epsilon s n)*
      (originalChange (frequencyRay epsilon s n)*(rawEffectiveFrame (frequencyRay epsilon s n)*(slowFastFrame*wideRayScaling epsilon)))=0 := by
    calc
      _=originalChange (frequencyRay epsilon s n)*nullProjection*
          (originalInverse (frequencyRay epsilon s n)*originalChange (frequencyRay epsilon s n))*
          rawEffectiveFrame (frequencyRay epsilon s n)*(slowFastFrame*wideRayScaling epsilon) := by noncomm_ring
      _=originalChange (frequencyRay epsilon s n)*(nullProjection*rawEffectiveFrame (frequencyRay epsilon s n))*
          (slowFastFrame*wideRayScaling epsilon) := by rw [original_inverse_change,mul_one];noncomm_ring
      _=0 := by rw [frame,mul_zero,zero_mul]
  rw [product,Matrix.zero_mulVec]

/-- Differentiating the original projected right-inverse equation returns the actual polarization, without any emitter visibility premise. -/
theorem sourceNativePolarization_sheetReturn (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
        (sourcePhotonSheetJacobiJet e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n)=
      sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonGreen_equations branch n unit,sourceWholePhotonGreen_residue branch n unit,
    sourceNativePolarization_generated branch n unit] with e equations pole polarization
  let c:=sourceSheet branch n unit e.val
  let U:=sourceNativePolarization branch e.val c n
  let R:=sourceWholePhotonResidue e.val c n
  let K:=fun s : ℝ=>originalJacobi (frequencyRay e.val s n)
  have kernel : K c*ᵥU=0 := by simpa only [nativeActionFourierHessian_original] using polarization.2
  have castSmul (r : ℝ) (M : Matrix (Fin 289) (Fin 289) ℂ) : (r:ℂ) • M=r • M := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  have poleReal : Tendsto (fun s : ℝ=>(s-c) • sourceWholePhotonGreen e.val s n) (𝓝[≠] c) (𝓝 R) := by
    simpa only [castSmul] using pole
  have slopeLimit:=(sourcePhotonSheetJacobi_hasDerivAt e.val c n).tendsto_slope
  have operatorLimit:=poleReal.mul slopeLimit
  have multiply : Continuous (fun pair : Matrix (Fin 289) (Fin 289) ℂ × (Fin 289→ℂ)=>pair.1*ᵥpair.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have returning := (multiply.tendsto (R*sourcePhotonSheetJacobiJet e.val c n,U)).comp
    (operatorLimit.prodMk_nhds (tendsto_const_nhds (x:=U)))
  have projected : Tendsto (fun s : ℝ=>(1-sourcePhotonNullField e.val s n)*ᵥU) (𝓝[≠] c) (𝓝 U) := by
    have pair:=((tendsto_const_nhds (x:=(1 : Matrix (Fin 289) (Fin 289) ℂ))).sub
      (((sourcePhotonNullField_continuous e.val n).tendsto c).mono_left (nhdsWithin_le_nhds : 𝓝[≠] c≤𝓝 c))).prodMk_nhds
      (tendsto_const_nhds (x:=U))
    have result := (multiply.tendsto _).comp pair
    simpa only [Function.comp_def,Matrix.sub_mulVec,Matrix.one_mulVec,U,sourceNativePolarization_null,sub_zero] using result
  have same : (fun s : ℝ=>(((s-c) • sourceWholePhotonGreen e.val s n)*slope K c s)*ᵥU)=ᶠ[𝓝[≠] c]
      (fun s : ℝ=>(1-sourcePhotonNullField e.val s n)*ᵥU) := by
    filter_upwards [equations,self_mem_nhdsWithin] with s original different
    have nonzero : s-c≠0 := sub_ne_zero.mpr different
    rw [slope_def_module,smul_mul_assoc,mul_smul_comm,smul_smul,mul_inv_cancel₀ nonzero,one_smul,
      mul_sub,Matrix.sub_mulVec,original.2,
      ←Matrix.mulVec_mulVec U (sourceWholePhotonGreen e.val s n) (K c),kernel,Matrix.mulVec_zero,sub_zero]
  have result := tendsto_nhds_unique returning (projected.congr' same.symm)
  simpa only [Function.comp_def,Matrix.mulVec_mulVec] using result

/-- The source cofactor coordinate receives its normalization from the whole Jacobi flux and its independent source reader. -/
theorem sourceNativePolarization_sheetFlux (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (sourcePhotonSheetJacobiJet e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceNativePolarization branch e.val (sourceSheet branch n unit e.val) n)=1 := by
  filter_upwards [sourceNativePolarization_sheetReturn branch n unit,sourceWholePhotonResidue_factor branch n unit,
    sourceNativePolarization_generated branch n unit] with e returned factor nonzero
  rw [factor] at returned
  exact (smul_left_injective ℂ nonzero.1) (returned.trans (one_smul ℂ _).symm)

/-- The same independent forcing reader is a left homogeneous mode of the original full pencil. -/
theorem sourcePhotonLeftReader_homogeneous (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀v : Fin 289→ℂ,
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (originalJacobi (frequencyRay e.val (sourceSheet branch n unit e.val) n)*ᵥv)=0 := by
  filter_upwards [sourceWholePhotonResidue_homogeneous branch n unit,sourceWholePhotonResidue_factor branch n unit,
    sourceNativePolarization_generated branch n unit] with e homogeneous factor polarization
  intro v
  have returned:=congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>M*ᵥv) homogeneous.1
  rw [←Matrix.mulVec_mulVec,factor,Matrix.zero_mulVec] at returned
  exact (smul_eq_zero.mp returned).resolve_right polarization.1

/-- The frequency-residue polarization uses the already generated epsilon-squared conversion on each leg. -/
def sourceNativeFrequencyPolarization (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 289→ℂ :=
  (epsilon^2:ℝ) • sourceNativePolarization branch epsilon s n

theorem sourceNativePolarization_frequencyFlux (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (sourcePhotonFrequencyJacobiJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n*ᵥ
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)=1 := by
  filter_upwards [sourceNativePolarization_sheetFlux branch n unit] with e flux
  have nonzero : e.val^2≠0 := pow_ne_zero _ (ne_of_gt e.property.1)
  unfold sourcePhotonFrequencyJacobiJet sourceNativeFrequencyPolarization
  rw [(sourcePhotonFrequencyJacobi_hasDerivAt e (sourceSheet branch n unit e.val) n).deriv,
    Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,inv_mul_cancel₀ nonzero,one_smul,flux]

/-- Actual charged emitters are the same independent left reader used by the full field flux. -/
theorem sourcePhotonEmitter_leftReader (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourcePhotonEmitter leg branch epsilon s n=
      sourcePhotonLeftReader branch epsilon s n
        (sheetCurrent leg.q epsilon s n leg.momentum
          (sourceChargedRestIndex leg.sideL leg.edgeL) (sourceChargedRestIndex leg.sideR leg.edgeR) leg.window) := rfl

/-- Source visibility remains in the actual current coefficient after physical-frequency flux normalization. -/
theorem sourcePhotonFrequencyResidue_fluxFactor (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀leg : SourcePhotonLeg,
      sourcePhotonFrequencyResidue leg e.val (sourceSheet branch n unit e.val) n=
        sourcePhotonEmitter leg branch e.val (sourceSheet branch n unit e.val) n •
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourcePhotonFrequencyResidue_factor branch n unit] with e factor
  intro leg
  rw [factor leg,sourceNativeFrequencyPolarization]
  ext i
  simp only [Pi.smul_apply,Complex.real_smul,smul_eq_mul]
  ring

/-- The frequency-normalized operator is the pole residue of the same complete Green matrix in physical omega. -/
theorem sourceWholePhotonGreen_frequencyResidue (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun omega : ℝ=>((omega-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        sourceWholePhotonGreen e.val (omega/e.val^2) n)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n)) := by
  filter_upwards [sourceWholePhotonGreen_residue branch n unit] with e pole
  let s:=sourceSheet branch n unit e.val
  let a:=e.val^2
  have nonzero : a≠0 := pow_ne_zero 2 e.property.1.ne'
  have divided : a*s/a=s := by field_simp
  have reparam : Tendsto (fun omega : ℝ=>omega/a) (𝓝[≠] (a*s)) (𝓝[≠] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have result : Tendsto (fun omega : ℝ=>omega/a) (𝓝[≠] (a*s)) (𝓝 ((a*s)/a)) :=
        ((continuous_id.div_const a).tendsto (a*s)).mono_left nhdsWithin_le_nhds
      simpa only [divided] using result
    · filter_upwards [self_mem_nhdsWithin] with omega outside
      change omega/a≠s
      intro equal
      apply outside
      change omega=a*s
      exact ((div_eq_iff nonzero).mp equal).trans (mul_comm s a)
  have result : Tendsto (fun omega : ℝ=>(a:ℂ) •
      (((omega/a-s:ℝ):ℂ) • sourceWholePhotonGreen e.val (omega/a) n)) (𝓝[≠] (a*s))
      (𝓝 ((a:ℂ) • sourceWholePhotonResidue e.val s n)) := tendsto_const_nhds.smul (pole.comp reparam)
  have castSmul : (a:ℂ) • sourceWholePhotonResidue e.val s n=sourceWholePhotonFrequencyResidue e.val s n := by
    ext i j
    simp only [sourceWholePhotonFrequencyResidue,Matrix.smul_apply,Complex.real_smul,smul_eq_mul,a]
  rw [castSmul] at result
  apply result.congr'
  filter_upwards [] with omega
  have scalar : a*(omega/a-s)=omega-a*s := by field_simp
  rw [smul_smul,←Complex.ofReal_mul,scalar]
  rfl

end LowEnergy.PreparationPhysicalNativePhotonFluxReturn
