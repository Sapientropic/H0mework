import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceCausalFieldReturn

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullSlowFieldResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumNativePoleTensor PreparationVacuumNativeSlowCoupling
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalFeedback CanonicalGradedSpatialSource
open PreparationVacuumStaticPoleResponse PreparationVacuumWholeOrigin
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumQuantumSlowResidue
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel fullKernelFrame unrestrictedGreen slowFastFrame
  sourceNativeReader sourceActualNativeForcing returnedHalfCurrent

private theorem five_scaled (d : ℝ) (v : Fin 5→ℂ) :
    wideRayScaling d*ᵥfiveVector v=fiveVector (rayScaling d*ᵥv) := by
  funext j
  rw [wideRayScaling,Matrix.mulVec_diagonal]
  by_cases inside : j.val<5
  · simp only [fiveVector,dif_pos inside,if_pos inside,rayScaling,Matrix.mulVec_diagonal]
  · simp only [fiveVector,dif_neg inside,mul_zero]

private theorem five_smul (z : ℂ) (v : Fin 5→ℂ) : fiveVector (z • v)=z • fiveVector v := by
  funext i
  by_cases inside : i.val<5
  · simp only [fiveVector,dif_pos inside,Pi.smul_apply]
  · simp only [fiveVector,dif_neg inside,Pi.smul_apply,smul_zero]

private theorem mode_unscale (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (v : Fin 5→ℂ) :
    modeCoordinates (sourceRealScale n zeta d) ((sourceCausalBalanced n zeta.val d.val)⁻¹*ᵥv)=
      slowFastFrame*ᵥfiveVector ((sourceCausalNormalized n zeta.val d.val)⁻¹*ᵥv) := by
  rw [sourceCausalBalanced,Matrix.mul_inv_rev,←Matrix.mulVec_mulVec]
  unfold modeCoordinates
  simp only [sourceRealScale]
  rw [five_scaled,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (sourceCausalScaling_unit d.val d.property.1.ne')),Matrix.one_mulVec]

def sourceRegularMatrix (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange p*(contactInverse p*originalReadback p+
    unrestrictedGreen p*activeProjection*originalReadback p)

def sourceNativeFrame (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange p*rawEffectiveFrame p*slowFastFrame

def sourceCornerRead (d : ℝ) (f : Fin 289→ℂ) : Fin 5→ℂ :=
  fun i=>(wideRayScaling d*ᵥ(slowFastFrame.transpose*ᵥf)) (fiveIndex i)

/-- A total expression whose generated legal domain returns the original uncleared field. -/
def sourceCausalFullExpression (n : PhysicalMomentum) (zeta : ℂ) (d : ℝ) (forcing : Fin 289→ℂ) : Fin 289→ℂ :=
  let p:=fixedMomentum (d • n) ((d:ℂ)*zeta)
  sourceNativeFrame p*ᵥfiveVector ((sourceCausalNormalized n zeta d)⁻¹*ᵥ
    sourceCornerRead d (sourceNativeReader p*ᵥforcing))+
    sourceRegularMatrix p*ᵥforcing

theorem sourceCausalFullExpression_original (n : PhysicalMomentum) (zeta : sourceCausalDomain n)
    (d : sourceCausalScale n zeta) (forcing : Fin 289→ℂ) :
    sourceCausalFullExpression n zeta.val d.val forcing=sourceField (sourceCausalFieldPoint n zeta d) forcing := by
  rw [sourceCausalField_schur,mode_unscale]
  have green : unrestrictedGreen (sourceCausalComplement n zeta d).val=complementGreen (sourceCausalComplement n zeta d) := by
    simp only [unrestrictedGreen,complementGreen]
  have frame : rawEffectiveFrame (sourceCausalComplement n zeta d).val=effectiveFrame (sourceCausalComplement n zeta d) := by
    simp only [rawEffectiveFrame,effectiveFrame,green]
  have reader : rawEffectiveReader (sourceCausalComplement n zeta d).val=effectiveReader (sourceCausalComplement n zeta d) := by
    simp only [rawEffectiveReader,effectiveReader,green]
  have forcingRead : sourceCornerRead d.val
      (sourceNativeReader (sourceCausalComplement n zeta d).val*ᵥforcing)=sourceCausalBalancedForcing n zeta d forcing := by
    unfold sourceCornerRead sourceCausalBalancedForcing activeForcing
    simp only [sourceNativeReader,←Matrix.mulVec_mulVec,reader]
  unfold sourceCausalFullExpression sourceNativeFrame sourceRegularMatrix
  rw [←forcingRead]
  simp only [←frame,←green,Matrix.add_mulVec,←Matrix.mulVec_mulVec,Matrix.mulVec_add]
  simp only [sourceCausalComplement,activeForcing]
  abel

/-- The actual common-eight quantum source drives the same complete field occurrence. -/
def sourceJointCausalField (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) (d : ℝ) : Fin 289→ℂ :=
  sourceCausalFullExpression n zeta d (returnedHalfCurrent q (-(d • n)) 0 l r ((d:ℂ)*zeta))

theorem sourceJointCausalField_whole (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (d : sourceCausalScale n zeta) :
    originalJacobi (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥsourceJointCausalField q n zeta.val l r d.val=
      returnedHalfCurrent q (-(d.val • n)) 0 l r ((d.val:ℂ)*zeta.val)-
      originalRowLift (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥ
        (nullProjection*ᵥ(originalReadback (fixedMomentum (d.val • n) ((d.val:ℂ)*zeta.val))*ᵥ
          returnedHalfCurrent q (-(d.val • n)) 0 l r ((d.val:ℂ)*zeta.val))) := by
  rw [sourceJointCausalField,sourceCausalFullExpression_original]
  exact original_forced_field (sourceCausalFieldPoint n zeta d) _

def sourceSlowRead (f : Fin 289→ℂ) : Fin 5→ℂ :=
  fun i=>if i.val<3 then (slowFastFrame.transpose*ᵥf) (fiveIndex i) else 0

def sourceReducedRead (d : ℝ) (f : Fin 289→ℂ) : Fin 5→ℂ :=
  fun i=>(if i.val<3 then (1:ℂ) else (d:ℂ))*(slowFastFrame.transpose*ᵥf) (fiveIndex i)

private theorem sourceCornerRead_scaled (d : ℝ) (nonzero : d≠0) (f : Fin 289→ℂ) :
    ((d:ℂ)^3) • sourceCornerRead d f=sourceReducedRead d ((d:ℂ) • f) := by
  funext i
  simp only [sourceCornerRead,sourceReducedRead,wideRayScaling,Matrix.mulVec_diagonal,Pi.smul_apply,
    Matrix.mulVec_smul,smul_eq_mul,fiveIndex,i.isLt,if_true]
  split_ifs <;> field_simp [Complex.ofReal_ne_zero.mpr nonzero]

private theorem reducedRead_continuous : Continuous (fun p : ℝ×(Fin 289→ℂ)=>sourceReducedRead p.1 p.2) := by
  apply continuous_pi
  intro i
  unfold sourceReducedRead
  split_ifs <;> fun_prop

private theorem sourcePoint_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>fixedMomentum (d • n) ((d:ℂ)*zeta)) (𝓝[>] 0) (𝓝 0) := by
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [sourcePhysicalRay_generated,zero_smul] using scalar.smul (tendsto_const_nhds (x:=fixedMomentum n zeta))

private theorem sourceMatrix_continuous (terms : List SourceTerm) : Continuous (sourceMatrix terms) := by
  induction terms with
  | nil=>exact continuous_const
  | cons a rest ih=>
    have term : Continuous a.matrix := by
      apply continuous_matrix
      intro i j
      simp only [SourceTerm.matrix,Matrix.single_apply]
      split_ifs
      · unfold Powers.value;fun_prop
      · exact continuous_const
    exact term.add ih

private theorem sourceNativeFrame_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>sourceNativeFrame (fixedMomentum (d • n) ((d:ℂ)*zeta))) (𝓝[>] 0)
      (𝓝 (originalChange 0*fullKernelFrame*slowFastFrame)) := by
  have point:=sourcePoint_limit n zeta
  have changeLimit:=(sourceMatrix_continuous originalChangeTerms).continuousAt.tendsto.comp point
  have kernel : Tendsto (fun d : ℝ=>activeKernel (fixedMomentum (d • n) ((d:ℂ)*zeta))) (𝓝[>] 0) (𝓝 (activeKernel 0)) := by
    simpa only [activeKernel,Function.comp_def] using (sourceMatrix_continuous activeTerms).continuousAt.tendsto.comp point
  have green:=unrestrictedGreen_smooth_origin.continuousAt.tendsto.comp point
  have frame:=(tendsto_const_nhds (x:=fullKernelFrame)).sub
    ((green.mul kernel).mul (tendsto_const_nhds (x:=fullKernelFrame)))
  have result:=(changeLimit.mul frame).mul (tendsto_const_nhds (x:=slowFastFrame))
  have origin : unrestrictedGreen 0*activeKernel 0*fullKernelFrame=0 := by rw [mul_assoc,fullKernel_origin,mul_zero]
  simpa only [Function.comp_def,sourceNativeFrame,rawEffectiveFrame,origin,sub_zero,originalChange] using result

private theorem sourceRegularMatrix_limit (n : PhysicalMomentum) (zeta : ℂ) :
    Tendsto (fun d : ℝ=>sourceRegularMatrix (fixedMomentum (d • n) ((d:ℂ)*zeta))) (𝓝[>] 0)
      (𝓝 (sourceRegularMatrix 0)) := by
  have point:=sourcePoint_limit n zeta
  have changeLimit:=(sourceMatrix_continuous originalChangeTerms).continuousAt.tendsto.comp point
  have contact:=(sourceMatrix_continuous contactInverseTerms).continuousAt.tendsto.comp point
  have readback : Continuous originalReadback := by
    unfold originalReadback originalChange
    exact ((sourceMatrix_continuous originalChangeTerms).comp continuous_neg).matrix_transpose
  have read:=readback.continuousAt.tendsto.comp point
  have green:=unrestrictedGreen_smooth_origin.continuousAt.tendsto.comp point
  exact changeLimit.mul ((contact.mul read).add ((green.mul tendsto_const_nhds).mul read))

/-- Complete causal field residue; its input includes the true native reader derivative times the full current residue. -/
def sourceJointFieldResidue (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (l r : RestStateIndex) : Fin 289→ℂ :=
  (originalChange 0*fullKernelFrame*slowFastFrame)*ᵥfiveVector
    ((sourceCausalPrincipal n zeta)⁻¹*ᵥsourceSlowRead (sourceActualNativeResidue q n zeta l r))

private theorem five_continuous : Continuous (fiveVector : (Fin 5→ℂ)→Fin 289→ℂ) := by
  apply continuous_pi
  intro i
  unfold fiveVector
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- The actual half-axis quantum current and the original field share a generated joint causal corner. -/
theorem sourceJointCausalField_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>((d:ℂ)^3) • sourceJointCausalField q n zeta.val l r d)
      (𝓝[>] 0) (𝓝 (sourceJointFieldResidue q n zeta.val l r)) := by
  have positive:=zeta.property.1
  have forcing:=sourceActualNative_residue q n zeta.val positive l r nonrealL nonrealR
  have current:=sourceFullCurrent_residue q n zeta.val positive l r nonrealL nonrealR
  have scalar : Tendsto (fun d : ℝ=>(d:ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have realScalar : Tendsto (fun d : ℝ=>d) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have reduced:=reducedRead_continuous.continuousAt.tendsto.comp (realScalar.prodMk_nhds forcing)
  have origin : sourceReducedRead 0 (sourceActualNativeResidue q n zeta.val l r)=
      sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) := by
    funext i
    simp only [sourceReducedRead,sourceSlowRead,Complex.ofReal_zero]
    split_ifs <;> simp only [one_mul,zero_mul]
  rw [origin] at reduced
  have input : Tendsto (fun d : ℝ=>((d:ℂ)^3) • sourceCornerRead d (sourceActualNativeForcing q n zeta.val l r d))
      (𝓝[>] 0) (𝓝 (sourceSlowRead (sourceActualNativeResidue q n zeta.val l r))) := by
    apply reduced.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact (sourceCornerRead_scaled d (ne_of_gt hd) _).symm
  have inverse:=sourceCausalInverse_limit n zeta
  have coordinates:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp (inverse.prodMk_nhds input)
  have lifted:=five_continuous.continuousAt.tendsto.comp coordinates
  have native:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    ((sourceNativeFrame_limit n zeta.val).prodMk_nhds lifted)
  have regular:=(continuous_fst.matrix_mulVec continuous_snd).continuousAt.tendsto.comp
    ((sourceRegularMatrix_limit n zeta.val).prodMk_nhds current)
  have regularZero:=scalar.smul regular
  simp only [zero_smul] at regularZero
  have result:=native.add regularZero
  simp only [add_zero] at result
  apply result.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  simp only [Function.comp_def,sourceJointCausalField,sourceCausalFullExpression,smul_add,
    ←sourceActualNativeForcing_generated,Matrix.mulVec_smul,five_smul,smul_smul]
  congr 1
  rw [←pow_succ']

end LowEnergy.PreparationVacuumFullSlowFieldResponse
