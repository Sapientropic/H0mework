import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePinnedPoleBoundary
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceAmputatedPreparedVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedPoleTensor
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumFullOriginResponse
open PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalPoleAmputation
open PreparationVacuumFullSlowFieldResponse PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFieldConstraintResponse SourcePropagationNativeActionHessian
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumQuantumSlowResidue
open PreparationVacuumWholeOrigin PreparationVacuumNativePoleTensor
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open Filter Set
open scoped BigOperators Matrix Topology
attribute [local irreducible] sourcePoleActionEuler sourcePoleEulerInitial
  fullNativeOrigin fullKernelFrame slowFastFrame sourceAmputatedPoleVertex

private theorem initial_window_derivative (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (i : Fin 289) :
    HasDerivAt (fun T=>actualCurrent q pL pR l r 0 T i)
      (sourcePoleEulerInitial q pL pR l r i) 0 := by
  have continuous:=sourcePoleActionEuler_continuous q pL pR l r i
  have derivative:=intervalIntegral.integral_hasDerivAt_right (continuous.intervalIntegrable 0 0)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt
  simpa only [actualCurrent,sourcePoleCurrentWindow,laplaceWeight,neg_zero,zero_mul,
    Complex.exp_zero,one_mul,sourcePoleEulerInitial] using derivative

private theorem complex_const_derivative (a : ℂ) (f : ℝ→ℂ) (b : ℂ) (x : ℝ)
    (h : HasDerivAt f b x) : HasDerivAt (fun t=>a*f t) (a*b) x := by
  simpa only [Pi.smul_def,smul_eq_mul] using h.const_smul a

/-- The paid whole-source window identity generates its actual independent-leg initial reader. -/
theorem sourceInitial_origin_read (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) :
    fullNativeOrigin.transpose*ᵥsourcePoleEulerInitial q pL pR l r=
      sourceOriginPair (sourceOriginWeight (sourcePoleEulerInitial q pL pR l r)) := by
  funext j
  have weight:=complex_const_derivative ((3/10:ℂ)*rootTwo) _ _ 0
    ((initial_window_derivative q pL pR l r 21).sub (initial_window_derivative q pL pR l r 34))
  have single (a : Fin 289) : HasDerivAt
      (fun T : ℝ=>(Pi.single a (sourceOriginWeight (actualCurrent q pL pR l r 0 T)) : Fin 289→ℂ) j)
      ((Pi.single a (sourceOriginWeight (sourcePoleEulerInitial q pL pR l r)) : Fin 289→ℂ) j) 0 := by
    by_cases same : j=a
    · subst j
      simpa only [Pi.single_eq_same,sourceOriginWeight,Pi.sub_apply] using weight
    · simp only [Pi.single_eq_of_ne same]
      exact hasDerivAt_const 0 0
  have rightDerivative:=(single 0).add (single 1)
  have leftDerivative : HasDerivAt
      (fun T=>(fullNativeOrigin.transpose*ᵥactualCurrent q pL pR l r 0 T) j)
      ((fullNativeOrigin.transpose*ᵥsourcePoleEulerInitial q pL pR l r) j) 0 :=
    by
      have h:=HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>complex_const_derivative
        (fullNativeOrigin.transpose j i) _ _ 0 (initial_window_derivative q pL pR l r i))
      simpa only [Matrix.mulVec,dotProduct] using h
  have same : (fun T=>(fullNativeOrigin.transpose*ᵥactualCurrent q pL pR l r 0 T) j)=
      (fun T=>(sourceOriginPair (sourceOriginWeight (actualCurrent q pL pR l r 0 T))) j) := by
    funext T
    exact congrFun (actual_origin_kernel_read q pL pR l r 0 T) j
  rw [same] at leftDerivative
  exact leftDerivative.unique rightDerivative

/-- Complexified field insertion of the original matter-action derivative, with the original independent dual. -/
def sourceBareFieldVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (v : Fin 289→ℂ) : ℂ :=
  ∑i,v i*sourceBarePoleVertex q pL pR l r (fieldUnit i)

def sourceAmputatedFieldVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (v : Fin 289→ℂ) : ℂ :=
  ∑i,v i*sourceAmputatedPoleVertex q pL pR l r (fieldUnit i)

def sourceFieldLegCorrection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (v : Fin 289→ℂ) : ℂ :=
  ∑i,v i*sourcePoleVertexLegCorrection q pL pR l r (fieldUnit i)

theorem sourceAmputatedFieldVertex_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (v : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR l r v=
      sourceBareFieldVertex q pL pR l r v+sourceFieldLegCorrection q pL pR l r v := by
  simp only [sourceAmputatedFieldVertex,sourceBareFieldVertex,sourceFieldLegCorrection,
    sourceAmputatedPoleVertex_generated,mul_add,Finset.sum_add_distrib]

theorem sourceObservedField_legs_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (v : Fin 289→ℂ) :
    ‖sourceAmputatedFieldVertex q pL pR l r v-sourceBareFieldVertex q pL pR l r v‖ ≤
      ∑i,‖v i‖*sourcePoleVertexLegPrice q pL pR l r (fieldUnit i) := by
  rw [sourceAmputatedFieldVertex_generated,add_sub_cancel_left]
  unfold sourceFieldLegCorrection
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (sourcePoleVertexLegCorrection_price q pL pR l r (fieldUnit i)) (norm_nonneg _)

private theorem material_gap_nonzero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourcePoleMaterialPairGap q pL pR l r≠0 := by
  apply mul_ne_zero
  · intro zero
    have imaginary:=congrArg Complex.im zero
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at imaginary
    exact nonrealL imaginary
  · intro zero
    have imaginary:=congrArg Complex.im zero
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at imaginary
    exact nonrealR imaginary

theorem sourceAmputatedFieldVertex_initial (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (v : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR l r v=
      -sourcePoleMaterialPairGap q pL pR l r*(v ⬝ᵥsourcePoleEulerInitial q pL pR l r) := by
  simp only [sourceAmputatedFieldVertex,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sourcePoleInitial_amputated q pL pR l r nonrealL nonrealR]
  field_simp [material_gap_nonzero q pL pR l r nonrealL nonrealR]

private theorem slow_fast_head (v : Fin 5→ℂ) :
    (slowFastFrame*ᵥfiveVector v) 0=v 0 ∧ (slowFastFrame*ᵥfiveVector v) 1=v 1 := by
  norm_num [slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,Powers.value,
    coefficientValue,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero,Matrix.add_mulVec,Matrix.single_mulVec,Matrix.zero_mulVec,fiveVector,Function.update_apply,Fin.ext_iff]

/-- The true held matter observer selects its source weight on both canonical origin modes. -/
theorem sourceAmputatedFieldVertex_frame (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (v : Fin 5→ℂ) :
    sourceAmputatedFieldVertex q pL pR l r
      ((originalChange 0*fullKernelFrame*slowFastFrame)*ᵥfiveVector v)=
      -sourcePoleMaterialPairGap q pL pR l r*
        sourceOriginWeight (sourcePoleEulerInitial q pL pR l r)*(v 0+v 1) := by
  rw [sourceAmputatedFieldVertex_initial q pL pR l r nonrealL nonrealR]
  rw [←Matrix.mulVec_mulVec]
  have frame : originalChange 0*fullKernelFrame=fullNativeOrigin := by unfold fullNativeOrigin;rfl
  rw [frame]
  rw [dotProduct_comm,←Matrix.dotProduct_transpose_mulVec,sourceInitial_origin_read]
  simp only [sourceOriginPair,dotProduct_add,dotProduct_single]
  rw [(slow_fast_head v).1,(slow_fast_head v).2]
  ring

def sourceCanonicalDenominator (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 2) : ℂ :=
  if i=0 then rootTwo*rootFifteen*(-(25/18:ℂ)*zeta^2+(25/54:ℂ)*(spatialSquare n:ℂ))
  else rootTwo*rootFifteen*((10/99:ℂ)*zeta^2+(12/335:ℂ)*(spatialSquare n:ℂ))

private theorem causal_heads (n : PhysicalMomentum) (zeta : sourceCausalDomain n) (f : Fin 5→ℂ) :
    ((sourceCausalPrincipal n zeta.val)⁻¹*ᵥf) 0=(sourceCanonicalDenominator n zeta.val 0)⁻¹*f 0 ∧
    ((sourceCausalPrincipal n zeta.val)⁻¹*ᵥf) 1=(sourceCanonicalDenominator n zeta.val 1)⁻¹*f 1 := by
  have determinant:=zeta.property.2
  rw [sourceCausalPrincipal_det] at determinant
  have zeroNonzero:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp determinant).1).1).2
  have oneNonzero:=(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp determinant).1).2
  let v:=(sourceCausalPrincipal n zeta.val)⁻¹*ᵥf
  have equation : sourceCausalPrincipal n zeta.val*ᵥv=f := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr zeta.property.2),Matrix.one_mulVec]
  have row0:=congrFun equation 0
  have row1:=congrFun equation 1
  norm_num [sourceCausalPrincipal,Matrix.add_mulVec,Matrix.mulVec_diagonal,Matrix.single_mulVec,Function.update_apply,Fin.ext_iff] at row0 row1
  constructor
  · change v 0=_
    rw [sourceCanonicalDenominator,if_pos rfl]
    simp only [neg_mul] at zeroNonzero ⊢
    rw [←row0,←mul_assoc,inv_mul_cancel₀ zeroNonzero,one_mul]
  · change v 1=_
    rw [sourceCanonicalDenominator,if_neg (by decide : (1:Fin 2)≠0)]
    rw [←row1,←mul_assoc,inv_mul_cancel₀ oneNonzero,one_mul]

private theorem signed_speed_square (branch : Fin 2) (negative : Bool) :
    (sourceSignedSpeed branch negative)^2=if branch=0 then (594/1675:ℝ) else 18/25 := by
  cases negative <;> simpa [sourceSignedSpeed] using sourceSpeed_square branch

/-- The canonical field denominator factors on its source propagation side. -/
theorem sourceObserved_canonical_factor (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (negative : Bool) (eta : ℝ) :
    sourceCanonicalDenominator n (sourcePoleSide (sourceSignedSpeed 0 negative) eta) 1=
      rootTwo*rootFifteen*(10/99:ℂ)*(eta:ℂ)*
        ((eta:ℂ)+2*Complex.I*(sourceSignedSpeed 0 negative:ℂ)) := by
  have square:=signed_speed_square 0 negative
  norm_num at square
  have complexSquare : (sourceSignedSpeed 0 negative:ℂ)^2=(594/1675:ℂ) := by
    rw [←Complex.ofReal_pow,square]
    norm_num
  norm_num [sourceCanonicalDenominator,sourcePoleSide,unit]
  ring_nf
  rw [complexSquare,Complex.I_sq]
  ring

/-- The other source propagation factor is absent from this actual held matter detector's denominators. -/
theorem sourceObserved_other_sheet_regular (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (negative : Bool) :
    sourceCanonicalDenominator n (Complex.I*(sourceSignedSpeed 1 negative:ℂ)) 0≠0 ∧
    sourceCanonicalDenominator n (Complex.I*(sourceSignedSpeed 1 negative:ℂ)) 1≠0 := by
  have square:=signed_speed_square 1 negative
  norm_num at square
  have complexSquare : (sourceSignedSpeed 1 negative:ℂ)^2=(18/25:ℂ) := by
    rw [←Complex.ofReal_pow,square]
    norm_num
  have two : rootTwo≠0 := by norm_num [rootTwo,Real.sqrt_ne_zero']
  have fifteen : rootFifteen≠0 := by norm_num [rootFifteen,Real.sqrt_ne_zero']
  norm_num [sourceCanonicalDenominator,unit,mul_pow,Complex.I_sq,complexSquare,
    mul_ne_zero two fifteen,two,fifteen]

/-- The actual amputated leading tensor is generated by the actual current and its actual amputated detector. -/
theorem sourceObservedField_tensor (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceAmputatedFieldVertex q pL pR a b (sourceJointFieldResidue q n zeta.val l r)=
      -sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)*
        ((sourceCanonicalDenominator n zeta.val 0)⁻¹*
          sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) 0+
         (sourceCanonicalDenominator n zeta.val 1)⁻¹*
          sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) 1) := by
  unfold sourceJointFieldResidue
  rw [sourceAmputatedFieldVertex_frame q pL pR a b nonrealL nonrealR]
  rw [(causal_heads n zeta _).1,(causal_heads n zeta _).2]

attribute [local irreducible] sourceEqualProjection sourcePinnedResolvent sourceFullInitialUpper
  sourceFullInitialBase sourceRetainerReturn sourceResonanceProjection sourceOffPoleReturn
  sourceUpperResidue sourceBaseResidue sourceGaugeResidue sourceOriginInverse

private theorem origin_projected (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (X : SourceOp) :
    sourceOriginInverse F n zeta (sourceEqualProjection F X)=
      sourcePinnedResolvent F n zeta*sourceEqualProjection F X := by
  have idem:=congrArg (fun A : SourceSuperOp=>A X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at idem
  simp only [sourceOriginInverse,add_apply,sourcePinnedLeadingInverse_apply,
    sourceOffProjection,sub_apply,one_apply_eq_self,idem,sub_self,add_zero]

/-- Both actual source initial sectors retain every pinned resonance and every nonresonant channel. -/
theorem sourceActual_upper_boundary (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    sourceUpperResidue q n (sourcePoleSide c eta) i=
      ((eta:ℂ)⁻¹ • sourceResonanceProjection q.F n c+sourceOffPoleReturn q.F n c eta)*
        sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i) := by
  rw [sourceUpperResidue,origin_projected,sourcePinnedResolvent_boundary q.F n c eta positive]

theorem sourceActual_base_boundary (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (i : Fin 289) :
    sourceBaseResidue q n (sourcePoleSide c eta) i=
      -(((eta:ℂ)⁻¹ • sourceResonanceProjection q.F n c+sourceOffPoleReturn q.F n c eta)*
        sourceEqualProjection q.F (sourceRetainerReturn q.F
          (((eta:ℂ)⁻¹ • sourceResonanceProjection q.F n c+sourceOffPoleReturn q.F n c eta)*
            sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))) := by
  unfold sourceBaseResidue
  apply congrArg (fun X : SourceOp=> -X)
  let U:=sourceUpperResidue q n (sourcePoleSide c eta) i
  let R:=(eta:ℂ)⁻¹ • sourceResonanceProjection q.F n c+sourceOffPoleReturn q.F n c eta
  calc
    sourceOriginInverse q.F n (sourcePoleSide c eta)
        (sourceEqualProjection q.F (sourceRetainerReturn q.F U))=
      sourcePinnedResolvent q.F n (sourcePoleSide c eta)*
        sourceEqualProjection q.F (sourceRetainerReturn q.F U) := origin_projected _ _ _ _
    _=R*sourceEqualProjection q.F (sourceRetainerReturn q.F U) :=
      congrArg (fun X : SourceOp=>X*sourceEqualProjection q.F (sourceRetainerReturn q.F U))
        (sourcePinnedResolvent_boundary q.F n c eta positive)
    _=R*sourceEqualProjection q.F (sourceRetainerReturn q.F
        (R*sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))) :=
      congrArg (fun X : SourceOp=>R*sourceEqualProjection q.F (sourceRetainerReturn q.F X))
        (sourceActual_upper_boundary q n c eta positive i)

theorem sourceActual_gauge_boundary (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (c eta : ℝ) (positive : 0<eta) (mu : Fin 4) (a : Fin 12) :
    sourceGaugeResidue q n (sourcePoleSide c eta) mu a=
      ((eta:ℂ)⁻¹ • sourceResonanceProjection q.F n c+sourceOffPoleReturn q.F n c eta)*
        sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (gaugeSlot mu a)) := by
  rw [sourceGaugeResidue,origin_projected,sourcePinnedResolvent_boundary q.F n c eta positive]

private theorem vertex_smul (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (z : ℂ) (v : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR l r (z • v)=z*sourceAmputatedFieldVertex q pL pR l r v := by
  simp only [sourceAmputatedFieldVertex,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

/-- The full quantum field is observed through the actual amputated matter-action vertex. -/
theorem sourceObservedField_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^3*
      sourceAmputatedFieldVertex q pL pR a b (sourceJointCausalField q n zeta.val l r d))
      (𝓝[>] 0) (𝓝 (sourceAmputatedFieldVertex q pL pR a b
        (sourceJointFieldResidue q n zeta.val l r))) := by
  have continuous : Continuous (sourceAmputatedFieldVertex q pL pR a b) := by
    unfold sourceAmputatedFieldVertex
    fun_prop
  have limit:=continuous.continuousAt.tendsto.comp
    (sourceJointCausalField_residue q n zeta l r nonrealL nonrealR)
  simpa only [Function.comp_def,vertex_smul] using limit

/-- Each signed propagation sheet has a generated field side and the same actual independent-leg observer. -/
theorem sourceObservedSide_residue (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (branch : Fin 2) (negative : Bool) (eta : ℝ) (positive : 0<eta)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun d : ℝ=>(d:ℂ)^3*sourceAmputatedFieldVertex q pL pR a b
      (sourceJointCausalField q n (sourcePoleSide (sourceSignedSpeed branch negative) eta) l r d))
      (𝓝[>] 0) (𝓝 (sourceAmputatedFieldVertex q pL pR a b
        (sourceJointFieldResidue q n (sourcePoleSide (sourceSignedSpeed branch negative) eta) l r))) :=
  sourceObservedField_residue q n (sourceObservedSide n branch negative eta positive)
    l r a b pL pR nonrealL nonrealR

end LowEnergy.PreparationVacuumObservedPoleTensor
