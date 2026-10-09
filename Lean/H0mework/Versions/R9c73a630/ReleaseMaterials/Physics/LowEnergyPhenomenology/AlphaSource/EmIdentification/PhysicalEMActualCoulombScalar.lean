import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualStaticWindow
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugePreparedStaticCEM
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCoframePreparedPotential

/-! Actual raw Coulomb scalar: the once-Coulomb `sourceGaugeStaticCEM`
contraction of the original `sourceCommonCoulombTensor` by the actual
detector returns `K*D_actual*W_cf` minus the complete leg correction,
with `K` the paid spatial inverse sum.  The detector projection is the
original `actual_origin_kernel_read`/`returnedCurrentWindow_zero` pair;
the source side consumes `sourceNativeSimple_prepared`. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin
open PreparationVacuumFullSlowFieldResponse PreparationVacuumStaticSimpleCoupling
open PreparationVacuumChargedSpatialResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalCommonObservableUnits
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalGaugePreparedStaticCEM
open PreparationPhysicalGaugeSpatialChannelExpansion PreparationPhysicalCoframePreparedReturn
open GaussComposite.PhysicalEMActualStaticWindow
open CanonicalGradedSpatialSource
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology InnerProductSpace

attribute [local irreducible]
  emActualJointKernel sourcePoleRead sourcePolePrepared
  actualCurrent returnedCurrentWindow
  sourceCommonDetector sourceActualPreparedDetector sourceActualPreparedKernel
  sourceActualPreparedWeight
  sourceActualLegNormalization sourceActualLegCorrection sourceGaugeActualCoulombField
  sourceGaugeStaticCEM sourceGaugeStaticAlpha sourceCoframePreparedStatic
  sourceNativeSimple sourceActualPreparedCurrent
  emStaticModeKernel emFullStaticKernel emCompensationStaticKernel
  emFullStaticWindow emCompensationStaticWindow

/-- All64 actual origin scalar: weighted `actualOriginWeight` over the
detector rest-pair labels. -/
def emActualOriginScalar (qd : PhysicalResponsePoint)
    (dSL dEL dSR dER : Fin 2) (T : ℝ) : ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
      actualOriginWeight qd 0 0 a b 0 T

/-- All64 coframe static scalar: weighted `sourcePoleRead` of the
original `sourceCoframePreparedStatic` over the source rest-pair
labels. -/
def emCoframeStaticScalar (q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (n : PhysicalMomentum) : ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 sL eL sR eR a b*
      sourcePoleRead q.epsilon q.precision 0 0 a b (sourceCoframePreparedStatic q n)

/-- The spatial inverse sum `K` paid as source arithmetic. -/
theorem em_spatial_inverse_sum_generated :
    (sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
      (sourceChargedSpatialCoefficient 1:ℂ)⁻¹=
      (9023/9000:ℂ)*rootTwo*rootFifteen := by
  have htwo : rootTwo≠0 := by unfold rootTwo;norm_cast;positivity
  have hfifteen : rootFifteen≠0 := by unfold rootFifteen;norm_cast;positivity
  have htwo_sq : rootTwo^2=2 := by
    norm_cast
    norm_num [rootTwo,←Complex.ofReal_pow,Real.sq_sqrt]
  have hfifteen_sq : rootFifteen^2=15 := by
    norm_cast
    norm_num [rootFifteen,←Complex.ofReal_pow,Real.sq_sqrt]
  have coef0 : (sourceChargedSpatialCoefficient 0:ℂ) =
      (rootTwo*rootFifteen)*(25/54:ℂ) := by
    norm_num [sourceChargedSpatialCoefficient,rootTwo,rootFifteen]
  have coef1 : (sourceChargedSpatialCoefficient 1:ℂ) =
      (rootTwo*rootFifteen)*(12/335:ℂ) := by
    norm_num [sourceChargedSpatialCoefficient,rootTwo,rootFifteen]
  rw [coef0,coef1]
  field_simp [htwo,hfifteen]
  ring_nf
  simp only [htwo_sq,hfifteen_sq]
  norm_num

/-- `fiveVector` of a single is the original single. -/
private theorem em_fiveVector_single (i : Fin 5) :
    fiveVector (Pi.single i 1)=Pi.single (fiveIndex i) 1 := by
  funext j
  simp only [fiveVector,fiveIndex,Pi.single_apply,Fin.ext_iff]
  by_cases h : j.val<5
  · rw [dif_pos h]
  · rw [dif_neg h,if_neg (by omega)]

/-- Channel-zero slow read of the origin pair. -/
private theorem em_slowFast_origin_zero (w : ℂ) :
    (slowFastFrame.transpose*ᵥ(Pi.single 0 w+Pi.single 1 w)) ⟨0,by decide⟩=w := by
  simp only [Matrix.mulVec_add,Matrix.mulVec_single,Pi.add_apply]
  norm_num [slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,
    Powers.value,coefficientValue,Matrix.single_apply,Matrix.transpose_apply,
    Fin.ext_iff,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]

/-- Channel-one slow read of the origin pair. -/
private theorem em_slowFast_origin_one (w : ℂ) :
    (slowFastFrame.transpose*ᵥ(Pi.single 0 w+Pi.single 1 w)) ⟨1,by decide⟩=w := by
  simp only [Matrix.mulVec_add,Matrix.mulVec_single,Pi.add_apply]
  norm_num [slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,
    Powers.value,coefficientValue,Matrix.single_apply,Matrix.transpose_apply,
    Fin.ext_iff,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]

/-- Channel-two slow read of the origin pair. -/
private theorem em_slowFast_origin_two (w : ℂ) :
    (slowFastFrame.transpose*ᵥ(Pi.single 0 w+Pi.single 1 w)) ⟨2,by decide⟩=0 := by
  simp only [Matrix.mulVec_add,Matrix.mulVec_single,Pi.add_apply]
  norm_num [slowFastFrame,slowFastFrameTerms,sourceMatrix,SourceTerm.matrix,
    Powers.value,coefficientValue,Matrix.single_apply,Matrix.transpose_apply,
    Fin.ext_iff,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_zero,QuadraticAlgebra.im_zero]

/-- `sourceSlowRead` of the origin pair gives `w` on channels 0/1 and 0
on channel 2, because the public slowFastFrame mixes only the pair
indices. -/
private theorem em_slowRead_origin_pair (j : Fin 3) (w : ℂ) :
    sourceSlowRead (sourceOriginPair w) ⟨j.val,by omega⟩=
      (if j.val=2 then (0:ℂ) else w) := by
  unfold sourceSlowRead sourceOriginPair
  rw [if_pos (by omega : j.val<3)]
  fin_cases j <;>
    simp only [fiveIndex,em_slowFast_origin_zero,em_slowFast_origin_one,
      em_slowFast_origin_two] <;>
    norm_num

/-- Per-pair detector contraction of an origin column returns the slow
read of the actual origin pair through the original
`actual_origin_kernel_read`. -/
theorem em_detector_column (qd : PhysicalResponsePoint) (a b : RestStateIndex) (T : ℝ)
    (i : Fin 3) :
    sourceCommonDetector qd 0 0 a b 0 T (sourceCommonOriginColumn i)=
      sourceSlowRead (sourceOriginPair (actualOriginWeight qd 0 0 a b 0 T))
        ⟨i.val,by omega⟩ := by
  rw [sourceCommonDetector_current,
    show (∑j : Fin 289,returnedCurrentWindow qd 0 0 a b 0 T j*
        sourceCommonOriginColumn i j)=
      dotProduct (returnedCurrentWindow qd 0 0 a b 0 T) (sourceCommonOriginColumn i)
        from rfl]
  rw [returnedCurrentWindow_zero]
  unfold sourceCommonOriginColumn
  rw [show (originalChange 0*fullKernelFrame*slowFastFrame)=fullNativeOrigin*slowFastFrame from rfl]
  rw [Matrix.dotProduct_mulVec,
    ←Matrix.transpose_transpose (fullNativeOrigin*slowFastFrame),
    Matrix.vecMul_transpose,Matrix.transpose_mul,←Matrix.mulVec_mulVec]
  rw [actual_origin_kernel_read]
  rw [show (Pi.single 0 ((3/10:ℂ)*rootTwo*
        (actualCurrent qd 0 0 a b 0 T 21-actualCurrent qd 0 0 a b 0 T 34))+
      Pi.single 1 ((3/10:ℂ)*rootTwo*
        (actualCurrent qd 0 0 a b 0 T 21-actualCurrent qd 0 0 a b 0 T 34)))=
      sourceOriginPair (actualOriginWeight qd 0 0 a b 0 T) from rfl]
  rw [em_fiveVector_single,dotProduct_single,mul_one]
  unfold sourceSlowRead
  rw [if_pos (by omega : i.val<3)]

/-- Per-pair detector contraction of the original three-channel Coulomb
tensor returns the inverse-sum `D` times `W`. -/
theorem em_detector_tensor_scalar (qd q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (aD bD aS bS : RestStateIndex) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceCommonDetector qd 0 0 aD bD 0 T (sourceCommonCoulombTensor q n aS bS)=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        actualOriginWeight qd 0 0 aD bD 0 T)*
        sourcePoleRead q.epsilon q.precision 0 0 aS bS (sourceCoframePreparedStatic q n) := by
  unfold sourceCommonCoulombTensor
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  rw [Fin.sum_univ_three]
  rw [sourceNativeSimple_prepared q n aS bS hz hw]
  simp only [em_detector_column qd aD bD T 0,em_detector_column qd aD bD T 1,
    em_detector_column qd aD bD T 2,em_slowRead_origin_pair]
  norm_num
  ring

/-- The prepared weighted detector on the Coulomb tensor returns
`K*D_actual*W` for each source pair. -/
theorem em_preparedDetector_tensor_scalar (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER : Fin 2) (n : PhysicalMomentum)
    (aS bS : RestStateIndex) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
        (sourceCommonCoulombTensor q n aS bS)=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        emActualOriginScalar qd dSL dEL dSR dER T)*
        sourcePoleRead q.epsilon q.precision 0 0 aS bS (sourceCoframePreparedStatic q n) := by
  unfold sourceActualPreparedDetector
  simp only [sum_apply,smul_apply,smul_eq_mul]
  have term (a b : RestStateIndex) :
      sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
        (sourceCommonDetector qd 0 0 a b 0 T) (sourceCommonCoulombTensor q n aS bS)=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        sourcePoleRead q.epsilon q.precision 0 0 aS bS (sourceCoframePreparedStatic q n))*
        (sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
          actualOriginWeight qd 0 0 a b 0 T) := by
    rw [em_detector_tensor_scalar qd q n a b aS bS T hz hw]
    ring
  rw [Finset.sum_congr rfl (fun a _=>Finset.sum_congr rfl (fun b _=>term a b))]
  have fold : (∑a : RestStateIndex,∑b : RestStateIndex,
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        sourcePoleRead q.epsilon q.precision 0 0 aS bS (sourceCoframePreparedStatic q n))*
        (sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
          actualOriginWeight qd 0 0 a b 0 T))=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        sourcePoleRead q.epsilon q.precision 0 0 aS bS (sourceCoframePreparedStatic q n))*
        ∑a : RestStateIndex,∑b : RestStateIndex,
          sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
            actualOriginWeight qd 0 0 a b 0 T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [fold]
  unfold emActualOriginScalar
  ring

/-- The outer weighted contraction is `K*D_actual*W_cf`. -/
theorem em_outer_scalar_generated (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    (∑a : RestStateIndex,∑b : RestStateIndex,
      sourceActualPreparedWeight 0 0 sL eL sR eR a b*
        sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
          (sourceCommonCoulombTensor q n a b))=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        emActualOriginScalar qd dSL dEL dSR dER T)*
        emCoframeStaticScalar q sL eL sR eR n := by
  have term (a b : RestStateIndex) :
      sourceActualPreparedWeight 0 0 sL eL sR eR a b*
        sourceActualPreparedDetector qd 0 0 dSL dEL dSR dER 0 T
          (sourceCommonCoulombTensor q n a b)=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        emActualOriginScalar qd dSL dEL dSR dER T)*
        (sourceActualPreparedWeight 0 0 sL eL sR eR a b*
          sourcePoleRead q.epsilon q.precision 0 0 a b (sourceCoframePreparedStatic q n)) := by
    rw [em_preparedDetector_tensor_scalar qd q dSL dEL dSR dER n a b T hz hw]
    ring
  rw [Finset.sum_congr rfl (fun a _=>Finset.sum_congr rfl (fun b _=>term a b))]
  have fold : (∑a : RestStateIndex,∑b : RestStateIndex,
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        emActualOriginScalar qd dSL dEL dSR dER T)*
        (sourceActualPreparedWeight 0 0 sL eL sR eR a b*
          sourcePoleRead q.epsilon q.precision 0 0 a b (sourceCoframePreparedStatic q n)))=
      (((sourceChargedSpatialCoefficient 0:ℂ)⁻¹+
        (sourceChargedSpatialCoefficient 1:ℂ)⁻¹)*
        emActualOriginScalar qd dSL dEL dSR dER T)*
        ∑a : RestStateIndex,∑b : RestStateIndex,
          sourceActualPreparedWeight 0 0 sL eL sR eR a b*
            sourcePoleRead q.epsilon q.precision 0 0 a b (sourceCoframePreparedStatic q n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [fold]
  unfold emCoframeStaticScalar
  ring

/-- The once-Coulomb raw CEM coefficient is the leg normalization times
`K*D_actual*W_cf` minus the complete leg correction. -/
theorem em_staticCEM_scalar_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*
          emActualOriginScalar qd dSL dEL dSR dER T*
          emCoframeStaticScalar q sL eL sR eR n-
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceGaugeActualCoulombField q sL eL sR eR n))) := by
  rw [sourceGaugeStaticCEM_generated branch qd q dSL dEL dSR dER sL eL sR eR T n hzd hwd]
  have nonzero : ((ActionNormalization.phaseMomentum*sourceSpeed branch : ℝ):ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (mul_pos ActionNormalization.phaseMomentum_positive
      (sourceSpeed_positive branch)).ne'
  rw [em_outer_scalar_generated qd q dSL dEL dSR dER sL eL sR eR T n hz hw]
  rw [em_spatial_inverse_sum_generated]
  field_simp [nonzero]

/-- The dimensionless alpha read is the same coefficient divided once by
the original phase-momentum/speed product. -/
theorem em_staticAlpha_scalar_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticAlpha branch qd q dSL dEL dSR dER sL eL sR eR T n=
      (((ActionNormalization.phaseMomentum*sourceSpeed branch : ℝ):ℂ)⁻¹)*
        (sourceActualLegNormalization qd dSL dEL dSR dER*
          (((9023/9000:ℂ)*rootTwo*rootFifteen)*
            emActualOriginScalar qd dSL dEL dSR dER T*
            emCoframeStaticScalar q sL eL sR eR n-
            sourceActualLegCorrection qd dSL dEL dSR dER
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL eL sR eR n)))) := by
  unfold sourceGaugeStaticAlpha
  rw [em_staticCEM_scalar_generated branch qd q dSL dEL dSR dER sL eL sR eR T n hzd hwd hz hw]

/-- The raw CEM scalar with the actual-origin window split exposed: the
full original field-configuration window plus the source compensation
window. -/
theorem em_staticCEM_window_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*
          ((∑a : RestStateIndex,∑b : RestStateIndex,
              sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
                emFullStaticWindow qd 0 0 a b 0 T)+
            (∑a : RestStateIndex,∑b : RestStateIndex,
              sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
                emCompensationStaticWindow qd 0 0 a b 0 T))*
          emCoframeStaticScalar q sL eL sR eR n-
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceGaugeActualCoulombField q sL eL sR eR n))) := by
  have split : emActualOriginScalar qd dSL dEL dSR dER T=
      (∑a : RestStateIndex,∑b : RestStateIndex,
        sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
          emFullStaticWindow qd 0 0 a b 0 T)+
      (∑a : RestStateIndex,∑b : RestStateIndex,
        sourceActualPreparedWeight 0 0 dSL dEL dSR dER a b*
          emCompensationStaticWindow qd 0 0 a b 0 T) := by
    unfold emActualOriginScalar
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [←mul_add,em_actual_origin_window_split]
  rw [em_staticCEM_scalar_generated branch qd q dSL dEL dSR dER sL eL sR eR T n hzd hwd hz hw,
    split]

end LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar
