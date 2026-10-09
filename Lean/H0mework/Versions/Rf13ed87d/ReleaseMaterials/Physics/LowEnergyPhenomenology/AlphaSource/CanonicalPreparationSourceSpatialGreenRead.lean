import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSimpleRadialScale
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticSpatialSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumObservedPoleTensor PreparationVacuumObservedStaticResidue
open PreparationVacuumStaticSimpleCoupling PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumQuantumSlowResidue PreparationVacuumSharedPoleCarrier
open PreparationVacuumQuantumSlowResponse PreparationVacuumPhysicalSlowBlock
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumGaugeSlowFrequency
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalPoleAmputation
open PreparationVacuumCausalPoleResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCharacteristic
open CanonicalGradedSpatialSource MeasureTheory Filter Set
open scoped Matrix BigOperators Topology SchwartzMap Matrix.Norms.Operator
attribute [local irreducible] sourcePinnedVelocity sourceVelocityLinear sourceEqualProjection sourceRetainerReturn
  sourceFullInitialUpper sourceFullInitialBase sourcePoleRead sourceNativeReaderFirst
  fullKernelFrame activeProjection fullInverse originalReadback sourcePoleEulerInitial
  sourcePoleMaterialPairGap sourceJointFieldResidue sourceAmputatedFieldVertex sourcePinnedResolvent
  sourceOriginInverse sourceBaseResidue sourceUpperResidue sourceFullCurrentResidue sourceGaugeCurrentResidue

private theorem pinned_continuous (F : GaussUnitaryHistory.Index) : Continuous (sourcePinnedVelocity F) := by
  have velocity:=(sourceVelocityLinear F).toContinuousLinearMap.continuous
  unfold sourcePinnedVelocity
  exact (sourceEqualProjection F).continuous.comp (show Continuous (sourceVelocityLinear F) from velocity)

private theorem inverse_family_continuous {D R : Type*} [TopologicalSpace D] [NormedRing R]
    [HasSummableGeomSeries R] (f : D→R) (continuous : Continuous f)
    (unit : ∀n,IsUnit (f n)) : Continuous (fun n=>Ring.inverse (f n)) := by
  apply continuous_iff_continuousAt.mpr
  intro n
  obtain ⟨u,hu⟩:=unit n
  have inverseAt : ContinuousAt Ring.inverse (f n) := by
    rw [←hu]
    exact NormedRing.inverse_continuousAt u
  simpa only [Function.comp_def] using inverseAt.comp (f:=f) (g:=Ring.inverse) (x:=n) continuous.continuousAt

private theorem resolvent_continuous (F : GaussUnitaryHistory.Index) (zeta : ℂ) (positive : 0<zeta.re) :
    Continuous (fun n : PhysicalMomentum=>sourcePinnedResolvent F n zeta) := by
  have nonreal : (Complex.I*zeta).im≠0 := by
    simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using positive.ne'
  have inverse:=inverse_family_continuous
    (fun n : PhysicalMomentum=>sourcePinnedVelocity F n-(Complex.I*zeta) • (1:SourceOp))
    ((pinned_continuous F).sub continuous_const)
    (fun n=>FullYSourceResolventGraphSplice.resolvent_isUnit
      (sourcePinnedVelocity F n) (sourcePinnedVelocity_selfAdjoint F n) (Complex.I*zeta) nonreal)
  unfold sourcePinnedResolvent FullYSourceResolventGraphSplice.resolvent
  exact inverse.const_smul (-Complex.I)

private theorem projected_origin (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (X : SourceOp) :
    sourceOriginInverse F n zeta (sourceEqualProjection F X)=
      sourcePinnedResolvent F n zeta*sourceEqualProjection F X := by
  have idem:=congrArg (fun A : SourceSuperOp=>A X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at idem
  simp only [sourceOriginInverse,add_apply,sourcePinnedLeadingInverse_apply,
    sourceOffProjection,sub_apply,one_apply_eq_self,idem,sub_self,add_zero]

private theorem retained_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (i : Fin 289) :
    ‖sourceBaseResidue q n zeta i‖≤(1/zeta.re)^2*‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖*
      ‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖ := by
  simp only [sourceBaseResidue,sourceUpperResidue,projected_origin,norm_neg]
  have price:=sourcePinnedResolvent_price q.F n zeta positive
  have nonnegative : 0≤1/zeta.re := by positivity
  calc
    _≤‖sourcePinnedResolvent q.F n zeta‖*‖sourceEqualProjection q.F
      (sourceRetainerReturn q.F (sourcePinnedResolvent q.F n zeta*sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))‖ := norm_mul_le _ _
    _≤‖sourcePinnedResolvent q.F n zeta‖*(‖sourceEqualProjection q.F‖*
      (‖sourceRetainerReturn q.F‖*(‖sourcePinnedResolvent q.F n zeta‖*
        ‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖))) := by
      gcongr
      exact (sourceEqualProjection q.F).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_left ((sourceRetainerReturn q.F).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _≤(1/zeta.re)*(‖sourceEqualProjection q.F‖*(‖sourceRetainerReturn q.F‖*
      ((1/zeta.re)*‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖))) := by gcongr
    _=_ := by ring

/-- The full source current's uniform causal price retains the actual B1 and retainer. -/
def sourceSpatialCurrentPrice (q : PhysicalResponsePoint) (eta : ℝ) (l r : RestStateIndex) : ℝ :=
  ‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*(1/eta)^2*
    ‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖*
      ∑i : Fin 289,‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖

private theorem vector_reader_price {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype ι] (L : E→L[ℂ] ℂ) (X : ι→E) (B : ι→ℝ) (C : ℝ)
    (nonnegative : 0≤C) (budget : ∀i,0≤B i) (bound : ∀i,‖X i‖≤C*B i) :
    ‖fun i=> -L (X i)‖≤‖L‖*C*∑i,B i := by
  classical
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg L) nonnegative) (Finset.sum_nonneg (fun i _=>budget i)))).mpr
  intro i
  rw [norm_neg]
  apply (L.le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_left (bound i) (norm_nonneg _)).trans
  have single : B i≤∑j,B j := Finset.single_le_sum (fun j _=>budget j) (Finset.mem_univ i)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left single (mul_nonneg (norm_nonneg L) nonnegative)

private theorem current_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) :
    ‖sourceFullCurrentResidue q n zeta l r‖≤ sourceSpatialCurrentPrice q zeta.re l r := by
  have h:=vector_reader_price (sourcePoleRead q.epsilon q.precision 0 0 l r)
    (fun i : Fin 289=>sourceBaseResidue q n zeta i)
    (fun i : Fin 289=>‖sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)‖)
    ((1/zeta.re)^2*‖sourceEqualProjection q.F‖*‖sourceRetainerReturn q.F‖)
    (by positivity) (fun i=>norm_nonneg _) (fun i=>by simpa only [mul_assoc] using retained_bound q n zeta positive i)
  unfold sourceFullCurrentResidue
  simpa only [sourceSpatialCurrentPrice,mul_assoc] using h

private theorem gauge_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    ‖sourceGaugeCurrentResidue q n zeta l r mu a‖≤
      ‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*(1/zeta.re)*
        ‖sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (PreparationVacuumMixedFieldReturn.gaugeSlot mu a))‖ := by
  simp only [sourceGaugeCurrentResidue,sourceGaugeResidue,projected_origin,norm_neg]
  apply ((sourcePoleRead q.epsilon q.precision 0 0 l r).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)).trans
  have price:=sourcePinnedResolvent_price q.F n zeta positive
  calc
    _≤‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*((1/zeta.re)*
      ‖sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (PreparationVacuumMixedFieldReturn.gaugeSlot mu a))‖) := by gcongr
    _=_ := by ring

/-- The original gauge B0 price is generated on its actual two origin current entries. -/
def sourceSpatialGaugePrice (q : PhysicalResponsePoint) (eta : ℝ) (l r : RestStateIndex) : ℝ :=
  ‖(3/10:ℂ)*rootTwo‖*‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*(1/eta)*
    (‖sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (PreparationVacuumMixedFieldReturn.gaugeSlot 1 0))‖+
     ‖sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (PreparationVacuumMixedFieldReturn.gaugeSlot 2 1))‖)

private theorem origin_bound (q : PhysicalResponsePoint) (n : PhysicalMomentum) (zeta : ℂ)
    (positive : 0<zeta.re) (l r : RestStateIndex) :
    ‖sourceOriginCurrentResidue q n zeta l r‖≤ sourceSpatialGaugePrice q zeta.re l r := by
  apply (pi_norm_le_iff_of_nonneg (by unfold sourceSpatialGaugePrice;positivity)).mpr
  intro i
  unfold sourceOriginCurrentResidue sourceOriginPair
  by_cases zero : i=0
  · subst i
    simp only [Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (0:Fin 289)≠1),add_zero,norm_mul]
    rw [←norm_mul]
    apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add (gauge_bound q n zeta positive l r 1 0)
      (gauge_bound q n zeta positive l r 2 1)) (norm_nonneg _)).trans_eq
    unfold sourceSpatialGaugePrice
    ring
  · by_cases one : i=1
    · subst i
      simp only [Pi.add_apply,Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (1:Fin 289)≠0),zero_add,norm_mul]
      rw [←norm_mul]
      apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_left (add_le_add (gauge_bound q n zeta positive l r 1 0)
        (gauge_bound q n zeta positive l r 2 1)) (norm_nonneg _)).trans_eq
      unfold sourceSpatialGaugePrice
      ring
    · simp only [Pi.add_apply,Pi.single_eq_of_ne zero,Pi.single_eq_of_ne one,zero_add,norm_zero]
      unfold sourceSpatialGaugePrice
      positivity

private theorem spatial_coordinate_temperate (zeta : ℂ) (i : Fin 4) :
    Function.HasTemperateGrowth (fun n : PhysicalMomentum=>fixedMomentum n zeta i) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact Function.HasTemperateGrowth.const _
  · change Function.HasTemperateGrowth (fun n : PhysicalMomentum=>Complex.I*(n j:ℂ))
    have real:=(Complex.ofRealCLM.comp (ContinuousLinearMap.proj j : PhysicalMomentum→L[ℝ] ℝ)).hasTemperateGrowth
    exact (Function.HasTemperateGrowth.const _).mul real

private theorem source_matrix_temperate (terms : List SourceTerm) (zeta : ℂ) :
    Function.HasTemperateGrowth (fun n : PhysicalMomentum=>sourceMatrix terms (fixedMomentum n zeta)) := by
  induction terms with
  | nil=>exact Function.HasTemperateGrowth.const _
  | cons a rest ih=>
    have powers : Function.HasTemperateGrowth (fun n : PhysicalMomentum=>a.powers.value (fixedMomentum n zeta)) :=
      (((spatial_coordinate_temperate zeta 0).pow a.powers.temporal).mul
        ((spatial_coordinate_temperate zeta 1).pow a.powers.first)).mul
        ((spatial_coordinate_temperate zeta 2).pow a.powers.second) |>.mul
        ((spatial_coordinate_temperate zeta 3).pow a.powers.third)
    have term:=powers.smul (Function.HasTemperateGrowth.const (Matrix.single a.row a.column (coefficientValue a.coefficient)))
    have same : (fun n : PhysicalMomentum=>a.matrix (fixedMomentum n zeta))=
        fun n=>a.powers.value (fixedMomentum n zeta) • Matrix.single a.row a.column (coefficientValue a.coefficient) := by
      funext n
      ext i j
      simp only [SourceTerm.matrix,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
      split_ifs <;> ring
    have term' : Function.HasTemperateGrowth (fun n : PhysicalMomentum=>a.matrix (fixedMomentum n zeta)) := by
      rw [same]
      exact term
    have sameSum : (fun n : PhysicalMomentum=>sourceMatrix (a::rest) (fixedMomentum n zeta))=
        (fun n=>a.matrix (fixedMomentum n zeta))+(fun n=>sourceMatrix rest (fixedMomentum n zeta)) := by
      funext n
      exact sourceMatrix_cons a rest _
    rw [sameSum]
    exact term'.add ih

private theorem reader_temperate (zeta : ℂ) :
    Function.HasTemperateGrowth (fun n : PhysicalMomentum=>sourceNativeReaderFirst (fixedMomentum n zeta)) := by
  unfold sourceNativeReaderFirst sourceLinearPart degreeTensor
  exact ((Function.HasTemperateGrowth.const _).mul (source_matrix_temperate _ zeta)).sub
    (((((Function.HasTemperateGrowth.const _).mul (source_matrix_temperate _ zeta)).mul
      (Function.HasTemperateGrowth.const _)).mul (Function.HasTemperateGrowth.const _)).mul
      (Function.HasTemperateGrowth.const _))

/-- The same physical frequency-to-momentum map used by the original all-space matter dynamics. -/
def sourceSpatialMomentum (frequency : PhysicalMomentum) : PhysicalMomentum :=
  (2*Real.pi) • frequency

theorem sourceSpatialMomentum_original (frequency : FullQuantum.FullSpace.Position) :
    sourceSpatialMomentum (fun j=>frequency j)=FullQuantum.FullSpace.physicalMomentum frequency := rfl

private theorem momentum_temperate : Function.HasTemperateGrowth sourceSpatialMomentum := by
  exact ((2*Real.pi) • (ContinuousLinearMap.id ℝ PhysicalMomentum)).hasTemperateGrowth

private theorem weighted_reader_integrable (zeta : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun frequency=>‖test frequency‖*‖sourceNativeReaderFirst (fixedMomentum (sourceSpatialMomentum frequency) zeta)‖) := by
  have poly:=(reader_temperate zeta).comp momentum_temperate
  have h:=(SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ) poly test).integrable (μ:=volume) |>.norm
  simpa only [SchwartzMap.bilinLeftCLM_apply,ContinuousLinearMap.lsmul_apply,norm_smul,Function.comp_def] using h

private theorem current_continuous (q : PhysicalResponsePoint) (zeta : ℂ) (positive : 0<zeta.re)
    (l r : RestStateIndex) : Continuous (fun n : PhysicalMomentum=>sourceFullCurrentResidue q n zeta l r) := by
  apply continuous_pi
  intro i
  have resolvent:=resolvent_continuous q.F zeta positive
  simp only [sourceFullCurrentResidue,sourceBaseResidue,sourceUpperResidue,projected_origin]
  fun_prop

private theorem origin_continuous (q : PhysicalResponsePoint) (zeta : ℂ) (positive : 0<zeta.re)
    (l r : RestStateIndex) : Continuous (fun n : PhysicalMomentum=>sourceOriginCurrentResidue q n zeta l r) := by
  have resolvent:=resolvent_continuous q.F zeta positive
  apply continuous_pi
  intro i
  simp only [sourceOriginCurrentResidue,sourceOriginPair,Pi.single_apply,Pi.add_apply,
    sourceGaugeCurrentResidue,sourceGaugeResidue,projected_origin]
  split_ifs <;> fun_prop

def sourceDetectorImaginary (c eta : ℝ) (i : Fin 2) : ℝ :=
  Real.sqrt 2*Real.sqrt 15*(if i=0 then -(25/9:ℝ) else 20/99)*eta*c

private theorem detector_imaginary (n : PhysicalMomentum) (c eta : ℝ) (i : Fin 2) :
    (sourceCanonicalDenominator n (sourcePoleSide c eta) i).im=sourceDetectorImaginary c eta i := by
  fin_cases i <;> norm_num [sourceCanonicalDenominator,sourcePoleSide,sourceDetectorImaginary,
    rootTwo,rootFifteen,pow_two,Complex.mul_im,Complex.mul_re] <;> ring

private theorem detector_imaginary_ne (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (i : Fin 2) :
    sourceDetectorImaginary c eta i≠0 := by
  have coefficient : (if i=0 then -(25/9:ℝ) else 20/99)≠0 := by split_ifs <;> norm_num
  unfold sourceDetectorImaginary
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) coefficient) positive.ne') frequency

def sourceDetectorPrice (c eta : ℝ) (i : Fin 2) : ℝ := |sourceDetectorImaginary c eta i|⁻¹

private theorem detector_price (n : PhysicalMomentum) (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (i : Fin 2) :
    ‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖≤ sourceDetectorPrice c eta i := by
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr (detector_imaginary_ne c eta frequency positive i))
  rw [←detector_imaginary n c eta i]
  exact Complex.abs_im_le_norm _

private theorem slow_bound (v : Fin 289→ℂ) (i : Fin 5) :
    ‖sourceSlowRead v i‖≤‖slowFastFrame.transpose‖*‖v‖ := by
  unfold sourceSlowRead
  split_ifs
  · exact (norm_le_pi_norm _ _).trans (Matrix.linfty_opNorm_mulVec _ _)
  · rw [norm_zero]
    positivity

/-- Actual complete field observation at a source propagation side, retaining all current and detector legs. -/
def sourceSpatialResponse (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) (n : PhysicalMomentum) : ℂ :=
  sourceAmputatedFieldVertex q pL pR a b
    (sourceJointFieldResidue q n (sourcePoleSide (sourceSignedSpeed branch negative) eta) l r)

def sourceSpatialDetectorPrice (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℝ :=
  ‖-sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)‖*
    (sourceDetectorPrice (sourceSignedSpeed branch negative) eta 0+
      sourceDetectorPrice (sourceSignedSpeed branch negative) eta 1)*‖slowFastFrame.transpose‖

private theorem response_bound (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (n : PhysicalMomentum) :
    ‖sourceSpatialResponse q branch negative eta l r a b pL pR n‖≤
      sourceSpatialDetectorPrice q branch negative eta a b pL pR*
        (sourceSpatialGaugePrice q eta l r+
          ‖sourceNativeReaderFirst (fixedMomentum n (sourcePoleSide (sourceSignedSpeed branch negative) eta))‖*
            sourceSpatialCurrentPrice q eta l r) := by
  let zeta:=sourceObservedSide n branch negative eta positive
  have realPart : zeta.val.re=eta := by simp [zeta,sourceObservedSide,sourcePoleSide]
  have native : ‖sourceActualNativeResidue q n zeta.val l r‖≤ sourceSpatialGaugePrice q eta l r+
      ‖sourceNativeReaderFirst (fixedMomentum n zeta.val)‖*sourceSpatialCurrentPrice q eta l r := by
    unfold sourceActualNativeResidue
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [realPart] using origin_bound q n zeta.val zeta.property.1 l r
    · exact (Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_left (by simpa only [realPart] using current_bound q n zeta.val zeta.property.1 l r) (norm_nonneg _))
  have cnonzero:=sourceSignedSpeed_nonzero branch negative
  have bound (i : Fin 2) :
      ‖(sourceCanonicalDenominator n zeta.val i)⁻¹*sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) ⟨i.val,by omega⟩‖≤
        sourceDetectorPrice (sourceSignedSpeed branch negative) eta i*‖slowFastFrame.transpose‖*
          (sourceSpatialGaugePrice q eta l r+‖sourceNativeReaderFirst (fixedMomentum n zeta.val)‖*sourceSpatialCurrentPrice q eta l r) := by
    rw [norm_mul]
    apply (mul_le_mul (detector_price n _ eta cnonzero positive i) (slow_bound _ _) (norm_nonneg _)
      (by unfold sourceDetectorPrice;positivity)).trans
    calc
      _=sourceDetectorPrice (sourceSignedSpeed branch negative) eta i*‖slowFastFrame.transpose‖*
        ‖sourceActualNativeResidue q n zeta.val l r‖ := by ring
      _≤_ := mul_le_mul_of_nonneg_left native (by unfold sourceDetectorPrice;positivity)
  have tensor:=sourceObservedField_tensor q n zeta l r a b pL pR nonrealL nonrealR
  dsimp only [zeta,sourceObservedSide] at tensor bound
  rw [sourceSpatialResponse,tensor,norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (bound 0) (bound 1)) (norm_nonneg _)).trans_eq
  unfold sourceSpatialDetectorPrice
  ring

private theorem response_continuous (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (sourceSpatialResponse q branch negative eta l r a b pL pR) := by
  let zeta:=sourcePoleSide (sourceSignedSpeed branch negative) eta
  have realPart : zeta.re=eta := by simp [zeta,sourcePoleSide]
  have causal : 0<zeta.re := by rwa [realPart]
  have current:=current_continuous q zeta causal l r
  have origin:=origin_continuous q zeta causal l r
  have reader:=(reader_temperate zeta).1.continuous
  have native : Continuous (fun n : PhysicalMomentum=>sourceActualNativeResidue q n zeta l r) :=
    origin.add (reader.matrix_mulVec current)
  have slow (i : Fin 5) : Continuous (fun n : PhysicalMomentum=>sourceSlowRead (sourceActualNativeResidue q n zeta l r) i) := by
    unfold sourceSlowRead
    split_ifs <;> fun_prop
  have denominator (i : Fin 2) : Continuous (fun n : PhysicalMomentum=>(sourceCanonicalDenominator n zeta i)⁻¹) := by
    have continuous : Continuous (fun n : PhysicalMomentum=>sourceCanonicalDenominator n zeta i) := by
      unfold sourceCanonicalDenominator spatialSquare
      split_ifs <;> fun_prop
    apply continuous.inv₀
    intro n zero
    have imaginary:=congrArg Complex.im zero
    rw [detector_imaginary n _ eta i,Complex.zero_im] at imaginary
    exact detector_imaginary_ne _ eta (sourceSignedSpeed_nonzero branch negative) positive i imaginary
  have same : sourceSpatialResponse q branch negative eta l r a b pL pR=
      fun n=> -sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)*
        ((sourceCanonicalDenominator n zeta 0)⁻¹*sourceSlowRead (sourceActualNativeResidue q n zeta l r) 0+
          (sourceCanonicalDenominator n zeta 1)⁻¹*sourceSlowRead (sourceActualNativeResidue q n zeta l r) 1) := by
    funext n
    exact sourceObservedField_tensor q n (sourceObservedSide n branch negative eta positive) l r a b pL pR nonrealL nonrealR
  rw [same]
  exact continuous_const.mul (((denominator 0).mul (slow 0)).add ((denominator 1).mul (slow 1)))

/-- Original physical momentum fixes the inverse spatial phase, including its existing 2*pi convention. -/
def sourceSpatialPhase (frequency position : PhysicalMomentum) : ℂ :=
  Complex.exp (Complex.I*((∑j,sourceSpatialMomentum frequency j*position j : ℝ):ℂ))

private theorem spatial_phase_norm (frequency position : PhysicalMomentum) : ‖sourceSpatialPhase frequency position‖=1 := by
  simp [sourceSpatialPhase,Complex.norm_exp]

/-- Full angular causal response read against an original-carrier Schwartz preparation. -/
def sourceSpatialIntegrand (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) (test : 𝓢(PhysicalMomentum,ℂ))
    (position frequency : PhysicalMomentum) : ℂ :=
  sourceSpatialPhase frequency position*test frequency*
    sourceSpatialResponse q branch negative eta l r a b pL pR (sourceSpatialMomentum frequency)

def sourceSpatialRead (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) (test : 𝓢(PhysicalMomentum,ℂ))
    (position : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceSpatialIntegrand q branch negative eta l r a b pL pR test position frequency

def sourceSpatialReadPrice (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) (test : 𝓢(PhysicalMomentum,ℂ)) : ℝ :=
  sourceSpatialDetectorPrice q branch negative eta a b pL pR*
    (sourceSpatialGaugePrice q eta l r*(∫frequency,‖test frequency‖)+
      sourceSpatialCurrentPrice q eta l r*(∫frequency,‖test frequency‖*
        ‖sourceNativeReaderFirst (fixedMomentum (sourceSpatialMomentum frequency) (sourcePoleSide (sourceSignedSpeed branch negative) eta))‖))

private theorem spatial_majorant_integrable (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun frequency=>sourceSpatialDetectorPrice q branch negative eta a b pL pR*
      (sourceSpatialGaugePrice q eta l r*‖test frequency‖+
        sourceSpatialCurrentPrice q eta l r*(‖test frequency‖*
          ‖sourceNativeReaderFirst (fixedMomentum (sourceSpatialMomentum frequency) (sourcePoleSide (sourceSignedSpeed branch negative) eta))‖))) :=
  ((test.integrable.norm.const_mul _).add ((weighted_reader_integrable _ test).const_mul _)).const_mul _

private theorem spatial_integrand_price (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ))
    (position frequency : PhysicalMomentum) :
    ‖sourceSpatialIntegrand q branch negative eta l r a b pL pR test position frequency‖≤
      sourceSpatialDetectorPrice q branch negative eta a b pL pR*
        (sourceSpatialGaugePrice q eta l r*‖test frequency‖+
          sourceSpatialCurrentPrice q eta l r*(‖test frequency‖*
            ‖sourceNativeReaderFirst (fixedMomentum (sourceSpatialMomentum frequency) (sourcePoleSide (sourceSignedSpeed branch negative) eta))‖)) := by
  simp only [sourceSpatialIntegrand,norm_mul,spatial_phase_norm,one_mul]
  exact (mul_le_mul_of_nonneg_left (response_bound q branch negative eta positive l r a b pL pR nonrealL nonrealR _)
    (norm_nonneg _)).trans_eq (by ring)

/-- Actual pinned-resolvent and field-imaginary prices generate integrability over the whole physical frequency space. -/
theorem sourceSpatialRead_integrable (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (position : PhysicalMomentum) :
    Integrable (sourceSpatialIntegrand q branch negative eta l r a b pL pR test position) := by
  have response:=response_continuous q branch negative eta positive l r a b pL pR nonrealL nonrealR
  have momentum:=momentum_temperate.1.continuous
  have continuous : Continuous (sourceSpatialIntegrand q branch negative eta l r a b pL pR test position) := by
    unfold sourceSpatialIntegrand sourceSpatialPhase
    fun_prop
  exact (spatial_majorant_integrable q branch negative eta l r a b pL pR test).mono'
    continuous.aestronglyMeasurable (Eventually.of_forall (spatial_integrand_price q branch negative eta positive l r a b pL pR nonrealL nonrealR test position))

/-- The complete generated spatial amplitude has a source-only finite price, uniformly in position. -/
theorem sourceSpatialRead_bound (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (test : 𝓢(PhysicalMomentum,ℂ)) (position : PhysicalMomentum) :
    ‖sourceSpatialRead q branch negative eta l r a b pL pR test position‖≤
      sourceSpatialReadPrice q branch negative eta l r a b pL pR test := by
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_ae (sourceSpatialRead_integrable q branch negative eta positive l r a b pL pR nonrealL nonrealR test position).norm
    (spatial_majorant_integrable q branch negative eta l r a b pL pR test)
    (Eventually.of_forall (spatial_integrand_price q branch negative eta positive l r a b pL pR nonrealL nonrealR test position))).trans_eq
  rw [integral_const_mul,integral_add (test.integrable.norm.const_mul _)
    ((weighted_reader_integrable _ test).const_mul _),integral_const_mul,integral_const_mul]
  rfl

end LowEnergy.PreparationVacuumStaticSpatialSource
