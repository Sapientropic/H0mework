import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSpatialGreenRead
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualSpatialPacket
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticSpatialSource
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
open scoped Matrix BigOperators Topology SchwartzMap Matrix.Norms.Operator ContDiff
attribute [local irreducible] sourcePinnedVelocity sourceVelocityLinear sourceEqualProjection sourceRetainerReturn
  sourceFullInitialUpper sourceFullInitialBase sourcePoleRead sourceNativeReaderFirst
  fullKernelFrame activeProjection fullInverse originalReadback sourcePoleEulerInitial
  sourcePoleMaterialPairGap sourceJointFieldResidue sourceAmputatedFieldVertex sourcePinnedResolvent
  sourceOriginInverse sourceBaseResidue sourceUpperResidue sourceFullCurrentResidue sourceGaugeCurrentResidue

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

private theorem vector_reader_price {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype ι] (L : E→L[ℂ] ℂ) (X : ι→E) (B : ι→ℝ) (C : ℝ)
    (nonnegative : 0≤ C) (budget : ∀i,0≤ B i) (bound : ∀i,‖X i‖≤ C*B i) :
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


private theorem source_matrix_smooth (terms : List SourceTerm) : ContDiff ℂ ∞ (sourceMatrix terms) := by
  induction terms with
  | nil=>exact contDiff_const
  | cons a rest ih=>
    have powers : ContDiff ℂ ∞ (fun v : Fin 4→ℂ=>a.powers.value v) := by
      unfold Powers.value
      fun_prop
    have sameTerm : a.matrix=(fun v : Fin 4→ℂ=>a.powers.value v • Matrix.single a.row a.column (coefficientValue a.coefficient)) := by
      funext v
      ext i j
      simp only [SourceTerm.matrix,Matrix.smul_apply,Matrix.single_apply,smul_eq_mul]
      split_ifs <;> ring
    have term : ContDiff ℂ ∞ a.matrix := by
      rw [sameTerm]
      exact powers.smul contDiff_const
    have same : sourceMatrix (a::rest)=(fun v=>a.matrix v+sourceMatrix rest v) := by
      funext v
      exact sourceMatrix_cons _ _ _
    rw [same]
    exact term.add ih

private theorem source_reader_smooth : ContDiff ℂ ∞ sourceNativeReaderFirst := by
  unfold sourceNativeReaderFirst sourceLinearPart degreeTensor
  exact ((contDiff_const.mul contDiff_const).mul (source_matrix_smooth _)).sub
    (((((contDiff_const.mul (source_matrix_smooth _)).mul contDiff_const).mul contDiff_const).mul contDiff_const))

/-- The true source polynomial generates its continuous linear first-jet map. -/
def sourceReaderLinear : (Fin 4→ℂ)→L[ℂ] Matrix (Fin 289) (Fin 289) ℂ :=
  fderiv ℂ sourceNativeReaderFirst 0

theorem sourceReaderLinear_generated (v : Fin 4→ℂ) : sourceReaderLinear v=sourceNativeReaderFirst v := by
  have input : HasDerivAt (fun z : ℂ=>z • v) v 0 := by
    simpa only [one_smul,id_eq] using (hasDerivAt_id (0:ℂ)).smul_const v
  have differentiable : Differentiable ℂ sourceNativeReaderFirst := source_reader_smooth.differentiable (by norm_num)
  have derivative : HasFDerivAt sourceNativeReaderFirst sourceReaderLinear ((0:ℂ) • v) := by
    simpa only [sourceReaderLinear,zero_smul] using (differentiable 0).hasFDerivAt
  have composed:=derivative.comp_hasDerivAt 0 input
  have output : HasDerivAt (fun z : ℂ=>z • sourceNativeReaderFirst v) (sourceNativeReaderFirst v) 0 := by
    simpa only [one_smul,id_eq] using (hasDerivAt_id (0:ℂ)).smul_const (sourceNativeReaderFirst v)
  have same : (fun z : ℂ=>sourceNativeReaderFirst (z • v))=(fun z : ℂ=>z • sourceNativeReaderFirst v) :=
    funext (fun z=>sourceReaderFirst_radial v z)
  simp only [Function.comp_def] at composed
  rw [same] at composed
  exact composed.unique output

private theorem momentum_bound (n : PhysicalMomentum) (zeta : ℂ) :
    ‖fixedMomentum n zeta‖≤‖zeta‖+‖n‖ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact le_add_of_nonneg_right (norm_nonneg n)
  · change ‖Complex.I*(n j:ℂ)‖≤_
    rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]
    exact (norm_le_pi_norm n j).trans (le_add_of_nonneg_left (norm_nonneg zeta))

theorem sourceReaderLinear_bound (n : PhysicalMomentum) (zeta : ℂ) :
    ‖sourceNativeReaderFirst (fixedMomentum n zeta)‖≤‖sourceReaderLinear‖*(‖zeta‖+‖n‖) := by
  rw [←sourceReaderLinear_generated]
  exact (sourceReaderLinear.le_opNorm _).trans (mul_le_mul_of_nonneg_left (momentum_bound n zeta) (norm_nonneg _))

private theorem momentum_square_nonnegative (n : PhysicalMomentum) : 0≤ spatialSquare n := by
  unfold spatialSquare
  positivity

private theorem momentum_norm_square (n : PhysicalMomentum) : ‖n‖≤1+spatialSquare n := by
  apply (pi_norm_le_iff_of_nonneg (by have h:=momentum_square_nonnegative n;linarith)).mpr
  intro i
  have bound (x y z : ℝ) : |x|≤1+(x^2+y^2+z^2) := by
    nlinarith [sq_nonneg y,sq_nonneg z,sq_nonneg (|x|-1),sq_abs x]
  fin_cases i
  · change |n 0|≤1+(n 0^2+n 1^2+n 2^2)
    exact bound _ _ _
  · change |n 1|≤1+(n 0^2+n 1^2+n 2^2)
    nlinarith only [bound (n 1) (n 0) (n 2)]
  · change |n 2|≤1+(n 0^2+n 1^2+n 2^2)
    nlinarith only [bound (n 2) (n 0) (n 1)]

/-- Original spatial coefficient, without dropping either canonical denominator. -/
def sourceSpatialCoefficient (i : Fin 2) : ℝ :=
  Real.sqrt 2*Real.sqrt 15*(if i=0 then (25/54:ℝ) else 12/335)

theorem sourceSpatialCoefficient_positive (i : Fin 2) : 0<sourceSpatialCoefficient i := by
  unfold sourceSpatialCoefficient
  split_ifs <;> positivity

private theorem denominator_split (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 2) :
    sourceCanonicalDenominator n zeta i=(sourceSpatialCoefficient i:ℂ)*(spatialSquare n:ℂ)+
      sourceStaticDenominatorSlope i*zeta^2 := by
  unfold sourceCanonicalDenominator sourceSpatialCoefficient sourceStaticDenominatorSlope rootTwo rootFifteen
  split_ifs <;> push_cast <;> ring

private theorem detector_imaginary (n : PhysicalMomentum) (c eta : ℝ) (i : Fin 2) :
    (sourceCanonicalDenominator n (sourcePoleSide c eta) i).im=sourceDetectorImaginary c eta i := by
  fin_cases i <;> norm_num [sourceCanonicalDenominator,sourcePoleSide,sourceDetectorImaginary,
    rootTwo,rootFifteen,pow_two,Complex.mul_im,Complex.mul_re] <;> ring

private theorem detector_imaginary_ne (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (i : Fin 2) :
    sourceDetectorImaginary c eta i≠0 := by
  have coefficient : (if i=0 then -(25/9:ℝ) else 20/99)≠0 := by split_ifs <;> norm_num
  unfold sourceDetectorImaginary
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) coefficient) positive.ne') frequency

private theorem detector_price (n : PhysicalMomentum) (c eta : ℝ) (frequency : c≠0) (positive : 0<eta) (i : Fin 2) :
    ‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖≤ sourceDetectorPrice c eta i := by
  rw [norm_inv]
  apply inv_anti₀ (abs_pos.mpr (detector_imaginary_ne c eta frequency positive i))
  rw [←detector_imaginary n c eta i]
  exact Complex.abs_im_le_norm _

private theorem denominator_square_price (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 2)
    (nonzero : sourceCanonicalDenominator n zeta i≠0) :
    spatialSquare n*‖(sourceCanonicalDenominator n zeta i)⁻¹‖≤
      (sourceSpatialCoefficient i)⁻¹*(1+‖sourceStaticDenominatorSlope i*zeta^2‖*‖(sourceCanonicalDenominator n zeta i)⁻¹‖) := by
  have coefficient:=sourceSpatialCoefficient_positive i
  have numerator : sourceSpatialCoefficient i*spatialSquare n≤
      ‖sourceCanonicalDenominator n zeta i‖+‖sourceStaticDenominatorSlope i*zeta^2‖ := by
    have h:=norm_sub_le (sourceCanonicalDenominator n zeta i) (sourceStaticDenominatorSlope i*zeta^2)
    rw [denominator_split,add_sub_cancel_right,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg coefficient.le,Real.norm_of_nonneg (momentum_square_nonnegative n)] at h
    rw [denominator_split]
    exact h
  have scaled:=mul_le_mul_of_nonneg_right numerator (norm_nonneg ((sourceCanonicalDenominator n zeta i)⁻¹))
  rw [add_mul,norm_inv,mul_inv_cancel₀ (norm_ne_zero_iff.mpr nonzero)] at scaled
  have divided:=mul_le_mul_of_nonneg_left scaled (inv_nonneg.mpr coefficient.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ coefficient.ne',one_mul,norm_inv] using divided

def sourceWeightedDetectorPrice (c eta : ℝ) (i : Fin 2) : ℝ :=
  (‖sourcePoleSide c eta‖+1)*sourceDetectorPrice c eta i+
    (sourceSpatialCoefficient i)⁻¹*(1+‖sourceStaticDenominatorSlope i*(sourcePoleSide c eta)^2‖*sourceDetectorPrice c eta i)

/-- The original quadratic spatial denominator controls the actual first jet at every momentum. -/
theorem sourceWeightedDetector_bound (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (i : Fin 2) :
    (‖sourcePoleSide c eta‖+‖n‖)*‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖≤
      sourceWeightedDetectorPrice c eta i := by
  have nonzero : sourceCanonicalDenominator n (sourcePoleSide c eta) i≠0 := by
    intro h
    have im:=congrArg Complex.im h
    rw [detector_imaginary,Complex.zero_im] at im
    exact detector_imaginary_ne c eta frequency positive i im
  have square:=denominator_square_price n (sourcePoleSide c eta) i nonzero
  have price:=detector_price n c eta frequency positive i
  have coefficient:=sourceSpatialCoefficient_positive i
  calc
    _≤(‖sourcePoleSide c eta‖+(1+spatialSquare n))*‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖ := by gcongr;exact momentum_norm_square n
    _=(‖sourcePoleSide c eta‖+1)*‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖+
      spatialSquare n*‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖ := by ring
    _≤(‖sourcePoleSide c eta‖+1)*sourceDetectorPrice c eta i+
      (sourceSpatialCoefficient i)⁻¹*(1+‖sourceStaticDenominatorSlope i*(sourcePoleSide c eta)^2‖*‖(sourceCanonicalDenominator n (sourcePoleSide c eta) i)⁻¹‖) := by gcongr
    _≤ sourceWeightedDetectorPrice c eta i := by unfold sourceWeightedDetectorPrice;gcongr

private theorem slow_bound (v : Fin 289→ℂ) (i : Fin 5) :
    ‖sourceSlowRead v i‖≤‖slowFastFrame.transpose‖*‖v‖ := by
  unfold sourceSlowRead
  split_ifs
  · exact (norm_le_pi_norm _ _).trans (Matrix.linfty_opNorm_mulVec _ _)
  · rw [norm_zero]
    positivity

/-- Uniform multiplier price generated from the original two field denominators and complete current. -/
def sourceUniformResponsePrice (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℝ :=
  ‖-sourcePoleMaterialPairGap q pL pR a b*sourceOriginWeight (sourcePoleEulerInitial q pL pR a b)‖*
    ‖slowFastFrame.transpose‖*
    ((sourceDetectorPrice (sourceSignedSpeed branch negative) eta 0+sourceDetectorPrice (sourceSignedSpeed branch negative) eta 1)*
        sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*(sourceWeightedDetectorPrice (sourceSignedSpeed branch negative) eta 0+
        sourceWeightedDetectorPrice (sourceSignedSpeed branch negative) eta 1)*sourceSpatialCurrentPrice q eta l r)

theorem sourceUniformResponsePrice_nonnegative (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    0≤ sourceUniformResponsePrice q branch negative eta l r a b pL pR := by
  unfold sourceUniformResponsePrice sourceWeightedDetectorPrice sourceDetectorPrice
    sourceSpatialGaugePrice sourceSpatialCurrentPrice
  have zero:=sourceSpatialCoefficient_positive 0
  have one:=sourceSpatialCoefficient_positive 1
  positivity

/-- Every momentum of the actual full-Gamma spatial response is uniformly bounded; the source supplies the multiplier. -/
theorem sourceSpatialResponse_uniform (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (n : PhysicalMomentum) :
    ‖sourceSpatialResponse q branch negative eta l r a b pL pR n‖≤
      sourceUniformResponsePrice q branch negative eta l r a b pL pR := by
  let zeta:=sourceObservedSide n branch negative eta positive
  have realPart : zeta.val.re=eta := by simp [zeta,sourceObservedSide,sourcePoleSide]
  have gpos : 0≤ sourceSpatialGaugePrice q eta l r := by unfold sourceSpatialGaugePrice;positivity
  have cpos : 0≤ sourceSpatialCurrentPrice q eta l r := by unfold sourceSpatialCurrentPrice;positivity
  have native : ‖sourceActualNativeResidue q n zeta.val l r‖≤ sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*(‖zeta.val‖+‖n‖)*sourceSpatialCurrentPrice q eta l r := by
    unfold sourceActualNativeResidue
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [realPart] using origin_bound q n zeta.val zeta.property.1 l r
    · apply (Matrix.linfty_opNorm_mulVec _ _).trans
      exact mul_le_mul (sourceReaderLinear_bound n zeta.val)
        (by simpa only [realPart] using current_bound q n zeta.val zeta.property.1 l r)
        (norm_nonneg _) (by positivity)
  have channel (i : Fin 2) :
      ‖(sourceCanonicalDenominator n zeta.val i)⁻¹*sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) ⟨i.val,by omega⟩‖≤
        ‖slowFastFrame.transpose‖*(sourceDetectorPrice (sourceSignedSpeed branch negative) eta i*sourceSpatialGaugePrice q eta l r+
          ‖sourceReaderLinear‖*sourceWeightedDetectorPrice (sourceSignedSpeed branch negative) eta i*sourceSpatialCurrentPrice q eta l r) := by
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left (slow_bound _ _) (norm_nonneg _)).trans
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left native (norm_nonneg _)) (norm_nonneg _)).trans
    have ordinary:=detector_price n _ eta (sourceSignedSpeed_nonzero branch negative) positive i
    have weighted:=sourceWeightedDetector_bound n _ eta (sourceSignedSpeed_nonzero branch negative) positive i
    calc
      _=‖slowFastFrame.transpose‖*(‖(sourceCanonicalDenominator n zeta.val i)⁻¹‖*sourceSpatialGaugePrice q eta l r+
        ‖sourceReaderLinear‖*((‖zeta.val‖+‖n‖)*‖(sourceCanonicalDenominator n zeta.val i)⁻¹‖)*sourceSpatialCurrentPrice q eta l r) := by ring
      _≤_ := by dsimp only [zeta,sourceObservedSide];gcongr
  have tensor:=sourceObservedField_tensor q n zeta l r a b pL pR nonrealL nonrealR
  dsimp only [zeta,sourceObservedSide] at tensor channel
  rw [sourceSpatialResponse,tensor,norm_mul]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (channel 0) (channel 1)) (norm_nonneg _)).trans_eq
  unfold sourceUniformResponsePrice
  ring

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
theorem sourceSpatialResponse_continuous (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (sourceSpatialResponse q branch negative eta l r a b pL pR) := by
  let zeta:=sourcePoleSide (sourceSignedSpeed branch negative) eta
  have realPart : zeta.re=eta := by simp [zeta,sourcePoleSide]
  have causal : 0<zeta.re := by rwa [realPart]
  have current:=current_continuous q zeta causal l r
  have origin:=origin_continuous q zeta causal l r
  have point : Continuous (fun n : PhysicalMomentum=>fixedMomentum n zeta) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact continuous_const
    · change Continuous (fun n : PhysicalMomentum=>Complex.I*(n j:ℂ))
      fun_prop
  have reader : Continuous (fun n : PhysicalMomentum=>sourceNativeReaderFirst (fixedMomentum n zeta)) := by
    simp_rw [←sourceReaderLinear_generated]
    exact sourceReaderLinear.continuous.comp point
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


end LowEnergy.PreparationVacuumActualSpatialPacket
