import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedCornerInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedSpatialResponse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticSpatialSource PreparationVacuumActualSpatialPacket
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedPacketGreen
open PreparationVacuumMixedControl PreparationVacuumWholeOrigin
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

private theorem terms_nonnegative (terms : List SourceTerm) : 0≤(termsPrice terms:ℝ) :=
  by exact_mod_cast termsPrice_nonneg terms

private theorem linear_bound (terms : List SourceTerm) (v : Fin 4→ℂ) (r : ℝ)
    (nonnegative : 0≤r) (bound : ∀i,‖v i‖≤r) :
    ‖sourceLinearPart terms v‖≤(termsPrice (degreeTerms (positiveTerms terms) 1):ℝ)*r := by
  have homogeneous : ∀a∈degreeTerms (positiveTerms terms) 1,a.powers.total=1 := by
    intro a member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  simpa only [sourceLinearPart,degreeTensor,pow_one] using
    sourceMatrix_homogeneous_price _ 1 homogeneous v r nonnegative bound

private theorem momentum_bound (n : PhysicalMomentum) (zeta : ℂ) (i : Fin 4) :
    ‖fixedMomentum n zeta i‖≤‖zeta‖+‖n‖ := by
  refine Fin.cases ?_ (fun j=>?_) i
  · change ‖zeta‖≤‖zeta‖+‖n‖
    exact le_add_of_nonneg_right (norm_nonneg _)
  · change ‖Complex.I*(n j:ℂ)‖≤‖zeta‖+‖n‖
    simpa only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real] using
      (norm_le_pi_norm n j).trans (le_add_of_nonneg_left (norm_nonneg zeta))

/-- Coefficients are read from the original degree-one source terms and complete inverse, with no fitted linear map. -/
def sourceChargedFrameJetPrice : ℝ :=
  ((termsPrice (degreeTerms (positiveTerms originalChangeTerms) 1):ℝ)*‖fullKernelFrame‖+
    ‖originalChange 0‖*‖fullInverse‖*(termsPrice (degreeTerms (positiveTerms activeTerms) 1):ℝ)*‖fullKernelFrame‖)*‖slowFastFrame‖

theorem sourceChargedFrameJetPrice_nonnegative : 0≤ sourceChargedFrameJetPrice := by
  have a:=terms_nonnegative (degreeTerms (positiveTerms originalChangeTerms) 1)
  have b:=terms_nonnegative (degreeTerms (positiveTerms activeTerms) 1)
  unfold sourceChargedFrameJetPrice
  positivity

theorem sourceChargedFrameJet_bound (n : PhysicalMomentum) (zeta : ℂ) :
    ‖sourceChargedNativeFrameJet (fixedMomentum n zeta)‖≤ sourceChargedFrameJetPrice*(‖zeta‖+‖n‖) := by
  have O:=linear_bound originalChangeTerms (fixedMomentum n zeta) (‖zeta‖+‖n‖) (by positivity) (momentum_bound n zeta)
  have K:=linear_bound activeTerms (fixedMomentum n zeta) (‖zeta‖+‖n‖) (by positivity) (momentum_bound n zeta)
  have product : ‖originalChange 0*fullInverse*sourceLinearPart activeTerms (fixedMomentum n zeta)*fullKernelFrame‖≤
      ‖originalChange 0‖*‖fullInverse‖*‖sourceLinearPart activeTerms (fixedMomentum n zeta)‖*‖fullKernelFrame‖ := by
    apply (norm_mul_le _ _).trans
    gcongr
    apply (norm_mul_le _ _).trans
    gcongr
    exact norm_mul_le _ _
  unfold sourceChargedNativeFrameJet
  calc
    _≤(‖sourceLinearPart originalChangeTerms (fixedMomentum n zeta)*fullKernelFrame‖+
      ‖originalChange 0*fullInverse*sourceLinearPart activeTerms (fixedMomentum n zeta)*fullKernelFrame‖)*‖slowFastFrame‖ := by
      apply (norm_mul_le _ _).trans
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _≤(‖sourceLinearPart originalChangeTerms (fixedMomentum n zeta)‖*‖fullKernelFrame‖+
      ‖originalChange 0‖*‖fullInverse‖*‖sourceLinearPart activeTerms (fixedMomentum n zeta)‖*‖fullKernelFrame‖)*‖slowFastFrame‖ := by
      gcongr
      exact norm_mul_le _ _
    _≤((termsPrice (degreeTerms (positiveTerms originalChangeTerms) 1):ℝ)*(‖zeta‖+‖n‖)*‖fullKernelFrame‖+
      ‖originalChange 0‖*‖fullInverse‖*((termsPrice (degreeTerms (positiveTerms activeTerms) 1):ℝ)*(‖zeta‖+‖n‖))*‖fullKernelFrame‖)*‖slowFastFrame‖ := by
      gcongr
    _=sourceChargedFrameJetPrice*(‖zeta‖+‖n‖) := by unfold sourceChargedFrameJetPrice;ring

private theorem five_norm (v : Fin 5→ℂ) : ‖fiveVector v‖≤‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  unfold fiveVector
  split_ifs
  · exact norm_le_pi_norm v _
  · simp

private theorem three_norm (n : PhysicalMomentum) (zeta : ℂ) (f : Fin 289→ℂ) :
    ‖sourceChargedThreeSolution n zeta f‖≤
      ∑i : Fin 3,‖(sourceChargedDenominator n zeta i)⁻¹*sourceSlowRead f ⟨i.val,by omega⟩‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
  intro i
  fin_cases i
  · simp only [sourceChargedThreeSolution]
    exact Finset.single_le_sum (f:=fun j : Fin 3=>‖(sourceChargedDenominator n zeta j)⁻¹*sourceSlowRead f ⟨j.val,by omega⟩‖) (fun j _=>norm_nonneg _) (Finset.mem_univ (0:Fin 3))
  · simp only [sourceChargedThreeSolution]
    exact Finset.single_le_sum (f:=fun j : Fin 3=>‖(sourceChargedDenominator n zeta j)⁻¹*sourceSlowRead f ⟨j.val,by omega⟩‖) (fun j _=>norm_nonneg _) (Finset.mem_univ (1:Fin 3))
  · simp only [sourceChargedThreeSolution]
    exact Finset.single_le_sum (f:=fun j : Fin 3=>‖(sourceChargedDenominator n zeta j)⁻¹*sourceSlowRead f ⟨j.val,by omega⟩‖) (fun j _=>norm_nonneg _) (Finset.mem_univ (2:Fin 3))
  · norm_num [sourceChargedThreeSolution,Fin.ext_iff]
    exact Finset.sum_nonneg (fun _ _=>mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · norm_num [sourceChargedThreeSolution,Fin.ext_iff]
    exact Finset.sum_nonneg (fun _ _=>mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))

private theorem slow_bound (v : Fin 289→ℂ) (i : Fin 5) :
    ‖sourceSlowRead v i‖≤‖slowFastFrame.transpose‖*‖v‖ := by
  unfold sourceSlowRead
  split_ifs
  · exact (norm_le_pi_norm _ _).trans (Matrix.linfty_opNorm_mulVec _ _)
  · rw [norm_zero]
    positivity

private theorem linear_denominator_bound (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (i : Fin 3) :
    (‖sourcePoleSide c eta‖+‖n‖)*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖≤
      sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i := by
  have quadratic:=sourceChargedQuadratic_bound n c eta frequency positive i
  have ordinary:=sourceChargedDenominator_bound n c eta frequency positive i
  have linear : ‖sourcePoleSide c eta‖+‖n‖≤1+(‖sourcePoleSide c eta‖+‖n‖)^2 := by nlinarith [sq_nonneg (‖sourcePoleSide c eta‖+‖n‖-1)]
  calc
    _≤(1+(‖sourcePoleSide c eta‖+‖n‖)^2)*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖ :=
      mul_le_mul_of_nonneg_right linear (norm_nonneg _)
    _=‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖+
      (‖sourcePoleSide c eta‖+‖n‖)^2*‖(sourceChargedDenominator n (sourcePoleSide c eta) i)⁻¹‖ := by ring
    _≤_ := add_le_add ordinary quadratic

/-- Every original slow denominator, the native first jet, and the complete regular/contact return contribute to this source price. -/
def sourceChargedSecondPrice (q : PhysicalResponsePoint) (c eta : ℝ) (l r : RestStateIndex) : ℝ :=
  sourceChargedFrameJetPrice*∑i : Fin 3,‖slowFastFrame.transpose‖*
    ((sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i)*sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*sourceChargedQuadraticPrice c eta i*sourceSpatialCurrentPrice q eta l r)+
    ‖sourceRegularMatrix 0‖*sourceSpatialCurrentPrice q eta l r

theorem sourceChargedSecondPrice_nonnegative (q : PhysicalResponsePoint) (c eta : ℝ) (positive : 0<eta) (l r : RestStateIndex) :
    0≤ sourceChargedSecondPrice q c eta l r := by
  have frame:=sourceChargedFrameJetPrice_nonnegative
  have current : 0≤ sourceSpatialCurrentPrice q eta l r := by unfold sourceSpatialCurrentPrice;positivity
  have gauge : 0≤ sourceSpatialGaugePrice q eta l r := by unfold sourceSpatialGaugePrice;positivity
  unfold sourceChargedSecondPrice
  apply add_nonneg
  · apply mul_nonneg frame
    apply Finset.sum_nonneg
    intro i _
    have spatial := (sourceChargedSpatialCoefficient_positive i).le
    have denominator : 0≤ sourceChargedDenominatorPrice c eta i := by unfold sourceChargedDenominatorPrice;positivity
    have quadratic : 0≤ sourceChargedQuadraticPrice c eta i := by unfold sourceChargedQuadraticPrice;positivity
    positivity
  · positivity

/-- The full generated charged-order field, including its regular/contact part, is uniformly bounded on all spatial momenta. -/
theorem sourceChargedSecondField_uniform (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) :
    ‖sourceChargedSecondField q n (sourcePoleSide c eta) l r‖≤ sourceChargedSecondPrice q c eta l r := by
  let zeta : sourceCausalDomain n:=⟨sourcePoleSide c eta,sourcePoleSide_field_domain n c eta frequency positive⟩
  let R:=‖zeta.val‖+‖n‖
  have Rnonnegative : 0≤R:=by dsimp [R];positivity
  have realPart : zeta.val.re=eta:=by simp [zeta,sourcePoleSide]
  have gpos : 0≤ sourceSpatialGaugePrice q eta l r:=by unfold sourceSpatialGaugePrice;positivity
  have cpos : 0≤ sourceSpatialCurrentPrice q eta l r:=by unfold sourceSpatialCurrentPrice;positivity
  have framepos:=sourceChargedFrameJetPrice_nonnegative
  have native : ‖sourceActualNativeResidue q n zeta.val l r‖≤ sourceSpatialGaugePrice q eta l r+
      ‖sourceReaderLinear‖*R*sourceSpatialCurrentPrice q eta l r := by
    unfold sourceActualNativeResidue
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [realPart] using origin_bound q n zeta.val zeta.property.1 l r
    · apply (Matrix.linfty_opNorm_mulVec _ _).trans
      exact mul_le_mul (sourceReaderLinear_bound n zeta.val)
        (by simpa only [realPart] using current_bound q n zeta.val zeta.property.1 l r)
        (norm_nonneg _) (by positivity)
  have channel (i : Fin 3) :
      R*‖(sourceChargedDenominator n zeta.val i)⁻¹*sourceSlowRead (sourceActualNativeResidue q n zeta.val l r) ⟨i.val,by omega⟩‖≤
        ‖slowFastFrame.transpose‖*((sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i)*sourceSpatialGaugePrice q eta l r+
          ‖sourceReaderLinear‖*sourceChargedQuadraticPrice c eta i*sourceSpatialCurrentPrice q eta l r) := by
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (slow_bound _ _) (norm_nonneg _)) Rnonnegative).trans
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left native (norm_nonneg _)) (norm_nonneg _)) Rnonnegative).trans
    have linear:=linear_denominator_bound n c eta frequency positive i
    have quadratic:=sourceChargedQuadratic_bound n c eta frequency positive i
    calc
      _=‖slowFastFrame.transpose‖*((R*‖(sourceChargedDenominator n zeta.val i)⁻¹‖)*sourceSpatialGaugePrice q eta l r+
        ‖sourceReaderLinear‖*(R^2*‖(sourceChargedDenominator n zeta.val i)⁻¹‖)*sourceSpatialCurrentPrice q eta l r) := by ring
      _≤_ := by dsimp only [R,zeta];gcongr
  have total : R*‖sourceChargedFrameInput q n zeta.val l r‖≤
      ∑i : Fin 3,‖slowFastFrame.transpose‖*((sourceChargedDenominatorPrice c eta i+sourceChargedQuadraticPrice c eta i)*sourceSpatialGaugePrice q eta l r+
        ‖sourceReaderLinear‖*sourceChargedQuadraticPrice c eta i*sourceSpatialCurrentPrice q eta l r) := by
    rw [sourceChargedFrameInput_generated q n zeta]
    apply (mul_le_mul_of_nonneg_left ((five_norm _).trans (three_norm _ _ _)) Rnonnegative).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>channel i)
  unfold sourceChargedSecondField
  apply (norm_add_le _ _).trans
  unfold sourceChargedSecondPrice
  apply add_le_add
  · unfold sourceChargedActualFieldJet
    apply (Matrix.linfty_opNorm_mulVec _ _).trans
    apply (mul_le_mul_of_nonneg_right (sourceChargedFrameJet_bound n zeta.val) (norm_nonneg _)).trans
    simpa only [R,mul_assoc] using mul_le_mul_of_nonneg_left total framepos
  · apply (Matrix.linfty_opNorm_mulVec _ _).trans
    exact mul_le_mul_of_nonneg_left (by simpa only [realPart] using current_bound q n zeta.val zeta.property.1 l r) (norm_nonneg _)

private theorem physical_point_continuous (zeta : ℂ) : Continuous (fun n : PhysicalMomentum=>fixedMomentum n zeta) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_const
  · change Continuous (fun n : PhysicalMomentum=>Complex.I*(n j:ℂ))
    fun_prop

private theorem frame_jet_continuous : Continuous sourceChargedNativeFrameJet := by
  unfold sourceChargedNativeFrameJet sourceLinearPart degreeTensor
  exact (((source_matrix_smooth _).continuous.mul continuous_const).sub
    ((((continuous_const.mul continuous_const).mul (source_matrix_smooth _).continuous).mul continuous_const))).mul continuous_const

theorem sourceChargedSecondField_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) :
    Continuous (fun n : PhysicalMomentum=>sourceChargedSecondField q n (sourcePoleSide c eta) l r) := by
  let zeta:=sourcePoleSide c eta
  have realPart : zeta.re=eta:=by simp [zeta,sourcePoleSide]
  have causal : 0<zeta.re:=by rwa [realPart]
  have current:=current_continuous q zeta causal l r
  have origin:=origin_continuous q zeta causal l r
  have point:=physical_point_continuous zeta
  have reader : Continuous (fun n : PhysicalMomentum=>sourceNativeReaderFirst (fixedMomentum n zeta)) := by
    simp_rw [←sourceReaderLinear_generated]
    exact sourceReaderLinear.continuous.comp point
  have native : Continuous (fun n : PhysicalMomentum=>sourceActualNativeResidue q n zeta l r) :=
    origin.add (reader.matrix_mulVec current)
  have slow (i : Fin 5) : Continuous (fun n : PhysicalMomentum=>sourceSlowRead (sourceActualNativeResidue q n zeta l r) i) := by
    unfold sourceSlowRead
    split_ifs <;> fun_prop
  have denominator (i : Fin 3) : Continuous (fun n : PhysicalMomentum=>(sourceChargedDenominator n zeta i)⁻¹) := by
    have base : Continuous (fun n : PhysicalMomentum=>sourceChargedDenominator n zeta i) := by
      unfold sourceChargedDenominator spatialSquare
      fun_prop
    exact base.inv₀ (fun n=>sourceChargedDenominator_nonzero n c eta frequency positive i)
  have frameInput : Continuous (fun n : PhysicalMomentum=>sourceChargedFrameInput q n zeta l r) := by
    have same : (fun n : PhysicalMomentum=>sourceChargedFrameInput q n zeta l r)=
        fun n=>fiveVector (sourceChargedThreeSolution n zeta (sourceActualNativeResidue q n zeta l r)) := by
      funext n
      exact sourceChargedFrameInput_generated q n ⟨zeta,sourcePoleSide_field_domain n c eta frequency positive⟩ l r
    rw [same]
    apply continuous_pi
    intro j
    unfold fiveVector
    split_ifs
    · unfold sourceChargedThreeSolution
      split_ifs <;> fun_prop
    · exact continuous_const
  unfold sourceChargedSecondField sourceChargedActualFieldJet
  exact ((frame_jet_continuous.comp point).matrix_mulVec frameInput).add (continuous_const.matrix_mulVec current)

/-- The regular/contact summand keeps its own source price before packet integration. -/
def sourceChargedRegularPrice (q : PhysicalResponsePoint) (eta : ℝ) (l r : RestStateIndex) : ℝ :=
  ‖sourceRegularMatrix 0‖*sourceSpatialCurrentPrice q eta l r

theorem sourceChargedRegular_uniform (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (positive : 0<eta) (l r : RestStateIndex) :
    ‖sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n (sourcePoleSide c eta) l r‖≤
      sourceChargedRegularPrice q eta l r := by
  apply (Matrix.linfty_opNorm_mulVec _ _).trans
  exact mul_le_mul_of_nonneg_left (by simpa [sourcePoleSide] using (current_bound q n (sourcePoleSide c eta)
      (by simpa [sourcePoleSide] using positive) l r)) (norm_nonneg _)

theorem sourceChargedNative_uniform (q : PhysicalResponsePoint) (n : PhysicalMomentum) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) :
    ‖sourceChargedActualFieldJet q n (sourcePoleSide c eta) l r‖≤
      sourceChargedSecondPrice q c eta l r+sourceChargedRegularPrice q eta l r := by
  have same : sourceChargedActualFieldJet q n (sourcePoleSide c eta) l r=
      sourceChargedSecondField q n (sourcePoleSide c eta) l r-
        sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n (sourcePoleSide c eta) l r := by
    simp only [sourceChargedSecondField,add_sub_cancel_right]
  rw [same]
  exact (norm_sub_le _ _).trans (add_le_add (sourceChargedSecondField_uniform q n c eta frequency positive l r)
    (sourceChargedRegular_uniform q n c eta positive l r))

theorem sourceChargedRegular_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (positive : 0<eta) (l r : RestStateIndex) :
    Continuous (fun n : PhysicalMomentum=>sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n (sourcePoleSide c eta) l r) :=
  continuous_const.matrix_mulVec (current_continuous q (sourcePoleSide c eta) (by simpa [sourcePoleSide] using positive) l r)

theorem sourceChargedNative_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r : RestStateIndex) :
    Continuous (fun n : PhysicalMomentum=>sourceChargedActualFieldJet q n (sourcePoleSide c eta) l r) := by
  have same : (fun n : PhysicalMomentum=>sourceChargedActualFieldJet q n (sourcePoleSide c eta) l r)=
      fun n=>sourceChargedSecondField q n (sourcePoleSide c eta) l r-
        sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q n (sourcePoleSide c eta) l r := by
    funext n
    simp only [sourceChargedSecondField,add_sub_cancel_right]
  rw [same]
  exact (sourceChargedSecondField_continuous q c eta frequency positive l r).sub
    (sourceChargedRegular_continuous q c eta positive l r)

end LowEnergy.PreparationVacuumChargedSpatialResponse
