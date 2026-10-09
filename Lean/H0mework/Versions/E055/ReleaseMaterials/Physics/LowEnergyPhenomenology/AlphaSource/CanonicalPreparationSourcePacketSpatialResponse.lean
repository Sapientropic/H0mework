import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualPacketApproximation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualSpatialPacket
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticSpatialSource PreparationVacuumObservedPoleTensor
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationVacuumFullSlowFieldResponse PreparationVacuumPhysicalPoleAmputation
open CanonicalGradedSpatialSource FullQuantum FullSpace
open PreparationVacuumIndependentMomentumReturn PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace SchwartzMap FourierTransform BigOperators
attribute [local irreducible] sourceSpatialResponse sourceFrequencyPacket sourceUniformResponsePrice

private theorem multiplied_memLp (M : FullSpace.Position→ℂ) (measurable : AEStronglyMeasurable M volume)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) (f : PacketL2) : MemLp (fun x=>M x*f x) 2 volume := by
  apply (Lp.memLp f).of_le_mul (measurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖M x*f x‖≤K*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (bound x) (norm_nonneg _)

private def multiplyPacket (M : FullSpace.Position→ℂ) (measurable : AEStronglyMeasurable M volume)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) (f : PacketL2) : PacketL2 :=
  (multiplied_memLp M measurable K bound f).toLp (fun x=>M x*f x)

private theorem multiplyPacket_ae (M : FullSpace.Position→ℂ) (measurable : AEStronglyMeasurable M volume)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) (f : PacketL2) :
    multiplyPacket M measurable K bound f=ᵐ[volume] fun x=>M x*f x :=
  (multiplied_memLp M measurable K bound f).coeFn_toLp

private def multiplierLinear (M : FullSpace.Position→ℂ) (measurable : AEStronglyMeasurable M volume)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) : PacketL2→ₗ[ℂ]PacketL2 where
  toFun:=multiplyPacket M measurable K bound
  map_add' f g:=by
    apply Lp.ext
    filter_upwards [multiplyPacket_ae M measurable K bound (f+g),multiplyPacket_ae M measurable K bound f,
      multiplyPacket_ae M measurable K bound g,Lp.coeFn_add f g,
      Lp.coeFn_add (multiplyPacket M measurable K bound f) (multiplyPacket M measurable K bound g)] with x fg left right add output
    rw [fg,add,output]
    simp only [Pi.add_apply]
    rw [left,right,mul_add]
  map_smul' c f:=by
    apply Lp.ext
    filter_upwards [multiplyPacket_ae M measurable K bound (c • f),multiplyPacket_ae M measurable K bound f,
      Lp.coeFn_smul c f,Lp.coeFn_smul c (multiplyPacket M measurable K bound f)] with x cf input scale output
    change multiplyPacket M measurable K bound (c • f) x=(c • multiplyPacket M measurable K bound f) x
    rw [cf,scale,output]
    simp only [Pi.smul_apply]
    rw [input]
    simp only [smul_eq_mul]
    ring

private theorem multiplierLinear_bound (M : FullSpace.Position→ℂ) (measurable : AEStronglyMeasurable M volume)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) (f : PacketL2) :
    ‖multiplierLinear M measurable K bound f‖≤K*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplyPacket_ae M measurable K bound f] with x h
  change ‖multiplyPacket M measurable K bound f x‖≤K*‖f x‖
  rw [h,norm_mul]
  exact mul_le_mul_of_nonneg_right (bound x) (norm_nonneg _)

private def boundedMultiplier (M : FullSpace.Position→ℂ) (measurable : AEStronglyMeasurable M volume)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) : PacketL2→L[ℂ]PacketL2 :=
  (multiplierLinear M measurable K bound).mkContinuous K (multiplierLinear_bound M measurable K bound)

/-- Original inverse spatial phase and the complete independently amputated field form one actual multiplier. -/
def sourcePacketMultiplierValue (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) (frequency : FullSpace.Position) : ℂ :=
  sourceSpatialPhase (fun j=>frequency j) position*
    sourceSpatialResponse q branch negative eta l r a b pL pR (FullSpace.physicalMomentum frequency)

private theorem sourcePacketMultiplier_continuous (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (sourcePacketMultiplierValue q branch negative eta l r a b pL pR position) := by
  have response:=(sourceSpatialResponse_continuous q branch negative eta positive l r a b pL pR nonrealL nonrealR).comp
    FullSpace.physicalMomentum_continuous
  have coords:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3=>ℝ)).continuous
  unfold sourcePacketMultiplierValue sourceSpatialPhase sourceSpatialMomentum
  fun_prop

private theorem sourcePacketMultiplier_bound (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (frequency : FullSpace.Position) :
    ‖sourcePacketMultiplierValue q branch negative eta l r a b pL pR position frequency‖≤
      sourceUniformResponsePrice q branch negative eta l r a b pL pR := by
  have phase : ‖sourceSpatialPhase (fun j=>frequency j) position‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
  rw [sourcePacketMultiplierValue,norm_mul,phase,one_mul]
  exact sourceSpatialResponse_uniform q branch negative eta positive l r a b pL pR nonrealL nonrealR _

/-- The source's uniform momentum bound constructs the actual bounded operator on the original spatial packet space. -/
def sourcePacketOperator (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) : PacketL2→L[ℂ]PacketL2 :=
  boundedMultiplier (sourcePacketMultiplierValue q branch negative eta l r a b pL pR position)
    (sourcePacketMultiplier_continuous q branch negative eta positive l r a b pL pR position nonrealL nonrealR).aestronglyMeasurable
    (sourceUniformResponsePrice q branch negative eta l r a b pL pR)
    (sourcePacketMultiplier_bound q branch negative eta positive l r a b pL pR position nonrealL nonrealR)

theorem sourcePacketOperator_ae (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (f : PacketL2) :
    sourcePacketOperator q branch negative eta positive l r a b pL pR position nonrealL nonrealR f=ᵐ[volume]
      fun frequency=>sourcePacketMultiplierValue q branch negative eta l r a b pL pR position frequency*f frequency :=
  multiplyPacket_ae _
    (sourcePacketMultiplier_continuous q branch negative eta positive l r a b pL pR position nonrealL nonrealR).aestronglyMeasurable
    (sourceUniformResponsePrice q branch negative eta l r a b pL pR)
    (sourcePacketMultiplier_bound q branch negative eta positive l r a b pL pR position nonrealL nonrealR) f

theorem sourcePacketOperator_bound (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (f : PacketL2) :
    ‖sourcePacketOperator q branch negative eta positive l r a b pL pR position nonrealL nonrealR f‖≤
      sourceUniformResponsePrice q branch negative eta l r a b pL pR*‖f‖ :=
  multiplierLinear_bound _ _ _ _ _

/-- The actual original unit-ball preparation is consumed; neither scalar leg is chosen by the caller. -/
def sourceActualPacketResponse (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) : ℂ :=
  inner ℂ sourceFrequencyPacket
    (sourcePacketOperator q branch negative eta positive l r a b pL pR position nonrealL nonrealR sourceFrequencyPacket)

/-- The complete original packet response inherits the same source-only price. -/
theorem sourceActualPacketResponse_bound (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖sourceActualPacketResponse q branch negative eta positive l r a b pL pR position nonrealL nonrealR‖≤
      sourceUniformResponsePrice q branch negative eta l r a b pL pR := by
  unfold sourceActualPacketResponse
  apply (norm_inner_le_norm _ _).trans
  rw [sourceFrequencyPacket_unit,one_mul]
  simpa only [sourceFrequencyPacket_unit,mul_one] using
    sourcePacketOperator_bound q branch negative eta positive l r a b pL pR position nonrealL nonrealR sourceFrequencyPacket

/-- The generated smooth two-leg profile enters the already-paid spatial response directly. -/
def sourceSmoothPacketResponse (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) : ℂ :=
  sourceSpatialRead q branch negative eta l r a b pL pR
    (sourcePacketTest left right leftPositive rightPositive) position

theorem sourceSmoothPacketResponse_operator (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0)
    (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) :
    sourceSmoothPacketResponse q branch negative eta l r a b pL pR position left right leftPositive rightPositive=
      inner ℂ ((sourcePacketApprox left leftPositive).toLp 2 volume)
        (sourcePacketOperator q branch negative eta positive l r a b pL pR position nonrealL nonrealR
          ((sourcePacketApprox right rightPositive).toLp 2 volume)) := by
  let f : FullSpace.Position→ℂ:=fun frequency=>
    star (sourcePacketApprox left leftPositive frequency)*
      (sourcePacketMultiplierValue q branch negative eta l r a b pL pR position frequency*
        sourcePacketApprox right rightPositive frequency)
  have pullback : sourceSpatialIntegrand q branch negative eta l r a b pL pR
      (sourcePacketTest left right leftPositive rightPositive) position=f ∘ WithLp.toLp 2 := by
    funext frequency
    simp only [sourceSpatialIntegrand,sourcePacketTest_apply,Function.comp_def,f,sourcePacketMultiplierValue]
    have momentum : FullSpace.physicalMomentum (WithLp.toLp 2 frequency)=sourceSpatialMomentum frequency := rfl
    rw [momentum]
    ring
  unfold sourceSmoothPacketResponse sourceSpatialRead
  rw [pullback]
  have transported:=(PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3=>ℝ)).symm.toHomeomorph.measurableEmbedding) f
  simp only [Function.comp_def]
  rw [transported,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(sourcePacketApprox left leftPositive).coeFn_toLp 2 volume,
    (sourcePacketApprox right rightPositive).coeFn_toLp 2 volume,
    sourcePacketOperator_ae q branch negative eta positive l r a b pL pR position nonrealL nonrealR
      ((sourcePacketApprox right rightPositive).toLp 2 volume)] with frequency leftLeg rightLeg operated
  rw [operated,leftLeg,rightLeg]
  simp only [f,RCLike.inner_apply,starRingEnd_apply]
  ring

private theorem two_leg_error (A : PacketL2→L[ℂ]PacketL2) (K : ℝ) (_nonnegative : 0≤K)
    (bound : ∀f,‖A f‖≤K*‖f‖) (f g u v : PacketL2) :
    ‖inner ℂ f (A g)-inner ℂ u (A v)‖≤K*(‖f-u‖*‖g‖+‖u‖*‖g-v‖) := by
  have difference : inner ℂ f (A g)-inner ℂ u (A v)=
      inner ℂ (f-u) (A g)+inner ℂ u (A (g-v)) := by
    rw [inner_sub_left,map_sub,inner_sub_right]
    ring
  rw [difference]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)).trans
  calc
    _≤‖f-u‖*(K*‖g‖)+‖u‖*(K*‖g-v‖) := by gcongr <;> apply bound
    _=_ := by ring

/-- Independent source-generated approximations converge with an explicit two-leg error to the actual original packet response. -/
theorem sourceSmoothPacketResponse_error (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0)
    (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) :
    ‖sourceSmoothPacketResponse q branch negative eta l r a b pL pR position left right leftPositive rightPositive-
      sourceActualPacketResponse q branch negative eta positive l r a b pL pR position nonrealL nonrealR‖≤
      sourceUniformResponsePrice q branch negative eta l r a b pL pR*(left*(1+right)+right) := by
  rw [sourceSmoothPacketResponse_operator q branch negative eta positive l r a b pL pR position nonrealL nonrealR,
    sourceActualPacketResponse]
  have h:=two_leg_error (sourcePacketOperator q branch negative eta positive l r a b pL pR position nonrealL nonrealR)
    (sourceUniformResponsePrice q branch negative eta l r a b pL pR)
    (sourceUniformResponsePrice_nonnegative q branch negative eta positive l r a b pL pR)
    (sourcePacketOperator_bound q branch negative eta positive l r a b pL pR position nonrealL nonrealR)
    ((sourcePacketApprox left leftPositive).toLp 2 volume) ((sourcePacketApprox right rightPositive).toLp 2 volume)
    sourceFrequencyPacket sourceFrequencyPacket
  apply h.trans
  rw [sourceFrequencyPacket_unit,one_mul]
  gcongr
  · exact sourceUniformResponsePrice_nonnegative q branch negative eta positive l r a b pL pR
  · exact (sourcePacketApprox_error left leftPositive).le
  · exact sourcePacketApprox_norm right rightPositive
  · exact (sourcePacketApprox_error right rightPositive).le

/-- The original scalar packet multiplies the actual independent dual and actual amputated primal separately. -/
def sourcePacketIndependentVertex (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a b : RestStateIndex) (frequency : FullSpace.Position) (field : Fin 289→ℂ) : ℂ :=
  ∑i,field i*((star (sourceFrequencyPacket frequency)) •
    sourcePoleAmputatedDual q.epsilon q.precision pL a q.F q.z)
      (sourceMovingIndependentReader (fieldUnit i) pR q.F 0
        (sourceFrequencyPacket frequency • sourcePoleAmputatedPrimal q.epsilon q.precision pR b q.F q.w))

theorem sourcePacketIndependentVertex_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a b : RestStateIndex) (frequency : FullSpace.Position) (field : Fin 289→ℂ) :
    sourcePacketIndependentVertex q pL pR a b frequency field=
      star (sourceFrequencyPacket frequency)*sourceFrequencyPacket frequency*
        sourceAmputatedFieldVertex q pL pR a b field := by
  simp only [sourcePacketIndependentVertex,sourceAmputatedFieldVertex,sourceAmputatedPoleVertex,
    map_smul,smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The completed spatial response is the original independently prepared two-leg field observer integrated on the original packet. -/
theorem sourceActualPacketResponse_independent (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    sourceActualPacketResponse q branch negative eta positive l r a b pL pR position nonrealL nonrealR=
      ∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
        sourcePacketIndependentVertex q pL pR a b frequency
          (sourceJointFieldResidue q (FullSpace.physicalMomentum frequency)
            (sourcePoleSide (sourceSignedSpeed branch negative) eta) l r) := by
  rw [sourceActualPacketResponse,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourcePacketOperator_ae q branch negative eta positive l r a b pL pR position nonrealL nonrealR sourceFrequencyPacket] with frequency applied
  rw [applied,sourcePacketIndependentVertex_generated]
  simp only [sourcePacketMultiplierValue,sourceSpatialResponse,RCLike.inner_apply,starRingEnd_apply]
  ring

def sourcePacketAccuracy (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem sourcePacketAccuracy_positive (n : ℕ) : 0<sourcePacketAccuracy n := by
  unfold sourcePacketAccuracy
  positivity

/-- Fixed-eta actual packet response is generated as the limit of its own controlled two-leg Schwartz approximations. -/
theorem sourceActualPacketResponse_generated (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool) (eta : ℝ)
    (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun n : ℕ=>sourceSmoothPacketResponse q branch negative eta l r a b pL pR position
      (sourcePacketAccuracy n) (sourcePacketAccuracy n) (sourcePacketAccuracy_positive n) (sourcePacketAccuracy_positive n))
      atTop (𝓝 (sourceActualPacketResponse q branch negative eta positive l r a b pL pR position nonrealL nonrealR)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n=>norm_nonneg _)
    (fun n=>sourceSmoothPacketResponse_error q branch negative eta positive l r a b pL pR position nonrealL nonrealR
      (sourcePacketAccuracy n) (sourcePacketAccuracy n) (sourcePacketAccuracy_positive n) (sourcePacketAccuracy_positive n))
  have accuracy : Tendsto sourcePacketAccuracy atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [zero_mul,mul_zero,add_zero] using
    (tendsto_const_nhds (x:=sourceUniformResponsePrice q branch negative eta l r a b pL pR)).mul
      ((accuracy.mul (tendsto_const_nhds.add accuracy)).add accuracy)

/-- Unit normalization is inherited from the actual original packet, so constant source action coefficients are unchanged. -/
theorem sourcePacket_constant_read (coefficient : ℂ) :
    inner ℂ sourceFrequencyPacket (coefficient • sourceFrequencyPacket)=coefficient := by
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K,sourceFrequencyPacket_unit]
  norm_num

end LowEnergy.PreparationVacuumActualSpatialPacket
