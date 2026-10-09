import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedSecondUniform

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumChargedSpatialResponse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticSpatialSource PreparationVacuumActualSpatialPacket
open PreparationVacuumChargedPacketGreen PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumObservedPoleTensor PreparationVacuumPhysicalFeedback
open PreparationVacuumElectromagneticIdentity PreparationVacuumFullSlowFieldResponse
open PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumOriginalGreenFeedback
open PreparationVacuumIndependentMomentumReturn PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open CanonicalGradedSpatialSource FullQuantum FullSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology InnerProductSpace SchwartzMap FourierTransform BigOperators
attribute [local irreducible] sourceChargedSecondField sourceFrequencyPacket sourceChargedSecondPrice
  sourceFullCurrentResidue sourceChargedActualFieldJet sourceAmputatedFieldVertex

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

def sourceChargedObserverPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (a b : RestStateIndex) : ℝ :=
  ∑mu : Fin 4,‖sourceAmputatedFieldVertex q pL pR a b (sourceChargedLockedField mu)‖

private theorem charged_observed (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a b : RestStateIndex) (F : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart F)=
      ∑mu : Fin 4,sourceChargedCoefficient F mu*sourceAmputatedFieldVertex q pL pR a b (sourceChargedLockedField mu) := by
  simp only [sourceAmputatedFieldVertex,sourceChargedFieldPart,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

private theorem observer_bound (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (a b : RestStateIndex) (F : Fin 289→ℂ) :
    ‖sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart F)‖≤
      sourceChargedObserverPrice q pL pR a b*‖F‖ := by
  rw [charged_observed]
  apply (norm_sum_le _ _).trans
  unfold sourceChargedObserverPrice
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro mu _
  rw [norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm F _) (norm_nonneg _)

private theorem observer_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (a b : RestStateIndex) :
    Continuous (fun F : Fin 289→ℂ=>sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart F)) := by
  simp_rw [charged_observed]
  unfold sourceChargedCoefficient
  fun_prop

private theorem observer_add (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (a b : RestStateIndex)
    (F G : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart (F+G))=
      sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart F)+
        sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart G) := by
  simp only [charged_observed,sourceChargedCoefficient,Pi.add_apply,add_mul,Finset.sum_add_distrib]

def sourceChargedResponsePrice (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) : ℝ :=
  sourceChargedObserverPrice q pL pR a b*sourceChargedSecondPrice q c eta l r

theorem sourceChargedResponsePrice_nonnegative (q : PhysicalResponsePoint) (c eta : ℝ) (positive : 0<eta)
    (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    0≤ sourceChargedResponsePrice q c eta l r a b pL pR :=
  mul_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (sourceChargedSecondPrice_nonnegative q c eta positive l r)

/-- The independent material dual and primal consume the full generated charged second-order field. -/
def sourceChargedSecondResponse (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r a b : RestStateIndex) (pL pR n : PhysicalMomentum) : ℂ :=
  sourceAmputatedFieldVertex q pL pR a b
    (sourceChargedFieldPart (sourceChargedSecondField q n (sourcePoleSide c eta) l r))

theorem sourceChargedSecondResponse_uniform (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR n : PhysicalMomentum) :
    ‖sourceChargedSecondResponse q c eta l r a b pL pR n‖≤ sourceChargedResponsePrice q c eta l r a b pL pR :=
  (observer_bound q pL pR a b _).trans (mul_le_mul_of_nonneg_left
    (sourceChargedSecondField_uniform q n c eta frequency positive l r) (Finset.sum_nonneg (fun _ _=>norm_nonneg _)))

theorem sourceChargedSecondResponse_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequency : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR : PhysicalMomentum) :
    Continuous (sourceChargedSecondResponse q c eta l r a b pL pR) :=
  (observer_continuous q pL pR a b).comp (sourceChargedSecondField_continuous q c eta frequency positive l r)

/-- Original inverse spatial phase and the complete independently amputated field form one actual multiplier. -/
def sourceChargedPacketMultiplierValue (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) (frequency : FullSpace.Position) : ℂ :=
  sourceSpatialPhase (fun j=>frequency j) position*
    sourceChargedSecondResponse q c eta l r a b pL pR (FullSpace.physicalMomentum frequency)

/-- On either original signed branch, the actual delta-squared field produces the packet multiplier pointwise before any spatial integral. -/
theorem sourceChargedPacketMultiplier_generated (q : PhysicalResponsePoint) (branch : Fin 2) (negative : Bool)
    (eta : ℝ) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) (frequency : FullSpace.Position) :
    Tendsto (fun d : ℝ=>(d:ℂ)^2*(sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
        (sourceJointCausalField q (FullSpace.physicalMomentum frequency)
          (sourcePoleSide (sourceSignedSpeed branch negative) eta) l r d))))
      (𝓝[>] 0) (𝓝 (star (sourceFrequencyPacket frequency)*sourceFrequencyPacket frequency*
        sourceChargedPacketMultiplierValue q (sourceSignedSpeed branch negative) eta l r a b pL pR position frequency)) := by
  have result:=sourceChargedSecondField_original_packet q frequency
    ⟨sourcePoleSide (sourceSignedSpeed branch negative) eta,
      sourcePoleSide_field_domain _ _ eta (sourceSignedSpeed_nonzero branch negative) positive⟩
    l r a b pL pR position nonrealL nonrealR
  convert result using 1
  congr 1
  simp only [sourceChargedPacketMultiplierValue,sourceChargedSecondResponse,sourcePacketIndependentVertex_generated]
  ring

private theorem sourceChargedPacketMultiplier_continuous (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    Continuous (sourceChargedPacketMultiplierValue q c eta l r a b pL pR position) := by
  have response:=(sourceChargedSecondResponse_continuous q c eta frequencyNonzero positive l r a b pL pR).comp
    FullSpace.physicalMomentum_continuous
  have coords:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3=>ℝ)).continuous
  unfold sourceChargedPacketMultiplierValue sourceSpatialPhase sourceSpatialMomentum
  fun_prop

private theorem sourceChargedPacketMultiplier_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) (frequency : FullSpace.Position) :
    ‖sourceChargedPacketMultiplierValue q c eta l r a b pL pR position frequency‖≤
      sourceChargedResponsePrice q c eta l r a b pL pR := by
  have phase : ‖sourceSpatialPhase (fun j=>frequency j) position‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
  rw [sourceChargedPacketMultiplierValue,norm_mul,phase,one_mul]
  exact sourceChargedSecondResponse_uniform q c eta frequencyNonzero positive l r a b pL pR _

/-- The source's uniform momentum bound constructs the actual bounded operator on the original spatial packet space. -/
def sourceChargedPacketOperator (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) : PacketL2→L[ℂ]PacketL2 :=
  boundedMultiplier (sourceChargedPacketMultiplierValue q c eta l r a b pL pR position)
    (sourceChargedPacketMultiplier_continuous q c eta frequencyNonzero positive l r a b pL pR position).aestronglyMeasurable
    (sourceChargedResponsePrice q c eta l r a b pL pR)
    (sourceChargedPacketMultiplier_bound q c eta frequencyNonzero positive l r a b pL pR position)

theorem sourceChargedPacketOperator_ae (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) (f : PacketL2) :
    sourceChargedPacketOperator q c eta frequencyNonzero positive l r a b pL pR position f=ᵐ[volume]
      fun frequency=>sourceChargedPacketMultiplierValue q c eta l r a b pL pR position frequency*f frequency :=
  multiplyPacket_ae _
    (sourceChargedPacketMultiplier_continuous q c eta frequencyNonzero positive l r a b pL pR position).aestronglyMeasurable
    (sourceChargedResponsePrice q c eta l r a b pL pR)
    (sourceChargedPacketMultiplier_bound q c eta frequencyNonzero positive l r a b pL pR position) f

theorem sourceChargedPacketOperator_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) (f : PacketL2) :
    ‖sourceChargedPacketOperator q c eta frequencyNonzero positive l r a b pL pR position f‖≤
      sourceChargedResponsePrice q c eta l r a b pL pR*‖f‖ :=
  multiplierLinear_bound _ _ _ _ _

/-- The actual original unit-ball preparation is consumed; neither scalar leg is chosen by the caller. -/
def sourceActualChargedPacketResponse (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) : ℂ :=
  inner ℂ sourceFrequencyPacket
    (sourceChargedPacketOperator q c eta frequencyNonzero positive l r a b pL pR position sourceFrequencyPacket)

/-- The complete original packet response inherits the same source-only price. -/
theorem sourceActualChargedPacketResponse_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    ‖sourceActualChargedPacketResponse q c eta frequencyNonzero positive l r a b pL pR position‖≤
      sourceChargedResponsePrice q c eta l r a b pL pR := by
  unfold sourceActualChargedPacketResponse
  apply (norm_inner_le_norm _ _).trans
  rw [sourceFrequencyPacket_unit,one_mul]
  simpa only [sourceFrequencyPacket_unit,mul_one] using
    sourceChargedPacketOperator_bound q c eta frequencyNonzero positive l r a b pL pR position sourceFrequencyPacket

/-- Spatial integration is performed only after the charged residue has been generated. -/
def sourceSmoothChargedPacketResponse (q : PhysicalResponsePoint) (c eta : ℝ)
    (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) : ℂ :=
  ∫frequency : FullSpace.Position,star (sourcePacketApprox left leftPositive frequency)*
    (sourceChargedPacketMultiplierValue q c eta l r a b pL pR position frequency*
      sourcePacketApprox right rightPositive frequency)

theorem sourceSmoothChargedPacketResponse_operator (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) :
    sourceSmoothChargedPacketResponse q c eta l r a b pL pR position left right leftPositive rightPositive=
      inner ℂ ((sourcePacketApprox left leftPositive).toLp 2 volume)
        (sourceChargedPacketOperator q c eta frequencyNonzero positive l r a b pL pR position
          ((sourcePacketApprox right rightPositive).toLp 2 volume)) := by
  rw [sourceSmoothChargedPacketResponse,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(sourcePacketApprox left leftPositive).coeFn_toLp 2 volume,
    (sourcePacketApprox right rightPositive).coeFn_toLp 2 volume,
    sourceChargedPacketOperator_ae q c eta frequencyNonzero positive l r a b pL pR position
      ((sourcePacketApprox right rightPositive).toLp 2 volume)] with frequency leftLeg rightLeg operated
  rw [operated,leftLeg,rightLeg]
  simp only [RCLike.inner_apply,starRingEnd_apply]
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
theorem sourceSmoothChargedPacketResponse_error (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum)
    (left right : ℝ) (leftPositive : 0<left) (rightPositive : 0<right) :
    ‖sourceSmoothChargedPacketResponse q c eta l r a b pL pR position left right leftPositive rightPositive-
      sourceActualChargedPacketResponse q c eta frequencyNonzero positive l r a b pL pR position‖≤
      sourceChargedResponsePrice q c eta l r a b pL pR*(left*(1+right)+right) := by
  rw [sourceSmoothChargedPacketResponse_operator q c eta frequencyNonzero positive l r a b pL pR position,
    sourceActualChargedPacketResponse]
  have h:=two_leg_error (sourceChargedPacketOperator q c eta frequencyNonzero positive l r a b pL pR position)
    (sourceChargedResponsePrice q c eta l r a b pL pR)
    (sourceChargedResponsePrice_nonnegative q c eta positive l r a b pL pR)
    (sourceChargedPacketOperator_bound q c eta frequencyNonzero positive l r a b pL pR position)
    ((sourcePacketApprox left leftPositive).toLp 2 volume) ((sourcePacketApprox right rightPositive).toLp 2 volume)
    sourceFrequencyPacket sourceFrequencyPacket
  apply h.trans
  rw [sourceFrequencyPacket_unit,one_mul]
  gcongr
  · exact sourceChargedResponsePrice_nonnegative q c eta positive l r a b pL pR
  · exact (sourcePacketApprox_error left leftPositive).le
  · exact sourcePacketApprox_norm right rightPositive
  · exact (sourcePacketApprox_error right rightPositive).le

private theorem packet_integrable (M : FullSpace.Position→ℂ) (continuous : Continuous M)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) :
    Integrable (fun x=>star (sourceFrequencyPacket x)*(M x*sourceFrequencyPacket x)) := by
  have h:=L2.integrable_inner (𝕜:=ℂ) sourceFrequencyPacket
    (multiplyPacket M continuous.aestronglyMeasurable K bound sourceFrequencyPacket)
  apply h.congr
  filter_upwards [multiplyPacket_ae M continuous.aestronglyMeasurable K bound sourceFrequencyPacket] with x hx
  simp only [RCLike.inner_apply,starRingEnd_apply,hx]
  ring

private theorem packet_integral_bound (M : FullSpace.Position→ℂ) (continuous : Continuous M)
    (K : ℝ) (bound : ∀x,‖M x‖≤K) :
    ‖∫x,star (sourceFrequencyPacket x)*(M x*sourceFrequencyPacket x)‖≤K := by
  have same : (∫x,star (sourceFrequencyPacket x)*(M x*sourceFrequencyPacket x))=
      inner ℂ sourceFrequencyPacket (multiplyPacket M continuous.aestronglyMeasurable K bound sourceFrequencyPacket) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [multiplyPacket_ae M continuous.aestronglyMeasurable K bound sourceFrequencyPacket] with x hx
    simp only [RCLike.inner_apply,starRingEnd_apply,hx]
    ring
  rw [same]
  apply (norm_inner_le_norm _ _).trans
  rw [sourceFrequencyPacket_unit,one_mul]
  simpa only [multiplierLinear,LinearMap.coe_mk,AddHom.coe_mk,sourceFrequencyPacket_unit,mul_one] using
    multiplierLinear_bound M continuous.aestronglyMeasurable K bound sourceFrequencyPacket

private theorem field_packet_budget (q : PhysicalResponsePoint) (pL pR position : PhysicalMomentum)
    (a b : RestStateIndex) (F : PhysicalMomentum→Fin 289→ℂ) (continuous : Continuous F)
    (K : ℝ) (bound : ∀n,‖F n‖≤K) :
    Integrable (fun frequency : FullSpace.Position=>sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency
        (sourceChargedFieldPart (F (FullSpace.physicalMomentum frequency)))) ∧
    ‖∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency
        (sourceChargedFieldPart (F (FullSpace.physicalMomentum frequency)))‖≤ sourceChargedObserverPrice q pL pR a b*K := by
  let M : FullSpace.Position→ℂ:=fun frequency=>sourceSpatialPhase (fun j=>frequency j) position*
    sourceAmputatedFieldVertex q pL pR a b (sourceChargedFieldPart (F (FullSpace.physicalMomentum frequency)))
  have mc : Continuous M := by
    have response:=((observer_continuous q pL pR a b).comp continuous).comp FullSpace.physicalMomentum_continuous
    have coords:=(PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3=>ℝ)).continuous
    dsimp [M]
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  have mb (frequency : FullSpace.Position) : ‖M frequency‖≤ sourceChargedObserverPrice q pL pR a b*K := by
    have phase : ‖sourceSpatialPhase (fun j=>frequency j) position‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
    dsimp only [M]
    rw [norm_mul,phase,one_mul]
    exact (observer_bound q pL pR a b _).trans
      (mul_le_mul_of_nonneg_left (bound _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _)))
  have same : (fun frequency : FullSpace.Position=>sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency
        (sourceChargedFieldPart (F (FullSpace.physicalMomentum frequency))))=
      fun x=>star (sourceFrequencyPacket x)*(M x*sourceFrequencyPacket x) := by
    funext frequency
    rw [sourcePacketIndependentVertex_generated]
    dsimp [M]
    ring
  rw [same]
  exact ⟨packet_integrable M mc _ mb,packet_integral_bound M mc _ mb⟩

/-- Native jet and regular/contact contributions are separately integrable on the same original unit-ball Fourier packet. -/
theorem sourceChargedPacket_parts_integrable (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    Integrable (fun frequency : FullSpace.Position=>sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
        (sourceChargedActualFieldJet q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r))) ∧
    Integrable (fun frequency : FullSpace.Position=>sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
        (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r))) := by
  constructor
  · exact (field_packet_budget q pL pR position a b _
      (sourceChargedNative_continuous q c eta frequencyNonzero positive l r) _
      (fun n=>sourceChargedNative_uniform q n c eta frequencyNonzero positive l r)).1
  · exact (field_packet_budget q pL pR position a b _
      (sourceChargedRegular_continuous q c eta positive l r) _
      (fun n=>sourceChargedRegular_uniform q n c eta positive l r)).1

theorem sourceChargedPacket_parts_bound (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    (‖∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
        (sourceChargedActualFieldJet q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r))‖≤
      sourceChargedObserverPrice q pL pR a b*(sourceChargedSecondPrice q c eta l r+sourceChargedRegularPrice q eta l r)) ∧
    (‖∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
      sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
        (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r))‖≤
      sourceChargedObserverPrice q pL pR a b*sourceChargedRegularPrice q eta l r) := by
  constructor
  · exact (field_packet_budget q pL pR position a b _
      (sourceChargedNative_continuous q c eta frequencyNonzero positive l r) _
      (fun n=>sourceChargedNative_uniform q n c eta frequencyNonzero positive l r)).2
  · exact (field_packet_budget q pL pR position a b _
      (sourceChargedRegular_continuous q c eta positive l r) _
      (fun n=>sourceChargedRegular_uniform q n c eta positive l r)).2

theorem sourceActualChargedPacketResponse_independent (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    sourceActualChargedPacketResponse q c eta frequencyNonzero positive l r a b pL pR position=
      ∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
        sourcePacketIndependentVertex q pL pR a b frequency
          (sourceChargedFieldPart (sourceChargedSecondField q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r)) := by
  rw [sourceActualChargedPacketResponse,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceChargedPacketOperator_ae q c eta frequencyNonzero positive l r a b pL pR position sourceFrequencyPacket] with frequency applied
  rw [applied,sourcePacketIndependentVertex_generated]
  simp only [sourceChargedPacketMultiplierValue,sourceChargedSecondResponse,RCLike.inner_apply,starRingEnd_apply]
  ring

/-- The full packet value is exactly the sum of the native and regular/contact spatial integrals. -/
theorem sourceActualChargedPacketResponse_split (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    sourceActualChargedPacketResponse q c eta frequencyNonzero positive l r a b pL pR position=
      (∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
        sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
          (sourceChargedActualFieldJet q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r)))+
      ∫frequency : FullSpace.Position,sourceSpatialPhase (fun j=>frequency j) position*
        sourcePacketIndependentVertex q pL pR a b frequency (sourceChargedFieldPart
          (sourceRegularMatrix 0*ᵥsourceFullCurrentResidue q (FullSpace.physicalMomentum frequency) (sourcePoleSide c eta) l r)) := by
  rw [sourceActualChargedPacketResponse_independent]
  have parts:=sourceChargedPacket_parts_integrable q c eta frequencyNonzero positive l r a b pL pR position
  rw [←integral_add parts.1 parts.2]
  apply integral_congr_ae
  filter_upwards with frequency
  simp only [sourcePacketIndependentVertex_generated,sourceChargedSecondField,observer_add,mul_add]

/-- The actual response is generated by independent two-leg approximations with the source error bound. -/
theorem sourceActualChargedPacketResponse_generated (q : PhysicalResponsePoint) (c eta : ℝ)
    (frequencyNonzero : c≠0) (positive : 0<eta) (l r a b : RestStateIndex) (pL pR position : PhysicalMomentum) :
    Tendsto (fun n : ℕ=>sourceSmoothChargedPacketResponse q c eta l r a b pL pR position
      (sourcePacketAccuracy n) (sourcePacketAccuracy n) (sourcePacketAccuracy_positive n) (sourcePacketAccuracy_positive n))
      atTop (𝓝 (sourceActualChargedPacketResponse q c eta frequencyNonzero positive l r a b pL pR position)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n=>norm_nonneg _)
    (fun n=>sourceSmoothChargedPacketResponse_error q c eta frequencyNonzero positive l r a b pL pR position
      (sourcePacketAccuracy n) (sourcePacketAccuracy n) (sourcePacketAccuracy_positive n) (sourcePacketAccuracy_positive n))
  have accuracy : Tendsto sourcePacketAccuracy atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [zero_mul,mul_zero,add_zero] using
    (tendsto_const_nhds (x:=sourceChargedResponsePrice q c eta l r a b pL pR)).mul
      ((accuracy.mul (tendsto_const_nhds.add accuracy)).add accuracy)

end LowEnergy.PreparationVacuumChargedSpatialResponse
