import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticIRPacket
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMObservable

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource ProofFreeRicherAnholonomicSource PreparationVacuumOriginalGreenFeedback
open ActualEMCurrentSplit ActualEMResponseSplit ActualEMObservable ActualElectronOwnerTest
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalQuantumLockedCharge
open Stage9C.Material.SpinPair Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
attribute [local irreducible] emInsertion emStaticRegularOrigin emAngularCoefficient
  sourceActualPreparedCurrent emUnitSourceCurrent emUnitDetectorCovector

/-- A fixed pair of original full currents reads the literal EM tensor through its source-fixed coordinate duals. -/
def emCurrentPacketRead (fd fs : Fin 289→ℂ) : (Matrix (Fin 4) (Fin 4) ℂ) →L[ℂ] ℂ :=
  ({toFun:=fun M=>dotProduct (emCoordinateCurrent fd) (M*ᵥemCoordinateCurrent fs)
    map_add':=fun M N=>by simp only [Matrix.add_mulVec,dotProduct_add]
    map_smul':=fun r M=>by simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,RingHom.id_apply]} :
    (Matrix (Fin 4) (Fin 4) ℂ) →ₗ[ℂ] ℂ).toContinuousLinearMap

/-- The actual EM component of the spatial response is reconstructed by the same coordinate-dual injection. -/
def emCurrentPacketField (M : Matrix (Fin 4) (Fin 4) ℂ) (fs : Fin 289→ℂ) : Fin 289→ℂ :=
  emCoordinateDual*ᵥ(M*ᵥemCoordinateCurrent fs)

/-- At each original Green value this field is exactly the EM projection of the full response to the EM part of the actual source current. -/
theorem em_current_packet_source_field (G : Matrix (Fin 289) (Fin 289) ℂ) (fs : Fin 289→ℂ) :
    emCurrentPacketField (emResponseTensor G) fs=emCurrentForce (G*ᵥemCurrentForce fs) := by
  change emCoordinateDual*ᵥ((emInsertion.transpose*G*emInsertion)*ᵥemCoordinateCurrent fs)=
    emCoordinateDual*ᵥ(emInsertion.transpose*ᵥ(G*ᵥemCurrentForce fs))
  rw [em_current_force_insertion]
  simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]

private theorem em_pair_field_read (M : Matrix (Fin 4) (Fin 4) ℂ) (fd fs : Fin 289→ℂ) :
    dotProduct fd (emCurrentPacketField M fs)=emCurrentPacketRead fd fs M := by
  change dotProduct fd (emCoordinateDual*ᵥ(M*ᵥemCoordinateCurrent fs))=
    dotProduct (emCoordinateCurrent fd) (M*ᵥemCoordinateCurrent fs)
  simp only [emCoordinateDual,Matrix.smul_mulVec,dotProduct_smul,emCoordinateCurrent,emCurrent,smul_dotProduct]
  rw [←Matrix.dotProduct_transpose_mulVec]
  congr 1
  exact dotProduct_comm _ _

/-- The original action-normalized detector consumes this precise EM spatial field. -/
theorem em_unit_current_packet_actual (M : Matrix (Fin 4) (Fin 4) ℂ)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
      (emCurrentPacketField M (emUnitSourceCurrent qs sSL sSR mu S))=
      emCurrentPacketRead (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (emUnitSourceCurrent qs sSL sSR mu S) M := by
  rw [←actualElectronFieldTest_actual branch qd dSL dSR lambda T hzd hwd,
    ←em_unit_detector_actual,em_pair_field_read]

private theorem em_detector_source_covector (branch : Fin 2) (q : PhysicalResponsePoint)
    (sL sR : Fin 2) (lambda : ℂ) (T : ℝ) :
    emUnitDetectorCovector branch q sL sR lambda T=
      (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹) • emUnitSourceCurrent q sL sR lambda T := by
  ext i
  simp only [emUnitDetectorCovector,actualElectronFieldTest,emUnitSourceCurrent,emUnitSourceTest,
    smul_apply,ContinuousLinearMap.comp_apply,Pi.smul_apply]

/-- This vector retains all64 original prepared weights and the entire original full-field leg correction. -/
def emCorrectedPacketCurrent (q : PhysicalResponsePoint) (sL sR : Fin 2) (lambda : ℂ) (T : ℝ) : Fin 4→ℂ :=
  emCoordinateCurrent (sourceActualPreparedCurrent q 0 0 sL 0 sR 0 lambda T-emUnitSourceCorrection q sL sR lambda T)

/-- Both independent actual units return their source normalizations, with exactly one original h*c divisor. -/
theorem em_unit_packet_once_action (M : Matrix (Fin 4) (Fin 4) ℂ)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0)
    (hzs : qs.z.im≠0) (hws : qs.w.im≠0) :
    emCurrentPacketRead (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (emUnitSourceCurrent qs sSL sSR mu S) M=
      (sourceActualLegNormalization qd dSL 0 dSR 0*sourceActualLegNormalization qs sSL 0 sSR 0)/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
      dotProduct (emCorrectedPacketCurrent qd dSL dSR lambda T)
        (M*ᵥemCorrectedPacketCurrent qs sSL sSR mu S) := by
  change dotProduct (emCoordinateCurrent _) (M*ᵥemCoordinateCurrent _)=_
  rw [em_detector_source_covector,em_unit_source_current_return qd dSL dSR lambda T hzd hwd,
    em_unit_source_current_return qs sSL sSR mu S hzs hws]
  simp only [emCoordinateCurrent,emCurrent,emCorrectedPacketCurrent,Matrix.mulVec_smul,
    smul_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

/-- Both source-fixed full current vectors consume the complete actual IR Fourier limit. -/
theorem em_fixed_current_packet_ir (kappa : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (fd fs : Fin 289→ℂ) :
    Tendsto (fun scale : ℝ=>emCurrentPacketRead fd fs (emFullIRPacket scale test x)) (𝓝[>] 0)
      (𝓝 (emCurrentPacketRead fd fs (emLeadingPacket kappa 0 test x))) := by
  have tensor : Tendsto (fun scale : ℝ=>emFullIRPacket scale test x) (𝓝[>] 0)
      (𝓝 (emLeadingPacket kappa 0 test x)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    exact em_full_ir_packet_leading kappa test x a b
  exact (emCurrentPacketRead fd fs).continuous.tendsto _ |>.comp tensor

/-- The actual independently normalized finite-window electron pair is an original detector on the generated Fourier field. -/
theorem em_actual_unit_packet_ir (kappa : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    Tendsto (fun scale : ℝ=>sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
      (emCurrentPacketField (emFullIRPacket scale test x) (emUnitSourceCurrent qs sSL sSR mu S))) (𝓝[>] 0)
      (𝓝 (emCurrentPacketRead (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (emUnitSourceCurrent qs sSL sSR mu S) (emLeadingPacket kappa 0 test x))) := by
  simpa only [em_unit_current_packet_actual _ branch qd qs dSL dSR sSL sSR lambda mu T S hzd hwd] using
    em_fixed_current_packet_ir kappa test x (emUnitDetectorCovector branch qd dSL dSR lambda T)
      (emUnitSourceCurrent qs sSL sSR mu S)

/-- The complete current-pair coefficients multiply one local packet and every original Newton Hessian component. -/
theorem em_current_packet_newton (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (fd fs : Fin 289→ℂ) :
    emCurrentPacketRead fd fs (emLeadingPacket kappa d test x)=
      emCurrentPacketRead fd fs emStaticRegularOrigin*emPacket test x-
      ∑i : Fin 3,∑j : Fin 3,emCurrentPacketRead fd fs (emAngularCoefficient i j)*emNewtonHessian kappa d test x i j := by
  have tensor : emLeadingPacket kappa d test x=emPacket test x • emStaticRegularOrigin-
      ∑i : Fin 3,∑j : Fin 3,emNewtonHessian kappa d test x i j • emAngularCoefficient i j := by
    ext a b
    rw [em_leading_packet_return kappa positive d radial]
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul,mul_comm]
  rw [tensor,map_sub]
  simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

/-- The regulated source Newton representation and the actual whole-Green packet have the same generated current-pair limit. -/
theorem em_current_newton_radial (kappa : ℂ) (positive : 0<kappa.re)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (fd fs : Fin 289→ℂ) :
    Tendsto (fun d : ℝ=>emCurrentPacketRead fd fs emStaticRegularOrigin*emPacket test x-
      ∑i : Fin 3,∑j : Fin 3,emCurrentPacketRead fd fs (emAngularCoefficient i j)*emNewtonHessian kappa d test x i j)
      (𝓝[>] 0) (𝓝 (emCurrentPacketRead fd fs (emLeadingPacket kappa 0 test x))) := by
  have tensor : Tendsto (fun d : ℝ=>emLeadingPacket kappa d test x) (𝓝[>] 0)
      (𝓝 (emLeadingPacket kappa 0 test x)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    exact em_leading_packet_radial kappa positive test x a b
  have generated := (emCurrentPacketRead fd fs).continuous.tendsto _ |>.comp tensor
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with d dp
  exact em_current_packet_newton kappa positive d dp test x fd fs


/-- Actual unit detector/source currents retain all directional coefficients in the source Newton observation. -/
theorem em_actual_unit_packet_newton (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dSL dSR sSL sSR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
      (emCurrentPacketField (emLeadingPacket kappa d test x) (emUnitSourceCurrent qs sSL sSR mu S))=
      emCurrentPacketRead (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (emUnitSourceCurrent qs sSL sSR mu S) emStaticRegularOrigin*emPacket test x-
      ∑i : Fin 3,∑j : Fin 3,emCurrentPacketRead (emUnitDetectorCovector branch qd dSL dSR lambda T)
        (emUnitSourceCurrent qs sSL sSR mu S) (emAngularCoefficient i j)*emNewtonHessian kappa d test x i j := by
  rw [em_unit_current_packet_actual _ branch qd qs dSL dSR sSL sSR lambda mu T S hzd hwd]
  exact em_current_packet_newton kappa positive d radial test x _ _

private theorem em_bare_packet_pair (M : Matrix (Fin 4) (Fin 4) ℂ)
    (pointD pointS : BasePoint) (sideD edgeD sideS edgeS : Fin 2) :
    emCurrentPacketRead
      (actualRestNativeComplexForcingCovector pointD (sourceChargedRestIndex sideD edgeD) (sourceChargedRestIndex sideD edgeD))
      (actualRestNativeComplexForcingCovector pointS (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS)) M=
      (sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ)*(16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
        dotProduct (emBareRestDirection sideD) (M*ᵥemBareRestDirection sideS) := by
  change dotProduct (emCoordinateCurrent _) (M*ᵥemCoordinateCurrent _)=_
  simp only [emCoordinateCurrent,em_bare_diagonal_current,smul_smul,Matrix.mulVec_smul,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

/-- The local packet coefficient comes from the complete regular static EM tensor. -/
def emBareLocalCoefficient (sideD sideS : Fin 2) : ℂ :=
  (16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*(rootTwo*rootFifteen)*
    (-36823/448800+sourceRestSign sideD*sourceRestSign sideS*(lapse:ℂ)^2*(1699/96480))

/-- The complete bare four-current selects this longitudinal Newton-Hessian coefficient, with both signs retained. -/
def emBareDirectionalCoefficient (sideD sideS : Fin 2) : ℂ :=
  (16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
    ((rootTwo*rootFifteen)/96+(sourceRestSign sideD+sourceRestSign sideS)*(lapse:ℂ)*(3/40)+
      sourceRestSign sideD*sourceRestSign sideS*(lapse:ℂ)^2*(rootTwo*rootFifteen)*(137677/301500))

set_option maxHeartbeats 2400000 in
/-- Every original charged/neutral bare side/edge pair has the exact source spatial return, divided by the action and speed once. -/
theorem em_bare_once_action_newton (kappa : ℂ) (positive : 0<kappa.re) (d : ℝ) (radial : 0<d)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) (branch : Fin 2)
    (pointD pointS : BasePoint) (sideD edgeD sideS edgeS : Fin 2) :
    emCurrentPacketRead
      (actualRestNativeComplexForcingCovector pointD (sourceChargedRestIndex sideD edgeD) (sourceChargedRestIndex sideD edgeD))
      (actualRestNativeComplexForcingCovector pointS (sourceChargedRestIndex sideS edgeS) (sourceChargedRestIndex sideS edgeS))
      (emLeadingPacket kappa d test x)/((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)=
      ((sourceActualPhaseCharge edgeD:ℂ)*(sourceActualPhaseCharge edgeS:ℂ))/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)*
        (emBareLocalCoefficient sideD sideS*emPacket test x-
          emBareDirectionalCoefficient sideD sideS*emNewtonHessian kappa d test x 2 2) := by
  rw [em_bare_packet_pair]
  simp only [emBareRestDirection,Matrix.mulVec,dotProduct,Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [zero_mul,mul_zero,one_mul,mul_one,add_zero]
  simp_rw [em_leading_packet_return kappa positive d radial]
  simp only [em_static_regular_explicit,Fin.sum_univ_three]
  norm_num [emAngularCoefficient,Matrix.single_apply,Matrix.diagonal_apply,Matrix.cons_val,
    emBareLocalCoefficient,emBareDirectionalCoefficient,Fin.ext_iff]
  ring

end LowEnergy.GaussComposite.ActualEMCarrierOwn
