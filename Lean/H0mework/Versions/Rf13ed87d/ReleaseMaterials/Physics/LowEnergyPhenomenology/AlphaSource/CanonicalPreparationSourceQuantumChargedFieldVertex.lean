import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceQuantumLockedChargeEvolution
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedPacketFieldReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open GaussQuantumMultiplier
open GaussHistoryHilbert
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumPhysicalModeChargeRead
open PreparationVacuumChargedPacketGreen PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumSourceActionJets PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumRawJointFeedback
open PreparationVacuumFullSlowFieldResponse PreparationVacuumCausalPoleResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumActualSpatialPacket
open PreparationVacuumObservedPoleTensor PreparationVacuumWholeOrigin
open PreparationVacuumNativePoleTensor SourceQuantumGaugeSliceCoordinates
open Filter
open scoped BigOperators Matrix InnerProductSpace Topology
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] sourceModeGaussKernel sourceModeGaussReader fiveKernel

theorem sourceCharged_raw_action_factor (epsilon : ℝ) (precision : 0<epsilon)
    (mu : Fin 4) (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (side edge : Fin 2) :
    lift (quantized (rawActionSymbol (sourceLockedField mu 2) p s))
      (sourceChargedGaussPrepared epsilon precision side edge)=
      (sourceChargedPolarity edge:ℂ) •
        lift (quantized (rawActionSymbol (sourceNativeYField mu) p s))
          (sourceChargedGaussPrepared epsilon precision side edge) := by
  have fiber:=sourceCharged_fullCAR_difference mu p s nondegenerate side edge
  change GaussQuantumMultiplier.quantizer (rawActionSymbol (sourceLockedField mu 2) p s-
    (sourceChargedPolarity edge:ℂ) • rawActionSymbol (sourceNativeYField mu) p s)
      (sourceChargedFiber side edge)=0 at fiber
  rw [map_sub,map_smul,sub_apply,smul_apply,sub_eq_zero] at fiber
  apply GaussHalfDensity.fockHalfDensityEquiv.injective
  rw [map_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.smul_apply,sourceChargedGauss_action_coordinates]
  change GaussQuantumMultiplier.quantizer (rawActionSymbol (sourceLockedField mu 2) p s)
    (sourceChargedFiber side edge) word • sourcePoleBase epsilon precision=_
  rw [fiber]
  simp only [PiLp.smul_apply,smul_smul,smul_eq_mul,quantizer,LinearMap.coe_mk,AddHom.coe_mk]

def sourceQuantumChargedYLeg (q : PhysicalResponsePoint) (mu : Fin 4) (p : PhysicalMomentum)
    (x : physicalChart) (side edge : Fin 2) : H :=
  lift (quantized (rawActionSymbol (sourceNativeYField mu) p (sourceState x.val)))
    (sourceChargedGaussPrepared q.epsilon q.precision side edge)

def sourceQuantumChargedLockedLeg (q : PhysicalResponsePoint) (mu : Fin 4) (p : PhysicalMomentum)
    (x : physicalChart) (side edge : Fin 2) : H :=
  lift (quantized (rawActionSymbol (sourceLockedField mu 2) p (sourceState x.val)))
    (sourceChargedGaussPrepared q.epsilon q.precision side edge)

/-- The external-leg norm is exactly the original full-CAR source action norm on its generated fiber. -/
theorem sourceQuantumChargedYLeg_norm (q : PhysicalResponsePoint) (mu : Fin 4) (p : PhysicalMomentum)
    (x : physicalChart) (side edge : Fin 2) :
    ‖sourceQuantumChargedYLeg q mu p x side edge‖=
      ‖quantized (rawActionSymbol (sourceNativeYField mu) p (sourceState x.val))
        (sourceChargedFiber side edge)‖ := by
  let A : FiberOp:=quantized (rawActionSymbol (sourceNativeYField mu) p (sourceState x.val))
  have base : inner ℂ (sourcePoleBase q.epsilon q.precision) (sourcePoleBase q.epsilon q.precision)=1 := by
    rw [inner_self_eq_norm_sq_to_K,PreparationVacuumMovingPoleGaussReturn.sourcePoleBase_unit]
    norm_num
  have pair : inner ℂ (sourceQuantumChargedYLeg q mu p x side edge)
      (sourceQuantumChargedYLeg q mu p x side edge)=
        inner ℂ (A (sourceChargedFiber side edge)) (A (sourceChargedFiber side edge)) := by
    change inner ℂ (lift A (sourceChargedGaussPrepared q.epsilon q.precision side edge))
      (lift A (sourceChargedGaussPrepared q.epsilon q.precision side edge))=_
    rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply]
    simp only [sourceChargedGauss_action_coordinates,inner_smul_left,inner_smul_right,base,mul_one]
    rfl
  have real:=congrArg Complex.re pair
  change RCLike.re (inner ℂ (sourceQuantumChargedYLeg q mu p x side edge)
    (sourceQuantumChargedYLeg q mu p x side edge))=
      RCLike.re (inner ℂ (A (sourceChargedFiber side edge)) (A (sourceChargedFiber side edge))) at real
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at real
  change ‖sourceQuantumChargedYLeg q mu p x side edge‖=‖A (sourceChargedFiber side edge)‖
  nlinarith [norm_nonneg (sourceQuantumChargedYLeg q mu p x side edge),norm_nonneg (A (sourceChargedFiber side edge))]

private theorem locked_leg (q : PhysicalResponsePoint) (mu : Fin 4) (p : PhysicalMomentum)
    (x : physicalChart) (side edge : Fin 2) :
    sourceQuantumChargedLockedLeg q mu p x side edge=
      (sourceChargedPolarity edge:ℂ) • sourceQuantumChargedYLeg q mu p x side edge :=
  sourceCharged_raw_action_factor q.epsilon q.precision mu p (sourceState x.val)
    (PreparationVacuumSourceFieldFamily.coframe_nondegenerate x) side edge

def sourceQuantumCanonicalRead (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2) :
    (H→L[ℂ] H)→L[ℂ] ℂ :=
  (innerSL ℂ (sourceQuantumChargedYLeg q mu pL xL a b)).comp
    (ContinuousLinearMap.apply ℂ H (sourceQuantumChargedYLeg q nu pR xR c d))

/-- Both independent actual source legs supply their signs before any H, resolvent or reader is applied. -/
theorem sourceQuantumCharged_twoLeg_factor (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2) (T : H→L[ℂ] H) :
    inner ℂ (sourceQuantumChargedLockedLeg q mu pL xL a b)
      (T (sourceQuantumChargedLockedLeg q nu pR xR c d))=
      ((sourceChargedPolarity b:ℂ)*(sourceChargedPolarity d:ℂ))*
        sourceQuantumCanonicalRead q mu nu pL pR xL xR a b c d T := by
  rw [locked_leg,locked_leg,map_smul,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal,sourceQuantumCanonicalRead,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply]
  ring

def sourceQuantumChargedCanonicalCurrent (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2)
    (V : Fin 289→ℂ) (t : ℝ) : ℂ :=
  sourceQuantumCanonicalRead q mu nu pL pR xL xR a b c d
    (sourceModeGaussKernel V q pL pR t)

def sourceQuantumChargedLockedCurrent (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2)
    (V : Fin 289→ℂ) (t : ℝ) : ℂ :=
  inner ℂ (sourceQuantumChargedLockedLeg q mu pL xL a b)
    (sourceModeGaussKernel V q pL pR t (sourceQuantumChargedLockedLeg q nu pR xR c d))

theorem sourceQuantumChargedCanonicalCurrent_generated (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2)
    (V : Fin 289→ℂ) (t : ℝ) :
    sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d V t=
      (∑rho : Fin 4,sourceChargedCoefficient V rho*
        sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d
          (sourceChargedLockedField rho) t)+
      sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d
        (sourceChargedFieldRemainder V) t := by
  have locked (rho : Fin 4) :
      sourceModeGaussReader (sourceChargedLockedField rho) pR q.F=
        PreparationVacuumRawJointFeedback.rawReader (sourceLockedField rho 2) pR q.F 0 :=
    sourceModeGaussReader_real (sourceLockedField rho 2) pR q.F
  simp only [sourceQuantumChargedCanonicalCurrent,sourceModeGaussKernel]
  rw [sourceChargedGaussReader_generated]
  simp only [mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,map_add,map_sum,map_smul,smul_eq_mul]
  simp only [locked]

def sourceQuantumCanonicalLegPrice (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2) : ℝ :=
  ‖sourceQuantumChargedYLeg q mu pL xL a b‖*‖sourceQuantumChargedYLeg q nu pR xR c d‖

theorem sourceQuantumCanonicalRead_price (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2) (T : H→L[ℂ] H) :
    ‖sourceQuantumCanonicalRead q mu nu pL pR xL xR a b c d T‖≤
      sourceQuantumCanonicalLegPrice q mu nu pL pR xL xR a b c d*‖T‖ := by
  have h:=(norm_inner_le_norm (𝕜:=ℂ) (sourceQuantumChargedYLeg q mu pL xL a b)
      (T (sourceQuantumChargedYLeg q nu pR xR c d))).trans
    (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _))
  simpa only [sourceQuantumCanonicalRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply,sourceQuantumCanonicalLegPrice,mul_assoc,mul_comm,mul_left_comm] using h

/-- The remainder response price and the independently sourced external-leg price stay separate. -/
theorem sourceQuantumChargedCanonicalCurrent_remainder_price (q : PhysicalResponsePoint) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2)
    (V : Fin 289→ℂ) (t : ℝ) :
    ‖sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d
      (sourceChargedFieldRemainder V) t‖≤
      sourceQuantumCanonicalLegPrice q mu nu pL pR xL xR a b c d*
        sourceChargedRemainderCurrentPrice q V pL pR t := by
  have h:=sourceQuantumCanonicalRead_price q mu nu pL pR xL xR a b c d
    (sourceModeGaussKernel (sourceChargedFieldRemainder V) q pL pR t)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  rw [sourceModeGaussKernel_generated]
  exact (norm_sum_le _ _).trans (by simp only [norm_smul,sourceChargedRemainderCurrentPrice];rfl)

/-- The paid actual delta-squared jet and Regular0/full-current contact feed the two independent Gauss legs. -/
theorem sourceQuantumChargedSecondCurrent_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (zeta : sourceCausalDomain n) (l r : RestStateIndex) (mu nu : Fin 4)
    (pL pR : PhysicalMomentum) (xL xR : physicalChart) (a b c d : Fin 2) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun scale : ℝ=>(scale:ℂ)^2*
      sourceQuantumChargedLockedCurrent q mu nu pL pR xL xR a b c d
        (sourceChargedFieldPart (sourceJointCausalField q n zeta.val l r scale)) t)
      (𝓝[>] 0) (𝓝 (((sourceChargedPolarity b:ℂ)*(sourceChargedPolarity d:ℂ))*
        sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d
        (sourceChargedFieldPart (sourceChargedSecondField q n zeta.val l r)) t)) := by
  have part (V : Fin 289→ℂ) :
      sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d (sourceChargedFieldPart V) t=
        ∑rho : Fin 4,sourceChargedCoefficient V rho*
          sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d (sourceChargedLockedField rho) t := by
    unfold sourceQuantumChargedCanonicalCurrent
    rw [sourceModeGaussKernel_generated]
    unfold sourceChargedFieldPart
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [sourceModeGaussKernel_generated,map_sum,map_smul,smul_eq_mul,mul_assoc,Finset.mul_sum]
  have limit : Tendsto (fun scale : ℝ=>(scale:ℂ)^2*
      sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d
        (sourceChargedFieldPart (sourceJointCausalField q n zeta.val l r scale)) t)
      (𝓝[>] 0) (𝓝 (sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d
        (sourceChargedFieldPart (sourceChargedSecondField q n zeta.val l r)) t)) := by
    simp only [part,Finset.mul_sum,←mul_assoc]
    exact tendsto_finsetSum _ (fun rho _=>
      (sourceChargedSecondField_generated q n zeta l r rho nonrealL nonrealR).mul_const _)
  have factor (V : Fin 289→ℂ) : sourceQuantumChargedLockedCurrent q mu nu pL pR xL xR a b c d V t=
      ((sourceChargedPolarity b:ℂ)*(sourceChargedPolarity d:ℂ))*
        sourceQuantumChargedCanonicalCurrent q mu nu pL pR xL xR a b c d V t :=
    sourceQuantumCharged_twoLeg_factor q mu nu pL pR xL xR a b c d (sourceModeGaussKernel V q pL pR t)
  have actual:=limit.const_mul ((sourceChargedPolarity b:ℂ)*(sourceChargedPolarity d:ℂ))
  apply actual.congr'
  filter_upwards [] with scale
  rw [factor]
  ring

end LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge
