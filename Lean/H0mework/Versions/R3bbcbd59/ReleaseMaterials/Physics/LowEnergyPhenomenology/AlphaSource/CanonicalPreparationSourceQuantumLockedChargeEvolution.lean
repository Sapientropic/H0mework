import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceQuantumLockedPoleCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreHilbert
open GaussCoreDifferential PreparationVacuumElectromagneticIdentity
open Electromagnetic.ExternalState
open CanonicalGradedSpatialSource PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumPhysicalLockedN1Balance
open PreparationVacuumPhysicalLockedGaussBalance PreparationVacuumWeightedChargeActionWard
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumPhysicalModeChargeRead
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumNoetherChart
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumSourceActionJets
open PreparationVacuumPropagationPencil PreparationVacuumPhysicalPoleLegDynamics
open GaussHistoryHilbert Filter
open PreparationVacuumSourceFieldFamily SourceQuantumFockGauge GaussFockLift
open PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis CanonicalPhysicalSpatial
open GaussQuantumMultiplier
open scoped BigOperators Topology InnerProductSpace
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local irreducible] sourceTestApprox sourceApprox sourcePolePrepared physicalTime
  jointResolvent sourceHamiltonian sourceLockedRawChargeCore sourceLockedPairCore sourceLockedChargeCore
  noetherReader noetherTimeInsertion sourceChargedFullInsertion sourceN1Projection
  sourceModeGaussKernel fiveKernel leftGenerator rightGenerator

private def testApproxLinear (F : GaussUnitaryHistory.Index) : H→ₗ[ℂ] QuantumTest where
  toFun:=sourceTestApprox F
  map_add' u v:=by
    apply GaussCoreHilbert.embed_injective
    simp only [map_add,sourceTestApprox_embed]
  map_smul' c v:=by
    apply GaussCoreHilbert.embed_injective
    simp only [map_smul,sourceTestApprox_embed,RingHom.id_apply]

def sourceQuantumChargedPrimal (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) : H :=
  jointResolvent p q.F z 0 (physicalTime p q.F t 0
    (sourceChargedGaussPrepared q.epsilon q.precision side edge))

def sourceQuantumChargeDifference (mu : Fin 4) (p : PhysicalMomentum)
    (s : ActionState) (edge : Fin 2) : H→L[ℂ] H :=
  lift (quantized (rawActionSymbol (sourceLockedField mu 2) p s-
    (sourceChargedPolarity edge:ℂ) • rawActionSymbol (sourceNativeYField mu) p s))

def sourceQuantumChargeProjectionCommutator (q : PhysicalResponsePoint) (mu : Fin 4)
    (p : PhysicalMomentum) (s : ActionState) (edge : Fin 2) : H→L[ℂ] H :=
  sourceQuantumChargeDifference mu p s edge*sourceApprox q.F-
    sourceApprox q.F*sourceQuantumChargeDifference mu p s edge

theorem sourceQuantumCharge_projected_balance (q : PhysicalResponsePoint) (mu : Fin 4)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0) (side edge : Fin 2) :
    sourceQuantumChargeDifference mu p s edge
      (sourceApprox q.F (sourceChargedGaussPrepared q.epsilon q.precision side edge))=
      sourceQuantumChargeProjectionCommutator q mu p s edge
        (sourceChargedGaussPrepared q.epsilon q.precision side edge) := by
  have zero:=sourceCharged_fullGauss_difference q.epsilon q.precision mu p s nondegenerate side edge
  change sourceQuantumChargeDifference mu p s edge
    (sourceChargedGaussPrepared q.epsilon q.precision side edge)=0 at zero
  simp only [sourceQuantumChargeProjectionCommutator,sub_apply,mul_apply_eq_comp,zero,map_zero,sub_zero]

def sourceQuantumChargePropagationCommutator (q : PhysicalResponsePoint) (mu : Fin 4)
    (p : PhysicalMomentum) (s : ActionState) (edge : Fin 2) (z : ℂ) (t : ℝ) : H→L[ℂ] H :=
  sourceQuantumChargeDifference mu p s edge*jointResolvent p q.F z 0*physicalTime p q.F t 0-
    jointResolvent p q.F z 0*physicalTime p q.F t 0*sourceQuantumChargeDifference mu p s edge

/-- The original propagator produces its actual commutator defect; source-zero is not propagated by premise. -/
theorem sourceQuantumCharge_propagated_balance (q : PhysicalResponsePoint) (mu : Fin 4)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) :
    sourceQuantumChargeDifference mu p s edge (sourceQuantumChargedPrimal q p side edge z t)=
      sourceQuantumChargePropagationCommutator q mu p s edge z t
        (sourceChargedGaussPrepared q.epsilon q.precision side edge) := by
  have zero:=sourceCharged_fullGauss_difference q.epsilon q.precision mu p s nondegenerate side edge
  change sourceQuantumChargeDifference mu p s edge
    (sourceChargedGaussPrepared q.epsilon q.precision side edge)=0 at zero
  simp only [sourceQuantumChargedPrimal,sourceQuantumChargePropagationCommutator,
    sub_apply,mul_apply_eq_comp,zero,map_zero,sub_zero]

theorem sourceQuantumCharge_propagated_price (q : PhysicalResponsePoint) (mu : Fin 4)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) :
    ‖sourceQuantumChargeDifference mu p s edge (sourceQuantumChargedPrimal q p side edge z t)‖≤
      ‖sourceQuantumChargePropagationCommutator q mu p s edge z t‖ := by
  rw [sourceQuantumCharge_propagated_balance q mu p s nondegenerate side edge z t]
  simpa only [sourceChargedGauss_unit,mul_one] using
    (sourceQuantumChargePropagationCommutator q mu p s edge z t).le_opNorm
      (sourceChargedGaussPrepared q.epsilon q.precision side edge)

theorem sourceQuantumChargedPrimal_moving (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) :
    sourceQuantumChargedPrimal q p side edge z t=∑state : RestStateIndex,
      sourceChargedMovingCoefficient p side edge state • sourceActualN1Primal q p state z t := by
  unfold sourceQuantumChargedPrimal
  rw [sourceChargedGaussPrepared_moving q.epsilon q.precision p side edge,map_sum,map_sum]
  simp only [map_smul,sourceActualN1Primal]

/-- Original time and full resolvent generate the Number-one range of the actual charged maker. -/
theorem sourceQuantumChargedPrimal_N1 (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceN1Projection (sourceQuantumChargedPrimal q p side edge z t)=
      sourceQuantumChargedPrimal q p side edge z t := by
  rw [sourceQuantumChargedPrimal_moving,map_sum]
  simp only [map_smul,sourceActualN1Primal_generated q p _ z t nonreal]

theorem sourceQuantumChargedPrimal_coreN1 (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceN1Core (sourceTestApprox q.F (sourceQuantumChargedPrimal q p side edge z t))=
      sourceTestApprox q.F (sourceQuantumChargedPrimal q p side edge z t) := by
  rw [sourceQuantumChargedPrimal_moving]
  change sourceN1Core (testApproxLinear q.F (∑state : RestStateIndex,
    sourceChargedMovingCoefficient p side edge state • sourceActualN1Primal q p state z t))=
      testApproxLinear q.F (∑state : RestStateIndex,
        sourceChargedMovingCoefficient p side edge state • sourceActualN1Primal q p state z t)
  rw [map_sum]
  unfold sourceN1Core
  simp only [map_smul,map_sum]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state _
  rw [←smul_add]
  exact congrArg (fun f : QuantumTest=>sourceChargedMovingCoefficient p side edge state • f)
    (sourceActualN1Primal_core q p state z t nonreal)

theorem sourceQuantumChargedPrimal_pair_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceLockedPairCore (sourceTestApprox q.F (sourceQuantumChargedPrimal q p side edge z t))=0 :=
  (congrArg sourceLockedPairCore (sourceQuantumChargedPrimal_coreN1 q p side edge z t nonreal)).symm.trans
    (sourceLockedPair_sourceN1_zero _)

theorem sourceQuantumChargedPrimal_pairTorque_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (actualP k : PhysicalMomentum) :
    sourceLockedPairTorque actualP k
      (sourceTestApprox q.F (sourceQuantumChargedPrimal q p side edge z t))=0 := by
  have full : sourceLockedPairCore (fullSourceAction actualP
      (sourceTestApprox q.F (sourceQuantumChargedPrimal q p side edge z t)))=0 :=
    (congrArg (fun f : QuantumTest=>sourceLockedPairCore (fullSourceAction actualP f))
      (sourceQuantumChargedPrimal_coreN1 q p side edge z t nonreal)).symm.trans
        (sourceLockedPair_fullSource_N1_zero actualP _)
  unfold sourceLockedPairTorque
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,
    sourceQuantumChargedPrimal_pair_zero q p side edge z t nonreal,map_zero,full,sub_zero]

private theorem sourceQuantumChargedPrimal_rightPair_zero (q : PhysicalResponsePoint)
    (p : PhysicalMomentum) (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0)
    (actualP : PhysicalMomentum) :
    sourceLockedPairCore (rightCompressionDefect actualP q.F (sourceQuantumChargedPrimal q p side edge z t)+
      rightUncutDefect actualP q.F (sourceQuantumChargedPrimal q p side edge z t))=0 := by
  rw [sourceQuantumChargedPrimal_moving]
  have compression (y : H) : rightCompressionDefect actualP q.F y=
      testApproxLinear q.F (compression actualP q.F y)-
        physicalAction actualP (testApproxLinear q.F y) := rfl
  have uncut (y : H) : rightUncutDefect actualP q.F y=
      testApproxLinear q.F (sourceUncutAction actualP q.F y)-
        GaussYukawaOperator.originalAction (testApproxLinear q.F y) := rfl
  simp only [compression,uncut,map_sum,map_smul]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,←Finset.sum_add_distrib,map_sum]
  apply Finset.sum_eq_zero
  intro state _
  rw [←smul_sub,←smul_sub,←smul_add,map_smul]
  change sourceChargedMovingCoefficient p side edge state •
    sourceLockedPairCore (rightCompressionDefect actualP q.F (sourceActualN1Primal q p state z t)+
      rightUncutDefect actualP q.F (sourceActualN1Primal q p state z t))=0
  rw [sourceLockedActualN1_rightDefect_pair_zero q p state z t nonreal,smul_zero]

/-- Actual H returns all projection, compression, uncut and source torque terms. No propagated charge-zero is assumed. -/
theorem sourceQuantumChargedPrimal_lockedInsertion (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    noetherTimeInsertion (sourcePhysicalMaterialPoint q pL pR) (sourceLockedField 0 2)
      (sourceQuantumChargedPrimal q pR side edge z t)=
        sourceLockedN1WardReturn q pL pR (sourceQuantumChargedPrimal q pR side edge z t) := by
  rw [sourceLockedInsertion_generated]
  have momentum : pR+(pL-pR)=pL := by ext i;simp
  change sourceApprox q.F (embed (sourceLockedWeightedWard pR (pL-pR)
    (sourceTestApprox q.F (sourceQuantumChargedPrimal q pR side edge z t))))+
      leftCompressionDefect (pR+(pL-pR)) q.F (sourceLockedRawChargeCore
        (sourceTestApprox q.F (sourceQuantumChargedPrimal q pR side edge z t)))+
      leftUncutDefect (pR+(pL-pR)) q.F (sourceLockedRawChargeCore
        (sourceTestApprox q.F (sourceQuantumChargedPrimal q pR side edge z t)))-
      sourceApprox q.F (embed (sourceLockedRawChargeCore
        (rightCompressionDefect pR q.F (sourceQuantumChargedPrimal q pR side edge z t)+
          rightUncutDefect pR q.F (sourceQuantumChargedPrimal q pR side edge z t))))=_
  simp only [sourceLockedWeightedWard,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    sourceQuantumChargedPrimal_pairTorque_zero q pR side edge z t nonreal,sub_zero]
  rw [sourceLockedRawCore_generated]
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,
    sourceQuantumChargedPrimal_pair_zero q pR side edge z t nonreal,
    sourceQuantumChargedPrimal_rightPair_zero q pR side edge z t nonreal,sub_zero,momentum]
  rfl

def sourceQuantumChargedInsertionChannels (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (y : H) (mu : Fin 4) : H :=
  sourceChargedCoefficient V mu •
    (if mu=0 then sourceLockedN1WardReturn q pL pR y
      else noetherTimeInsertion (sourcePhysicalMaterialPoint q pL pR) (sourceLockedField mu 2) y)

theorem sourceQuantumChargedPrimal_fullInsertion (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (V : Fin 289→ℂ) (side edge : Fin 2)
    (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceChargedFullInsertion (sourcePhysicalMaterialPoint q pL pR) V
      (sourceQuantumChargedPrimal q pR side edge z t)=
      (∑mu : Fin 4,sourceQuantumChargedInsertionChannels q pL pR V
        (sourceQuantumChargedPrimal q pR side edge z t) mu)+
      sourceChargedFullInsertion (sourcePhysicalMaterialPoint q pL pR)
        (sourceChargedFieldRemainder V) (sourceQuantumChargedPrimal q pR side edge z t) := by
  rw [sourceChargedInsertion_generated]
  simp only [sum_apply,smul_apply,add_apply,sourceQuantumChargedInsertionChannels]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  split_ifs with zero
  · subst mu
    rw [sourceQuantumChargedPrimal_lockedInsertion q pL pR side edge z t nonreal]
  · rfl

def sourceQuantumChargedInsertionPrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (y : H) : ℝ :=
  (∑mu : Fin 4,‖sourceQuantumChargedInsertionChannels q pL pR V y mu‖)+
    ‖sourceChargedFullInsertion (sourcePhysicalMaterialPoint q pL pR) (sourceChargedFieldRemainder V) y‖

theorem sourceQuantumChargedPrimal_source_price (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (V : Fin 289→ℂ) (side edge : Fin 2)
    (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    ‖sourceChargedFullInsertion (sourcePhysicalMaterialPoint q pL pR) V
      (sourceQuantumChargedPrimal q pR side edge z t)‖≤
        sourceQuantumChargedInsertionPrice q pL pR V (sourceQuantumChargedPrimal q pR side edge z t) := by
  rw [sourceQuantumChargedPrimal_fullInsertion q pL pR V side edge z t nonreal]
  unfold sourceQuantumChargedInsertionPrice
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)

/-- The time derivative is generated by the original full H on this same Gauss restriction. -/
theorem sourceQuantumChargedPrimal_time (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (side edge : Fin 2) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    HasDerivAt (fun age=>sourceQuantumChargedPrimal q p side edge z age)
      ((-Complex.I) • sourceHamiltonian p q.F (sourceQuantumChargedPrimal q p side edge z t)) t := by
  have time:=SourceFiniteUnitary.time_derivative (sourceHamiltonian p q.F) t
    (sourceChargedGaussPrepared q.epsilon q.precision side edge)
  let R:=(jointResolvent p q.F z 0).restrictScalars ℝ
  have generated:=R.hasFDerivAt.comp_hasDerivAt t time
  have commute:=sourceResolvent_commutes p q.F z nonreal
  have order:=(SourceFiniteUnitary.time_commutes (sourceHamiltonian p q.F)
    (sourceHamiltonian p q.F) (Commute.refl _) t).eq
  convert! generated using 1
  · funext age
    simp only [sourceQuantumChargedPrimal,R,Function.comp_def,
      ContinuousLinearMap.coe_restrictScalars',physicalTime,sourceHamiltonian]
  · simp only [R,sourceQuantumChargedPrimal,ContinuousLinearMap.coe_restrictScalars',
      map_smul,physicalTime,sourceHamiltonian]
    have matrix : sourceHamiltonian p q.F*jointResolvent p q.F z 0*
        SourceFiniteUnitary.time (sourceHamiltonian p q.F) t=
      jointResolvent p q.F z 0*SourceFiniteUnitary.time (sourceHamiltonian p q.F) t*
        sourceHamiltonian p q.F := by
      rw [←commute,mul_assoc,order,←mul_assoc]
    simpa only [sourceHamiltonian,mul_apply_eq_comp] using
      congrArg (fun A : H→L[ℂ] H=>(-Complex.I) •
        A (sourceChargedGaussPrepared q.epsilon q.precision side edge)) matrix

def sourceQuantumChargedRead (q : PhysicalResponsePoint) (a b c d : Fin 2) :
    (H→L[ℂ] H)→L[ℂ] ℂ :=
  (innerSL ℂ (sourceChargedGaussPrepared q.epsilon q.precision a b)).comp
    (ContinuousLinearMap.apply ℂ H (sourceChargedGaussPrepared q.epsilon q.precision c d))

theorem sourceQuantumChargedRead_price (q : PhysicalResponsePoint) (a b c d : Fin 2) :
    ‖sourceQuantumChargedRead q a b c d‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  simp only [sourceQuantumChargedRead,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,innerSL_apply_apply]
  have price:=(norm_inner_le_norm (𝕜:=ℂ)
    (sourceChargedGaussPrepared q.epsilon q.precision a b)
    (A (sourceChargedGaussPrepared q.epsilon q.precision c d))).trans
      (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))
  simpa only [sourceChargedGauss_unit,one_mul,mul_one] using price

def sourceQuantumChargedFieldCurrent (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (a b c d : Fin 2) (t : ℝ) : ℂ :=
  sourceQuantumChargedRead q a b c d (sourceModeGaussKernel V q pL pR t)

/-- Every full-field channel propagates with the actual left and right H; all current transitions remain. -/
theorem sourceQuantumChargedFieldCurrent_time (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (a b c d : Fin 2) (t : ℝ) :
    HasDerivAt (fun age=>sourceQuantumChargedFieldCurrent q pL pR V a b c d age)
      (sourceQuantumChargedRead q a b c d
        (-leftGenerator (sourcePhysicalMaterialPoint q pL pR)*sourceModeGaussKernel V q pL pR t+
          sourceModeGaussKernel V q pL pR t*rightGenerator (sourcePhysicalMaterialPoint q pL pR))) t := by
  let point:=sourcePhysicalMaterialPoint q pL pR
  have generated:=HasDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 289)))=>
    (rawKernel_ode point (PreparationVacuumActionFieldLift.fieldUnit j) t).const_smul (V j))
  have equation : HasDerivAt (fun age=>sourceModeGaussKernel V q pL pR age)
      (-leftGenerator point*sourceModeGaussKernel V q pL pR t+
        sourceModeGaussKernel V q pL pR t*rightGenerator point) t := by
    simp only [point,sourcePhysicalMaterialPoint,sourceMaterialTransfer,
      sourceModeGaussKernel_generated,Finset.mul_sum,Finset.sum_mul,
      Finset.sum_add_distrib,smul_add,mul_smul_comm,smul_mul_assoc] at generated ⊢
    exact generated
  have read:=((sourceQuantumChargedRead q a b c d).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t equation
  simpa only [sourceQuantumChargedFieldCurrent,ContinuousLinearMap.coe_restrictScalars',
    Function.comp_def] using read

end LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge
