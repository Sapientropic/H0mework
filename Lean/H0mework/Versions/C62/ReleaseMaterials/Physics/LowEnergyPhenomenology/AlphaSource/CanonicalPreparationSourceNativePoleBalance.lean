import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceAxisCompatibility
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceModeContactRead

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPoleConstraintReturn
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalConstraint114 PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalModeContact PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator
attribute [local irreducible] actualC actualA jointResolvent physicalTime sourcePoleRead
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℚ ℂ _

private theorem source_scale : ((gaugeScale/2:ℝ):ℂ)=(3/10:ℂ)*rootTwo:=by
  unfold rootTwo gaugeScale spinScale
  push_cast
  ring

private theorem insertion_continuous (q : PhysicalResponsePoint) (A : H→L[ℂ] H) :
    Continuous (fun t : ℝ=>SourceFiniteUnitary.time (actualC 0 q.F) (-t)*CanonicalPhysicalResolvent.finiteResolvent 0 q.F q.z*
      A*CanonicalPhysicalResolvent.finiteResolvent 0 q.F q.w*SourceFiniteUnitary.time (actualC 0 q.F) t):=by
  have left:=(sourceTime_continuous q.F).comp
    (continuous_const.prodMk continuous_id.neg : Continuous (fun t : ℝ=>((0:PhysicalMomentum),-t)))
  have right:=(sourceTime_continuous q.F).comp
    (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ=>((0:PhysicalMomentum),t)))
  exact (((left.mul continuous_const).mul continuous_const).mul continuous_const).mul right

private theorem native_continuous (q : PhysicalResponsePoint) : Continuous (sourceContactKernel q 0 0):=
  insertion_continuous q _
private theorem deviation_continuous (q : PhysicalResponsePoint) : Continuous (sourceDeviationKernel q 0 0):=
  insertion_continuous q _

def nativeContactWindow (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) : ℂ:=
  ∫t in (0:ℝ)..T,sourcePoleRead q.epsilon q.precision 0 0 l r (sourceContactKernel q 0 0 t)

def configurationDeviationWindow (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) : ℂ:=
  ∫t in (0:ℝ)..T,sourcePoleRead q.epsilon q.precision 0 0 l r (sourceDeviationKernel q 0 0 t)

attribute [local irreducible] sourcePoleActionEuler sourceContactKernel sourceDeviationKernel

theorem actualOriginWeight_native (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    actualOriginWeight q 0 0 l r 0 T=nativeContactWindow q l r T-configurationDeviationWindow q l r T:=by
  have point (t : ℝ) :=sourceActualMode_contact_deviation q 0 0 l r t nonrealL nonrealR
  simp only [Complex.real_smul,source_scale] at point
  have nI:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.comp (native_continuous q)).intervalIntegrable (μ:=volume) (0:ℝ) T
  have dI:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.comp (deviation_continuous q)).intervalIntegrable (μ:=volume) (0:ℝ) T
  simp only [Function.comp_def] at nI dI
  have jI:=sourcePoleActionEuler_continuous q 0 0 l r (gaugeSlot 1 0) |>.intervalIntegrable (μ:=volume) (0:ℝ) T
  have kI:=sourcePoleActionEuler_continuous q 0 0 l r (gaugeSlot 2 1) |>.intervalIntegrable (μ:=volume) (0:ℝ) T
  have integral:=congrArg (fun f : ℝ→ℂ=>∫t in (0:ℝ)..T,f t) (funext point)
  rw [intervalIntegral.integral_sub nI dI,intervalIntegral.integral_const_mul,intervalIntegral.integral_sub jI kI] at integral
  have firstSlot : gaugeSlot 1 0=(21:Fin 289):=by decide
  have secondSlot : gaugeSlot 2 1=(34:Fin 289):=by decide
  simp only [firstSlot,secondSlot] at integral
  simpa only [actualOriginWeight,actualCurrent,sourcePoleCurrentWindow,laplaceWeight,zero_mul,neg_zero,
    Complex.exp_zero,one_mul,nativeContactWindow,configurationDeviationWindow] using integral

def originWardBoundary (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) : ℂ:=
  (∫t in (0:ℝ)..T,sourceActualN1ColorWardRead q 0 0 l r t)+
  (∫t in (0:ℝ)..T,sourceConstraintCovariant q 0 0 l r 0 t)-
    (sourceConstraintCharge q 0 0 l r T-sourceConstraintCharge q 0 0 l r 0)

theorem originCosource114_actualWard (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    actualCosource q 0 0 l r 0 T 114=originWardBoundary q l r T:=by
  have source:=sourceActualCosource114_N1WardBoundary q 0 0 l r 0 0 T nonrealL nonrealR
  have spatial : PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer 0 0)=0:=by
    funext i
    simp [PreparationVacuumPhysicalFeedback.physicalSpatial,sourcePhysicalTransfer]
  simpa only [actualCosource,spatial,originWardBoundary,laplaceWeight,zero_mul,neg_zero,
    Complex.exp_zero,one_mul] using source

theorem origin_native_Ward_balance (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    nativeContactWindow q l r T-configurationDeviationWindow q l r T= -originWardBoundary q l r T:=by
  rw [←actualOriginWeight_native q l r T nonrealL nonrealR,actualOriginWeight_cosource114,
    originCosource114_actualWard q l r T nonrealL nonrealR]

theorem actualAxisField_native_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • actualAxisField q l r T κ) staticApproach
      (𝓝 (fullNativeOrigin*ᵥ
        (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*(nativeContactWindow q l r T-configurationDeviationWindow q l r T))+
         Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*(nativeContactWindow q l r T-configurationDeviationWindow q l r T))))):=by
  simpa only [actualOriginWeight_native q l r T nonrealL nonrealR] using actualAxisField_coupled_residue q l r T nonrealL nonrealR

end LowEnergy.PreparationVacuumPoleConstraintReturn
