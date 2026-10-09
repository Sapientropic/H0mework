import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceConstrainedCurrentResponse
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingPoleCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCurrentLaplaceReturn
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open PreparationVacuumElectromagneticIdentity CanonicalGradedSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumCurrentSignalRealization
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumCurrentConstrainedInverse PreparationVacuumMixedFieldReturn
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open PreparationVacuumOriginalGreenFeedback
open scoped BigOperators ContDiff Topology Matrix
attribute [local irreducible] nativeHessian originalJacobi sourceDressedField sourceDressedGreen
  sourceMovingGaugeVertex actualMovingNativeForcing

def sourcePhysicalTransfer (leftMomentum rightMomentum : PhysicalMomentum) : PhysicalMomentum:=
  rightMomentum-leftMomentum

def sourcePhysicalClock (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) : ℂ:=
  -Complex.I*((sourceMovingPoleEnergy rightMomentum right-sourceMovingPoleEnergy leftMomentum left:ℝ):ℂ)

def sourcePhysicalFourier (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) : Fin 4→ℂ:=
  fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourcePhysicalTransfer leftMomentum rightMomentum))
    (sourcePhysicalClock leftMomentum rightMomentum left right)

theorem sourcePhysicalClock_re (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    (sourcePhysicalClock leftMomentum rightMomentum left right).re=0 :=by
  simp [sourcePhysicalClock]

theorem sourcePhysicalClock_growth (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    sourceClockGrowth (sourcePhysicalFourier leftMomentum rightMomentum left right)=0 :=by
  simp only [sourceClockGrowth,sourcePhysicalFourier,fullMomentum,Fin.cases_zero,sourcePhysicalClock_re,max_self]

private theorem sourceMovingWaveArgument_actual (momentum : PhysicalMomentum) (state : RestStateIndex) (point : BasePoint) :
    sourceMovingWaveArgument momentum state point=
      (∑axis : Fin 3,momentum axis*point axis.succ)-sourceMovingPoleEnergy momentum state*point 0 :=by
  simp [sourceMovingWaveArgument,smul_eq_mul]

theorem sourcePhysicalPhase_generated (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (point : BasePoint) :
    sourcePhase (sourcePhysicalFourier leftMomentum rightMomentum left right) point=
      ((sourceMovingWaveArgument rightMomentum right point-sourceMovingWaveArgument leftMomentum left point:ℝ):ℂ)*Complex.I :=by
  rw [sourcePhase_apply,Fin.sum_univ_succ]
  simp only [sourcePhysicalFourier,fullMomentum,Fin.cases_zero,Fin.cases_succ,sourcePhysicalTransfer,
    PreparationVacuumPhysicalFeedback.physicalSpatial,sourcePhysicalClock,Pi.sub_apply,
    sourceMovingWaveArgument_actual]
  push_cast
  simp_rw [mul_sub,sub_mul]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  ring

theorem sourceMovingPairPhase_generated (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (point : BasePoint) :
    star (sourceMovingWavePhase leftMomentum left point)*sourceMovingWavePhase rightMomentum right point=
      Complex.exp (sourcePhase (sourcePhysicalFourier leftMomentum rightMomentum left right) point) :=by
  rw [sourceMovingWavePhase,sourceMovingWavePhase,Complex.star_def,←Complex.exp_conj,←Complex.exp_add,
    sourcePhysicalPhase_generated]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

def sourcePhysicalCurrentAmplitude (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    SignalAmplitude:=actualMovingNativeForcing 0 leftMomentum rightMomentum left right

theorem sourceMovingWaveForcing_signal (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (point : BasePoint) :
    sourceMovingWaveForcing point leftMomentum rightMomentum left right=
      sourceSignalAmplitude (sourcePhysicalFourier leftMomentum rightMomentum left right)
        (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right) point :=by
  funext i
  rw [sourceMovingWaveForcing,sourceMovingPairPhase_generated]
  rfl

theorem sourceMovingWaveForcing_real (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (point : BasePoint) :
    (fun i=>(sourceMovingWaveForcing point leftMomentum rightMomentum left right i).re)=
      sourceRealSignal (sourcePhysicalFourier leftMomentum rightMomentum left right)
        (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right) point :=by
  rw [sourceMovingWaveForcing_signal]
  rfl

theorem sourceMovingWaveForcing_secondQuadrature (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (point : BasePoint) :
    (fun i=>(sourceMovingWaveForcing point leftMomentum rightMomentum left right i).im)=
      sourceRealSignal (sourcePhysicalFourier leftMomentum rightMomentum left right)
        (sourceQuadrature (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right)) point :=by
  rw [sourceSignal_quadrature,sourceMovingWaveForcing_signal]

theorem sourceMovingWaveForcing_initial (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    sourceMovingWaveForcing 0 leftMomentum rightMomentum left right=
      sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right :=by
  rw [sourceMovingWaveForcing_signal]
  funext i
  simp only [sourceSignalAmplitude,map_zero,Complex.exp_zero,one_mul]

theorem sourcePhysicalCurrent_nativeJets (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (point : BasePoint) :
    signalSecondJet (fun point=>fun i=>(sourceMovingWaveForcing point leftMomentum rightMomentum left right i).re) point=
      sourceRealSecondJet (sourcePhysicalFourier leftMomentum rightMomentum left right)
        (sourceMovingWaveForcing point leftMomentum rightMomentum left right) :=by
  have whole : (fun point=>fun i=>(sourceMovingWaveForcing point leftMomentum rightMomentum left right i).re)=
      sourceRealSignal (sourcePhysicalFourier leftMomentum rightMomentum left right)
        (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right) :=by
    funext point
    exact sourceMovingWaveForcing_real leftMomentum rightMomentum left right point
  rw [whole,sourceRealSignal_secondJet,←sourceMovingWaveForcing_signal]

end LowEnergy.PreparationVacuumPhysicalCurrentLaplaceReturn
