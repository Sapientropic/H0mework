import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalCurrentResponse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleLegDynamics
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumCurrentSignalRealization PreparationVacuumCurrentSignalOperator
open scoped BigOperators Topology Matrix

def sourceMaterialTransfer (leftMomentum rightMomentum : PhysicalMomentum) : PhysicalMomentum:=
  leftMomentum-rightMomentum

theorem sourceMaterialTransfer_current (leftMomentum rightMomentum : PhysicalMomentum) :
    sourceMaterialTransfer leftMomentum rightMomentum= -sourcePhysicalTransfer leftMomentum rightMomentum :=by
  funext axis
  simp only [sourceMaterialTransfer,sourcePhysicalTransfer,Pi.sub_apply,Pi.neg_apply]
  ring

def sourcePhysicalMaterialPoint (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum) :
    PhysicalResponsePoint:={q with p:=rightMomentum,k:=sourceMaterialTransfer leftMomentum rightMomentum}

theorem sourcePhysicalMaterialPoint_right (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum) :
    (sourcePhysicalMaterialPoint q leftMomentum rightMomentum).p=rightMomentum :=rfl

theorem sourcePhysicalMaterialPoint_left (q : PhysicalResponsePoint) (leftMomentum rightMomentum : PhysicalMomentum) :
    (sourcePhysicalMaterialPoint q leftMomentum rightMomentum).p+
      (sourcePhysicalMaterialPoint q leftMomentum rightMomentum).k=leftMomentum :=by
  funext axis
  simp only [sourcePhysicalMaterialPoint,sourceMaterialTransfer,Pi.add_apply,Pi.sub_apply]
  ring

/-- The test-field mode is the restriction opposite to the already generated source current mode. -/
def sourcePhysicalTestFourier (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) : Fin 4→ℂ:=
  -(sourcePhysicalFourier leftMomentum rightMomentum left right)

theorem sourcePhysicalTestFourier_material (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    sourcePhysicalTestFourier leftMomentum rightMomentum left right=
      fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial (sourceMaterialTransfer leftMomentum rightMomentum))
        (-sourcePhysicalClock leftMomentum rightMomentum left right) :=by
  funext mu
  refine Fin.cases ?_ (fun axis=>?_) mu
  · rfl
  · simp only [sourcePhysicalTestFourier,sourcePhysicalFourier,fullMomentum,Fin.cases_succ,Pi.neg_apply,
      PreparationVacuumPhysicalFeedback.physicalSpatial,sourceMaterialTransfer,sourcePhysicalTransfer,Pi.sub_apply]
    push_cast
    ring

private theorem sourcePhase_neg (p : Fin 4→ℂ) (point : BasePoint) : sourcePhase (-p) point= -sourcePhase p point :=by
  simp only [sourcePhase_apply,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]

theorem sourcePhysicalCurrent_test_pair (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (a : SignalAmplitude) (point : BasePoint) :
    (∑i : Fin 289,sourceMovingWaveForcing point leftMomentum rightMomentum left right i*
      sourceSignalAmplitude (sourcePhysicalTestFourier leftMomentum rightMomentum left right) a point i)=
      sourcePhysicalCurrentRead leftMomentum rightMomentum left right a :=by
  rw [sourceMovingWaveForcing_signal]
  unfold sourceSignalAmplitude sourcePhysicalCurrentRead sourcePhysicalTestFourier
  rw [sourcePhase_neg]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=(Complex.exp (sourcePhase (sourcePhysicalFourier leftMomentum rightMomentum left right) point)*
      Complex.exp (-sourcePhase (sourcePhysicalFourier leftMomentum rightMomentum left right) point))*
        (sourcePhysicalCurrentAmplitude leftMomentum rightMomentum left right i*a i) :=by ring
    _=_ :=by rw [←Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]

theorem sourcePhysicalCurrent_test_native (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex)
    (a : SignalAmplitude) (point : BasePoint) :
    sourceNativeGaugeCurrentComplex point (sourceMovingWavePairPoint point leftMomentum rightMomentum left right)
        (sourceRealSignal (sourcePhysicalTestFourier leftMomentum rightMomentum left right) a point)+
      Complex.I*sourceNativeGaugeCurrentComplex point (sourceMovingWavePairPoint point leftMomentum rightMomentum left right)
        (sourceRealSignal (sourcePhysicalTestFourier leftMomentum rightMomentum left right) (sourceQuadrature a) point)=
      sourcePhysicalCurrentRead leftMomentum rightMomentum left right a :=by
  rw [←sourceMovingWaveForcing_generated,←sourceMovingWaveForcing_generated,sourceSignal_quadrature]
  change (∑i : Fin 289,((sourceSignalAmplitude (sourcePhysicalTestFourier leftMomentum rightMomentum left right) a point i).re:ℂ)*
      sourceMovingWaveForcing point leftMomentum rightMomentum left right i)+
    Complex.I*(∑i : Fin 289,((sourceSignalAmplitude (sourcePhysicalTestFourier leftMomentum rightMomentum left right) a point i).im:ℂ)*
      sourceMovingWaveForcing point leftMomentum rightMomentum left right i)=_
  rw [Finset.mul_sum,←Finset.sum_add_distrib,←sourcePhysicalCurrent_test_pair leftMomentum rightMomentum left right a point]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=sourceMovingWaveForcing point leftMomentum rightMomentum left right i*
      (((sourceSignalAmplitude (sourcePhysicalTestFourier leftMomentum rightMomentum left right) a point i).re:ℂ)+
        ((sourceSignalAmplitude (sourcePhysicalTestFourier leftMomentum rightMomentum left right) a point i).im:ℂ)*Complex.I) :=by ring
    _=_ :=by rw [Complex.re_add_im]

end LowEnergy.PreparationVacuumPhysicalPoleLegDynamics
