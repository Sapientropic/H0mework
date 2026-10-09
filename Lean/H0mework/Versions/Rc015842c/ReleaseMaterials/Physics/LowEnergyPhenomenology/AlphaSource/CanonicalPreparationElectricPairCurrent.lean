import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationTemporalWardConsumer

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullElectricWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalGradedCharge
open CanonicalPhysicalWardCore
open scoped BigOperators ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

/-- The original CAR four-operator sum, on both 252-dimensional branches. -/
def pairFiber (A B : Matrix Mode Mode ℂ) : FockFiber →L[ℂ] FockFiber :=
  (fiberCoordinates.symm.toLinearMap.comp
    ((Fermion.normalProduct A B).comp fiberCoordinates.toLinearMap)).toContinuousLinearMap

theorem pairFiber_coordinates (A B : Matrix Mode Mode ℂ) (v : FockFiber) :
    fiberCoordinates (pairFiber A B v)=Fermion.normalProduct A B (fiberCoordinates v) := by
  change fiberCoordinates (fiberCoordinates.symm _)=_
  exact fiberCoordinates.apply_symm_apply _

theorem quantized_normal_order (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B=quantized (A*B)+pairFiber A B := by
  apply ContinuousLinearMap.ext
  intro v
  apply fiberCoordinates.injective
  change Fermion.quantize A (fiberCoordinates (quantized B v))=
    fiberCoordinates (quantized (A*B) v+pairFiber A B v)
  rw [map_add,pairFiber_coordinates]
  change Fermion.quantize A (Fermion.quantize B (fiberCoordinates v))=
    Fermion.quantize (A*B) (fiberCoordinates v)+Fermion.normalProduct A B (fiberCoordinates v)
  exact LinearMap.congr_fun (Fermion.quantize_normal_order A B) (fiberCoordinates v)

theorem pairFiber_sub (A B : Matrix Mode Mode ℂ) :
    pairFiber A B=quantized A*quantized B-quantized (A*B) := by
  rw [quantized_normal_order]
  abel

theorem pairFiber_weight (c : ℕ → ℂ) (A B : Matrix Mode Mode ℂ) :
    Commute (GaussFockWeights.weight c) (pairFiber A B) := by
  rw [pairFiber_sub]
  exact ((weight_commute c A).mul_right (weight_commute c B)).sub_right (weight_commute c (A*B))

/-- Smooth core realization; the theorem below identifies its original quartic coefficients. -/
def pairCurrent (k : PhysicalMomentum) (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (momentumAction k).comp (chargeAction a)-currentAction k a

theorem pairCurrent_apply (k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    pairCurrent k a f z=pairFiber (momentumMatrix z k) (chargeMatrix a) (f z) := by
  change quantized (momentumMatrix z k) (quantized (chargeMatrix a) (f z))-
    currentAction k a f z=_
  rw [CanonicalPhysicalWardCore.currentAction_apply,pairFiber_sub,momentum_charge]
  rfl

theorem full_current (k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    momentumAction k (chargeAction a f)=currentAction k a f+pairCurrent k a f := by
  simp only [pairCurrent,LinearMap.sub_apply,LinearMap.comp_apply]
  abel

theorem pairCurrent_original_words (k : PhysicalMomentum) (a : NativeLie)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    fiberCoordinates (pairCurrent k a f z)=
      (∑ i, ∑ j, ∑ u, ∑ v,
        (momentumMatrix z k i j*chargeMatrix a u v) •
          (Fermion.creation i*Fermion.creation u*Fermion.annihilation v*Fermion.annihilation j))
        (fiberCoordinates (f z)) := by
  rw [pairCurrent_apply,pairFiber_coordinates]
  rfl

theorem pairCurrent_oneParticle (k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    pairCurrent k a (GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel f)=0 := by
  change momentumAction k (chargeAction a _)-currentAction k a _=0
  rw [actual_current,sub_self]

end LowEnergy.PreparationVacuumFullElectricWard
