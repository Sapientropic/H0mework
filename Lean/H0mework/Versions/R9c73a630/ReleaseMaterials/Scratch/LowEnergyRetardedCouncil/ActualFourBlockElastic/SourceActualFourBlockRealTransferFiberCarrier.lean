import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferReader
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualFourBlockHilbertOperator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open QuantizationCheck.Fermion ActualFourBlockSource ActualFourBlockDetector
open MixedSpectatorPairedSourceFrame
open scoped BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := SourceRealScalarFock.branchOrder.toDecidableEq

attribute [local irreducible] MixedSpectatorContactExchange.contactCoefficient
  MixedSpectatorCanonical79Exchange.canonicalCoefficient MixedSpectatorDual24Exchange.dualCoefficient
  MixedSpectatorScalar61Exchange.greenCoefficient MixedSpectatorContactVertices.sourceVertex
  MixedSpectatorScalar61Exchange.sourceVertex LowEnergy.Fermion.normalProduct

/-- A linear lift of the original full occupation action, before any response compression. -/
def fiberLift : Module.End ℂ (Fock Mode) →ₗ[ℂ] (FockFiber →L[ℂ] FockFiber) where
  toFun T := LinearMap.toContinuousLinearMap (SourceCARBound.liftOp T)
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro v
    apply fiberCoordinates.injective
    change fiberCoordinates (SourceCARBound.liftOp (T+S) v) =
      fiberCoordinates (SourceCARBound.liftOp T v + SourceCARBound.liftOp S v)
    simp only [map_add,SourceCARBound.coordinates_liftOp,LinearMap.add_apply]
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro v
    apply fiberCoordinates.injective
    change fiberCoordinates (SourceCARBound.liftOp (c • T) v) =
      fiberCoordinates (c • SourceCARBound.liftOp T v)
    simp only [map_smul,SourceCARBound.coordinates_liftOp,LinearMap.smul_apply]

def axialTree (x : ℂ) : Module.End ℂ (Fock Mode) :=
  (∑a : Fin 97,∑b : Fin 97,
    ((-1/2 : ℂ)*MixedSpectatorContactExchange.contactCoefficient (worldTransfer x 0) a b) •
      LowEnergy.Fermion.normalProduct (MixedSpectatorContactVertices.sourceVertex 0 a)
        (MixedSpectatorContactVertices.sourceVertex 0 b)) +
  (∑a : Fin 97,∑b : Fin 97,
    ((-1/2 : ℂ)*MixedSpectatorCanonical79Exchange.canonicalCoefficient x 0 a b) •
      LowEnergy.Fermion.normalProduct (MixedSpectatorContactVertices.sourceVertex 0 a)
        (MixedSpectatorContactVertices.sourceVertex 0 b)) +
  (∑a : Fin 97,∑b : Fin 97,
    ((-1/2 : ℂ)*MixedSpectatorDual24Exchange.dualCoefficient x 0 a b) •
      LowEnergy.Fermion.normalProduct (MixedSpectatorContactVertices.sourceVertex 0 a)
        (MixedSpectatorContactVertices.sourceVertex 0 b)) +
  (∑a : Fin 70,∑b : Fin 70,
    ((-1/2 : ℂ)*MixedSpectatorScalar61Exchange.greenCoefficient (worldTransfer x 0) a b) •
      LowEnergy.Fermion.normalProduct (MixedSpectatorScalar61Exchange.sourceVertex a)
        (MixedSpectatorScalar61Exchange.sourceVertex b))

def axialFiber (x : ℂ) : FockFiber →L[ℂ] FockFiber := fiberLift (axialTree x)

theorem actual_axial_fiber (x : ℂ)
    (hC : MixedSpectatorCanonical79Exchange.RegularMomentum x 0)
    (hD : MixedSpectatorDual24Exchange.RegularMomentum x 0)
    (hS : MixedSpectatorScalar61Exchange.denominator (worldTransfer x 0) ≠ 0) :
    coherentFiber (axialKinematics x hC hD hS) = axialFiber x := by
  have hl (p : Kinematics) : coherentFiber p = fiberLift (coherentTree p) := by
    change (∑b : Fin 4,fiberLift (block p b)) = fiberLift (∑b : Fin 4,block p b)
    exact (map_sum fiberLift _ _).symm
  rw [hl]
  apply congrArg fiberLift
  rw [coherentTree,Fin.sum_univ_four]
  unfold block
  dsimp only [axialKinematics]
  have h3 : (3 : Fin 4) = (2 : Fin 3).succ := rfl
  rw [h3]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Fin.succ_zero_eq_one]
  unfold MixedSpectatorContactExchange.actualContactTree
    MixedSpectatorCanonical79Exchange.actualCanonicalTree
    MixedSpectatorDual24Exchange.actualDualTree MixedSpectatorScalar61Exchange.actualScalar61Tree
    axialTree
  simp only

end LowEnergy.ActualFourBlockRealTransfer
