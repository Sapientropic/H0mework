import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingPoleCurrent
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCreation
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalGradedCharge
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedState

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMovingPoleGaussReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumElectromagneticIdentity PreparationVacuumSourcePreparedState
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert GaussCoreHilbert GaussFockLift
open CanonicalPreparationCreation CanonicalGradedCharge CanonicalGradedSpatialSource
open ProofFreeRicherAnholonomicSource Stage10 Stage10.CanonicalMatter
open QuantizationCheck.Fermion YangMills.FullPairing
open scoped BigOperators InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] actualMovingPolePreparation sourcePreparation

def sourcePoleBase (epsilon : ℝ) (precision : 0<epsilon) : Base:=
  GaussHalfDensity.halfDensityEquiv 0 (sourcePreparation epsilon precision).point.val.val

theorem sourcePoleBase_unit (epsilon : ℝ) (precision : 0<epsilon) :
    ‖sourcePoleBase epsilon precision‖=1 :=by
  rw [←sourceCreated_norm,sourcePoleBase,←(sourcePreparation epsilon precision).created]
  exact (sourcePreparation epsilon precision).unit

def sourcePolePrimalCoordinates (momentum : PhysicalMomentum) (state : RestStateIndex) : Quantum.Index→ℂ:=
  Quantum.coordinates (actualMovingPolePreparation momentum state (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0)))

def sourcePoleCoordinates (momentum : PhysicalMomentum) (state : RestStateIndex) : Mode→ℂ:=
  Sum.elim (sourcePolePrimalCoordinates momentum state) (fun _=>0)

def sourcePoleFiber (momentum : PhysicalMomentum) (state : RestStateIndex) : FockFiber:=
  oneParticleFiber (sourcePoleCoordinates momentum state)

def sourcePoleCreation (momentum : PhysicalMomentum) (state : RestStateIndex) : FiberOp:=
  ∑i : Mode,sourcePoleCoordinates momentum state i • GaussCARHistory.createFiber i

theorem sourcePoleCreation_vacuum (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleCreation momentum state vacuumFiber=sourcePoleFiber momentum state :=by
  apply fiberCoordinates.injective
  simp only [sourcePoleCreation,sum_apply,smul_apply,map_sum,map_smul]
  change (∑i : Mode,sourcePoleCoordinates momentum state i •
    fiberCoordinates (SourceCARBound.createOp i vacuumFiber))=fiberCoordinates (sourcePoleFiber momentum state)
  simp only [SourceCARBound.createOp,SourceCARBound.coordinates_liftOp,vacuumFiber,sourcePoleFiber,
    oneParticleFiber,LinearEquiv.apply_symm_apply]
  simpa only [Fermion.waveCreation,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply,LinearMap.smul_apply] using
    Fermion.waveCreation_vacuum (sourcePoleCoordinates momentum state)

def sourcePolePrepared (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) (state : RestStateIndex) : H:=
  lift (sourcePoleCreation momentum state)
    (GaussHalfDensity.fockHalfDensityEquiv.symm (slot ∅ (sourcePoleBase epsilon precision)))

theorem sourcePolePrepared_coordinates (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (state : RestStateIndex) (word : Occupation) :
    GaussHalfDensity.fockHalfDensityEquiv (sourcePolePrepared epsilon precision momentum state) word=
      sourcePoleFiber momentum state word • sourcePoleBase epsilon precision :=by
  simp only [sourcePolePrepared,lift_apply,LinearIsometryEquiv.apply_symm_apply]
  rw [flatLift_apply]
  simp only [slot_apply,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold entry
  rw [←vacuumFiber_single,sourcePoleCreation_vacuum]

theorem sourcePoleFiber_gram (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    inner ℂ (sourcePoleFiber leftMomentum left) (sourcePoleFiber rightMomentum right)=
      inner ℂ (operator (actualMovingPolePreparation leftMomentum left) (YangMills.FullPairing.prepared 0))
        (operator (actualMovingPolePreparation rightMomentum right) (YangMills.FullPairing.prepared 0)) :=by
  rw [SourceQuantumFockGauge.fiber_pairing]
  simp only [sourcePoleFiber,oneParticleFiber,LinearEquiv.apply_symm_apply]
  rw [pairing_oneParticle]
  simp only [sourcePoleCoordinates,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    star_zero,mul_zero,Finset.sum_const_zero,add_zero]
  change Quantum.coordinatePair _ _=_
  rw [Quantum.coordinatePair_full,←YangMills.FullPairing.natural_inner]
  simp only [YangMills.FullPairing.prepared,operator_coordinates]

theorem sourcePolePrepared_gram (epsilon : ℝ) (precision : 0<epsilon)
    (leftMomentum rightMomentum : PhysicalMomentum) (left right : RestStateIndex) :
    inner ℂ (sourcePolePrepared epsilon precision leftMomentum left)
      (sourcePolePrepared epsilon precision rightMomentum right)=
      inner ℂ (operator (actualMovingPolePreparation leftMomentum left) (YangMills.FullPairing.prepared 0))
        (operator (actualMovingPolePreparation rightMomentum right) (YangMills.FullPairing.prepared 0)) :=by
  have base : inner ℂ (sourcePoleBase epsilon precision) (sourcePoleBase epsilon precision)=1 :=by
    rw [inner_self_eq_norm_sq_to_K,sourcePoleBase_unit]
    norm_num
  rw [←GaussHalfDensity.fockHalfDensityEquiv.inner_map_map,PiLp.inner_apply]
  simp only [sourcePolePrepared_coordinates,inner_smul_left,inner_smul_right,base,
    mul_one]
  change inner ℂ (sourcePoleFiber leftMomentum left) (sourcePoleFiber rightMomentum right)=_
  exact sourcePoleFiber_gram leftMomentum rightMomentum left right

theorem sourcePolePrepared_orthonormal (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum)
    (left right : RestStateIndex) :
    inner ℂ (sourcePolePrepared epsilon precision momentum left)
      (sourcePolePrepared epsilon precision momentum right)=if left=right then 1 else 0 :=by
  rw [sourcePolePrepared_gram]
  exact actualMovingPole_orthonormal 0 momentum left right

theorem sourcePolePrepared_unit (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) (state : RestStateIndex) :
    ‖sourcePolePrepared epsilon precision momentum state‖=1 :=by
  have gram:=sourcePolePrepared_orthonormal epsilon precision momentum state state
  simp only [ite_true] at gram
  have real:=congrArg Complex.re gram
  change RCLike.re (inner ℂ (sourcePolePrepared epsilon precision momentum state)
    (sourcePolePrepared epsilon precision momentum state))=1 at real
  rw [inner_self_eq_norm_sq] at real
  nlinarith [norm_nonneg (sourcePolePrepared epsilon precision momentum state)]

end LowEnergy.PreparationVacuumMovingPoleGaussReturn
