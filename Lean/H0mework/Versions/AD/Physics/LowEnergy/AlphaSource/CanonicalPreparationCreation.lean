import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparedGraph
import H0mework.Physics.LowEnergyFermion.TwoParticle

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPreparationCreation
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open LowEnergy.GaussCoreHilbert LowEnergy.GaussFockLift
open scoped BigOperators
attribute [local instance] SourceRealScalarFock.branchOrder

def sourceCreation : FiberOp :=
  ∑ i : Mode, LowEnergy.CanonicalCompletedSector.seedCoordinates i •
    LowEnergy.GaussCARHistory.createFiber i

def vacuumFiber : FockFiber := fiberCoordinates.symm QuantizationCheck.Fermion.vacuum

theorem sourceCreation_vacuum :
    sourceCreation vacuumFiber = LowEnergy.CanonicalCompletedSector.seed := by
  apply fiberCoordinates.injective
  simp only [sourceCreation, sum_apply, smul_apply,
    map_sum, map_smul]
  change (∑ i : Mode, LowEnergy.CanonicalCompletedSector.seedCoordinates i •
    fiberCoordinates (LowEnergy.SourceCARBound.createOp i vacuumFiber)) =
      fiberCoordinates LowEnergy.CanonicalCompletedSector.seed
  simp only [LowEnergy.SourceCARBound.createOp, LowEnergy.SourceCARBound.coordinates_liftOp,
    vacuumFiber, LowEnergy.CanonicalCompletedSector.seed, LinearEquiv.apply_symm_apply]
  simpa only [LowEnergy.Fermion.waveCreation, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.sum_apply, LinearMap.smul_apply] using
    LowEnergy.Fermion.waveCreation_vacuum LowEnergy.CanonicalCompletedSector.seedCoordinates

theorem vacuumFiber_single : vacuumFiber = EuclideanSpace.single (∅ : Occupation) 1 := by
  apply PiLp.ext
  intro word
  simp [vacuumFiber, fiberCoordinates, QuantizationCheck.Fermion.vacuum,
    QuantizationCheck.Fermion.occupationBasis, EuclideanSpace.single]

def sourceCreated (f : Base) : H :=
  lift sourceCreation
    (LowEnergy.GaussHalfDensity.fockHalfDensityEquiv.symm (slot ∅ f))

theorem sourceCreated_coordinates (f : Base) (word : Occupation) :
    LowEnergy.GaussHalfDensity.fockHalfDensityEquiv (sourceCreated f) word =
      LowEnergy.CanonicalCompletedSector.seed word • f := by
  simp only [sourceCreated, lift_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [flatLift_apply]
  simp only [slot_apply, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold entry
  rw [← vacuumFiber_single, sourceCreation_vacuum]

theorem sourceCreated_norm (f : Base) : ‖sourceCreated f‖ = ‖f‖ := by
  have square : ‖sourceCreated f‖^2 = ‖f‖^2 := by
    rw [← LowEnergy.GaussHalfDensity.fockHalfDensityEquiv.norm_map,
      PiLp.norm_sq_eq_of_L2]
    simp only [sourceCreated_coordinates, norm_smul, mul_pow, ← Finset.sum_mul]
    rw [← PiLp.norm_sq_eq_of_L2, LowEnergy.GaussComposite.SourceGraph.seed_unit]
    norm_num
  nlinarith [norm_nonneg (sourceCreated f), norm_nonneg f]

theorem sourceCreated_unit_iff (f : Base) : ‖sourceCreated f‖ = 1 ↔ ‖f‖ = 1 := by
  rw [sourceCreated_norm]

end LowEnergy.CanonicalPreparationCreation
