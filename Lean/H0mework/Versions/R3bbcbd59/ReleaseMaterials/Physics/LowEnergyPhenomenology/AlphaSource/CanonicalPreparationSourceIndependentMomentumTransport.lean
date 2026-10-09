import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationMovingNoetherPreparedContact
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceMovingCoframeFormReturn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumIndependentMomentumReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField DiracExteriorMatterAction
open FullQuantum.StateGreen PreparationVacuumSourceFieldFamily
open PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumNonlinearFieldCurve PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumFieldConstraintResponse
open ProofFreeRicherAnholonomicSource
open SourceQuantumGaugeSliceCoordinates CanonicalGradedSpatialSource
open GaussHistoryHilbert SourceQuantumFockGauge GaussCoreHilbert GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert
open scoped Topology ContDiff BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _

abbrev Mother:=YangMills.FullPairing.Mother
abbrev IndependentDual:=Module.Dual ℂ DiracExteriorMatterCarrier

def sourceDensityMother : Mother:=
  Quantum.operatorMatrix.toLinearEquiv.symm densityActionMatrix

def sourceCanonicalMomentum (base : ActionState) (chi : IndependentDual) : IndependentDual:=
  legendreDual base (chi.comp sourceDensityMother)

/-- The independent momentum stays fixed while its original density dual changes. -/
def sourceCandidateDual (base candidate : ActionState) (chi : IndependentDual) : IndependentDual:=
  densityDual candidate (sourceCanonicalMomentum base chi)

theorem sourceCandidateDual_momentum (base candidate : ActionState)
    (valid : candidate∈validStates) (chi : IndependentDual) :
    legendreDual candidate (sourceCandidateDual base candidate chi)=sourceCanonicalMomentum base chi :=
  legendreDual_density candidate valid _

theorem sourceCandidateDual_originalMomentum (base : ActionState)
    (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (connectionRows : Fin 4→SourceMatrix) (scalar : SourceMatrix)
    (valid : (C.coframe point,connectionRows,scalar)∈validStates) (chi : IndependentDual) :
    FullQuantum.normalizedMomentum C point
      (sourceCandidateDual base (C.coframe point,connectionRows,scalar) chi)=
        sourceCanonicalMomentum base chi :=by
  rw [←legendreDual_original C point connectionRows scalar]
  exact sourceCandidateDual_momentum base _ valid chi

theorem sourceCandidateDual_base (base : ActionState) (valid : base∈validStates)
    (chi : IndependentDual) : sourceCandidateDual base base chi=chi.comp sourceDensityMother :=
  densityDual_legendre base valid _

def sourceReaderMother (reader : Field289) (p : PhysicalMomentum) (candidate : ActionState) : Mother:=
  Quantum.operatorMatrix.toLinearEquiv.symm (affineMatrix (densityVariation reader candidate) p)

def sourceReaderHamiltonian (reader : Field289) (p : PhysicalMomentum) (candidate : ActionState) : Mother:=
  (inverseMomentumMother candidate).comp (sourceReaderMother reader p candidate)

def sourceMovingDensityMother (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) : Mother:=
  sourceDensityMother.comp ((momentumMother base).comp
    ((inverseMomentumMother candidate).comp (sourceReaderMother reader p candidate)))

theorem sourceCandidateDual_density (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (chi : IndependentDual) (psi : DiracExteriorMatterCarrier) :
    sourceCandidateDual base candidate chi (sourceReaderMother reader p candidate psi)=
      chi (sourceMovingDensityMother reader p base candidate psi) :=rfl

theorem sourceCanonicalMomentum_reader (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (chi : IndependentDual) (psi : DiracExteriorMatterCarrier) :
    sourceCanonicalMomentum base chi (sourceReaderHamiltonian reader p candidate psi)=
      chi (sourceMovingDensityMother reader p base candidate psi) :=rfl

private theorem source_matrix (A : SourceMatrix) :
    Quantum.operatorMatrix (Quantum.operatorMatrix.toLinearEquiv.symm A)=A:=
  Quantum.operatorMatrix.toLinearEquiv.apply_symm_apply A

private theorem transportedDensity_body (reader : Field289) (base candidate : ActionState) (i : Fin 4) :
    transportedDensity reader base candidate i=
      densityActionMatrix*inversePhase base*statePhase candidate*densityVariation reader candidate i :=by
  unfold transportedDensity rawMomentumMatrix rawMomentumInverse
  simp only [mul_assoc]
  rw [←mul_assoc densityActionInverse densityActionMatrix,
    densityAction_two_sided.2,one_mul]

theorem sourceMovingDensity_matrix (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) :
    Quantum.operatorMatrix (sourceMovingDensityMother reader p base candidate)=
      affineMatrix (transportedDensity reader base candidate) p :=by
  rw [sourceMovingDensityMother,Quantum.matrix_composition,Quantum.matrix_composition,
    Quantum.matrix_composition]
  simp only [sourceDensityMother,momentumMother,inverseMomentumMother,sourceReaderMother,source_matrix]
  simp only [affineMatrix,transportedDensity_body,mul_add,Finset.mul_sum,mul_smul_comm,mul_assoc]

theorem sourceIndependentDensity_coordinates (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (chi : IndependentDual) (psi : DiracExteriorMatterCarrier) :
    sourceCandidateDual base candidate chi (sourceReaderMother reader p candidate psi)=
      SourceRealScalarFock.complexBilinear (affineMatrix (transportedDensity reader base candidate) p)
        (Quantum.dualCoordinates chi) (Quantum.coordinates psi) :=by
  rw [sourceCandidateDual_density,Quantum.full_response,sourceMovingDensity_matrix]
  simp only [SourceRealScalarFock.complexBilinear,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

theorem sourceIndependentDensity_realBranches (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) (chi : IndependentDual) (psi : DiracExteriorMatterCarrier) :
    (∑i : Mode,∑j : Mode,
      SourceRealScalarFock.normalizedMomentum (Quantum.dualCoordinates chi) i*
      SourceRealScalarFock.branches (affineMatrix (transportedDensity reader base candidate) p) i j*
      SourceRealScalarFock.normalizedPrimal (Quantum.coordinates psi) j)=
        ((sourceCandidateDual base candidate chi (sourceReaderMother reader p candidate psi)).re:ℂ) :=by
  rw [SourceRealScalarFock.branches_original_real_bilinear,sourceIndependentDensity_coordinates]

theorem sourceIndependentDensity_rawFourier (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) :
    transportedRawSymbol reader base candidate p=
      Matrix.fromBlocks
        (Quantum.operatorMatrix (sourceMovingDensityMother reader p base candidate)) 0 0
        ((Quantum.operatorMatrix (sourceMovingDensityMother reader (-p) base candidate)).map star) :=by
  rw [transportedRawSymbol,rawFourier_blocks,sourceMovingDensity_matrix,sourceMovingDensity_matrix]

theorem sourceIndependentDensity_fullCAR (reader : Field289) (p : PhysicalMomentum)
    (base candidate : ActionState) :
    Fermion.quantize (transportedRawSymbol reader base candidate p)=
      rawPairDensity
        (Quantum.operatorMatrix (sourceMovingDensityMother reader p base candidate))
        (Quantum.operatorMatrix (sourceMovingDensityMother reader (-p) base candidate)) :=by
  rw [rawPairDensity_quantize,sourceIndependentDensity_rawFourier]

theorem sourceIndependentDensity_noetherFiber (reader : Field289) (p : PhysicalMomentum)
    (u : JointParameter) (v : FockFiber) :
    fiberCoordinates (noetherFiber reader p u v)=
      rawPairDensity
        (Quantum.operatorMatrix (sourceMovingDensityMother reader p (sourceState u.2) (ambientState u)))
        (Quantum.operatorMatrix (sourceMovingDensityMother reader (-p) (sourceState u.2) (ambientState u)))
        (fiberCoordinates v) :=by
  change Fermion.quantize (transportedRawSymbol reader (sourceState u.2) (ambientState u) p)
    (fiberCoordinates v)=_
  rw [sourceIndependentDensity_fullCAR]

theorem sourceCandidateDual_fullField (u : JointParameter) (valid : ambientState u∈validStates)
    (chi : IndependentDual) :
    legendreDual (sourceState (jointCurve u)+complement u.1 u.2)
      (sourceCandidateDual (sourceState u.2) (ambientState u) chi)=sourceCanonicalMomentum (sourceState u.2) chi :=by
  rw [←ambientState_coordinate]
  exact sourceCandidateDual_momentum _ _ valid chi

end LowEnergy.PreparationVacuumIndependentMomentumReturn
