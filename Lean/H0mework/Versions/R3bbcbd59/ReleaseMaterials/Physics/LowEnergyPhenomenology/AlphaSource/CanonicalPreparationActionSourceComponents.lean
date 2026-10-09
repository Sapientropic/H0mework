import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNonlinearPreparedReader

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActionDecomposition
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeVariation
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

open GaussNativePotential GaussNativeMatter
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift

-- All components below read the same emitted action, including its retained spin connection.
def leftTime (z : SourceCoordinateSlice) : SourceMatrix :=
  (-Complex.I) • Ring.inverse (principalMatrix (sourceCoframe z))

def spinConnection (mu : Fin 4) : SourceMatrix :=
  Quantum.operatorMatrix (diracMatrixMatterAction
    (diracSpinConnectionLift (actual.gravityConnection 0) mu))

def spatialConnection (z : SourceCoordinateSlice) : SourceMatrix :=
  ∑ i : Fin 3, leftTime z*coefficientMatrix i.succ (sourceCoframe z)*
    nativePrimal (connectionField z i)

def retainedConnection (z : SourceCoordinateSlice) : SourceMatrix :=
  leftTime z*coefficientMatrix 0 (sourceCoframe z)*familyConnection z 0+
    ∑ i : Fin 3,leftTime z*coefficientMatrix i.succ (sourceCoframe z)*spinConnection i.succ

def scalarComponent (z : SourceCoordinateSlice) : SourceMatrix := leftTime z*familyScalar z

theorem connection_spatial (z : SourceCoordinateSlice) (i : Fin 3) :
    familyConnection z i.succ=spinConnection i.succ+nativePrimal (connectionField z i) := by
  change Quantum.operatorMatrix (_+_)=_+_
  rw [map_add]
  rfl

theorem source_affine_hamiltonian (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    affineMatrix (stateHamiltonian (sourceState z)) p=familyHamiltonian z (sourceCoframe z) p := by
  simp only [affineMatrix,stateHamiltonian,sourceState,Fin.cases_zero,Fin.cases_succ,
    familyHamiltonian,familyLower,stateLower,timeSymbol,Matrix.mul_add,Matrix.mul_sum,
    Matrix.mul_smul,smul_add,Finset.smul_sum,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [←mul_assoc,neg_mul,Complex.I_mul_I]
  simp

theorem source_zero_components (z : SourceCoordinateSlice) :
    stateHamiltonian (sourceState z) 0=
      scalarComponent z+spatialConnection z+retainedConnection z := by
  simp only [stateHamiltonian,sourceState,Fin.cases_zero,stateLower,timeSymbol,
    Fin.sum_univ_succ,connection_spatial,Matrix.mul_add,Matrix.mul_sum,smul_add,
    Finset.smul_sum,scalarComponent,spatialConnection,retainedConnection,leftTime,
    Matrix.smul_mul,Matrix.mul_assoc,Finset.sum_add_distrib]
  abel

theorem leftTime_source (z : physicalChart) :
    leftTime z.val=(lapse:ℂ) • Quantum.operatorMatrix (diracMatrixMatterAction diracGammaZero) := by
  rw [leftTime,principal_inverse_original _ (temporal_noncharacteristic z),temporal_inverse]
  rw [map_smul,smul_smul]
  congr 1
  calc
    (-Complex.I)*((lapse:ℂ)*Complex.I)=-(Complex.I*Complex.I)*(lapse:ℂ) := by ring
    _ = _ := by rw [Complex.I_mul_I]; simp

theorem scalar_yukawa (z : physicalChart) :
    scalarComponent z.val=GaussYukawaCoefficient.primal (scalarField z.val) := by
  change scalarComponent z.val=Quantum.operatorMatrix (FullQuantum.yukawaHamiltonian _)
  rw [scalarComponent,leftTime_source]
  simp only [FullQuantum.yukawaHamiltonian,map_smul,
    Quantum.matrix_composition,Matrix.smul_mul,familyScalar]

theorem actual_hamiltonian_components (z : physicalChart) (p : PhysicalMomentum) :
    affineMatrix (stateHamiltonian (sourceState z.val)) p=
      GaussYukawaCoefficient.primal (scalarField z.val)+spatialConnection z.val+
      retainedConnection z.val+primalMatrix z.val p := by
  rw [source_affine_hamiltonian,familyHamiltonian_original]
  have spatial:=hamiltonian_source_principal (emitter z.val) 0 z rfl p
  have hs:=congrArg Quantum.operatorMatrix (sub_eq_iff_eq_add.mp spatial)
  rw [map_add] at hs
  have hz:=source_zero_components z.val
  rw [scalar_yukawa z] at hz
  have hzero:=familyHamiltonian_original z 0
  have ha:=source_affine_hamiltonian z.val 0
  simp only [affineMatrix,Pi.zero_apply,Complex.ofReal_zero,zero_smul,
    Finset.sum_const_zero,add_zero] at ha
  rw [←hzero,←ha,hz] at hs
  exact hs.trans (by unfold CanonicalGradedSpatialSource.primalMatrix; abel)

end LowEnergy.PreparationVacuumActionDecomposition
