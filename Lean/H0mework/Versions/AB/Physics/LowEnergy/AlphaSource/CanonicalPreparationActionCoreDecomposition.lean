import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationActionSourceComponents

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

open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumNonlinearFieldCurve
open SU7ExteriorBreakingYukawa GaussNativeEnergy StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariationDensity

def primalLocal (i b : Fin 3) (z : SourceCoordinateSlice) : SourceMatrix :=
  (GaussMatterCore.coefficient i b z:ℂ) •
    ((Complex.I • GaussCoframeSpin.primal (Fin.castAdd 4 b))*nativePrimal (connectionField z i))

theorem spatialLeft_source (z : physicalChart) (i : Fin 3) :
    leftTime z.val*coefficientMatrix i.succ (sourceCoframe z.val)=
      ∑ b : Fin 3,((GaussMatterCore.coefficient i b z.val:ℂ)*Complex.I) •
        GaussCoframeSpin.primal (Fin.castAdd 4 b) := by
  rw [leftTime_source,coefficientMatrix,spatial_gamma,map_sum]
  simp only [map_smul,Matrix.mul_smul,Matrix.mul_sum,Matrix.smul_mul,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro b _
  have lift (A : DiracMatrix) : GaussCoframeSpin.spinLift A=spinCoordinates A :=
    (GaussCoframeSpin.spinLift_source A).symm
  rw [GaussCoframeSpin.primal,lift,source_boost,map_smul,smul_smul]
  change (Complex.I*(triadInverse z.val.1 i b:ℂ)*(lapse:ℂ)) •
      (Quantum.operatorMatrix (diracMatrixMatterAction diracGammaZero)*
       Quantum.operatorMatrix (diracMatrixMatterAction (diracGamma b.succ)))=_
  rw [←Quantum.matrix_composition,←diracMatrixMatterAction_mul]
  congr 1
  simp only [GaussMatterCore.coefficient,GaussNativeEnergy.source_time_generated,
    Complex.ofReal_mul,Complex.ofReal_ofNat,Matrix.cons_val_zero]
  ring

theorem spatialConnection_source (z : physicalChart) :
    spatialConnection z.val=∑ i : Fin 3,∑ b : Fin 3,primalLocal i b z.val := by
  unfold spatialConnection
  apply Finset.sum_congr rfl
  intro i _
  rw [spatialLeft_source,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [primalLocal,Matrix.smul_mul,smul_smul]

theorem branches_add (A B : SourceMatrix) :
    SourceRealScalarFock.branches (A+B)=SourceRealScalarFock.branches A+SourceRealScalarFock.branches B := by
  ext u v
  cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.map_apply]
  abel

theorem branches_sum {ι : Type*} [Fintype ι] (A : ι→SourceMatrix) :
    SourceRealScalarFock.branches (∑ i,A i)=∑ i,SourceRealScalarFock.branches (A i) := by
  classical
  ext u v
  cases u <;> cases v <;>
    simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.sum_apply]

theorem primalLocal_branches (i b : Fin 3) (z : SourceCoordinateSlice) :
    SourceRealScalarFock.branches (primalLocal i b z)=GaussMatterCore.localMatrix i b z := by
  change SourceRealScalarFock.branches ((GaussMatterCore.coefficient i b z:ℂ) •
    ((Complex.I • GaussCoframeSpin.primal (Fin.castAdd 4 b))*nativePrimal (connectionField z i)))=
    (GaussMatterCore.coefficient i b z:ℂ) •
    ((Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b))*nativeFull (connectionField z i))
  have hb : (Fin.castAdd 4 b).val<3:=b.isLt
  simp only [GaussCoframeSpin.full,hb,if_true,nativeFull,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.smul_mul]
  rw [Matrix.fromBlocks_multiply]
  ext u v
  cases u <;> cases v <;>
    simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.smul_apply,
      Matrix.mul_apply,smul_smul] <;> ring

theorem full_source_components (z : physicalChart) (p : PhysicalMomentum) :
    fourierLinear p (stateHamiltonian (sourceState z.val))=
      GaussYukawaCoefficient.fullMatrix (scalarField z.val)+
      (∑ i : Fin 3,∑ b : Fin 3,GaussMatterCore.localMatrix i b z.val)+
      SourceRealScalarFock.branches (retainedConnection z.val)+momentumMatrix z.val p := by
  change realFourierMatrix _ p=_
  rw [realFourierMatrix,actual_hamiltonian_components,actual_hamiltonian_components,
    momentumMatrix_branches]
  have regroup (A B C D E : SourceMatrix) :
      Matrix.fromBlocks (A+B+C+D) 0 0 (-((A+B+C+E).map star))=
      SourceRealScalarFock.branches A+SourceRealScalarFock.branches B+
      SourceRealScalarFock.branches C+Matrix.fromBlocks D 0 0 (-(E.map star)) := by
    ext u v
    cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.map_apply]
    abel
  rw [regroup]
  change SourceRealScalarFock.branches _+SourceRealScalarFock.branches _+_+_=_
  rw [spatialConnection_source,branches_sum]
  simp_rw [branches_sum,primalLocal_branches]
  rfl

def actualFiber (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberMap :=
  quantizer (fourierLinear p (stateHamiltonian (sourceState z)))

theorem actualFiber_smooth (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (actualFiber p) z.val := by
  have valid:=sourceState_valid z
  have hstate : ContDiffAt ℝ ∞ stateHamiltonian (sourceState z.val) :=
    contDiffAt_pi.mpr (fun i=>stateHamiltonian_smooth _ valid.1 valid.2 i)
  exact (hamiltonianQuantizer p).contDiff.contDiffAt.comp z.val
    (hstate.comp z.val sourceState_smooth.contDiffAt)

def actualCore (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (actualFiber p) (actualFiber_smooth p)

-- This algebraic restriction is identified below with the explicit retained source connection.
def retainedCore : QuantumTest →ₗ[ℂ] QuantumTest :=
  actualCore 0-GaussYukawaOperator.originalAction-GaussMatterCore.matterAction

theorem actualFiber_components (z : physicalChart) (p : PhysicalMomentum) :
    actualFiber p z.val=GaussYukawaCoefficient.sourceMap (scalarField z.val)+
      (∑ i : Fin 3,∑ b : Fin 3,quantized (GaussMatterCore.localMatrix i b z.val))+
      quantized (SourceRealScalarFock.branches (retainedConnection z.val))+
      CanonicalGradedSpatial.sourceMomentum p z.val := by
  rw [actualFiber,full_source_components]
  simp only [map_add,map_sum]
  rfl

theorem quantized_zero : quantized (0:FullMatrix)=0 := map_zero quantizer

theorem retainedCore_source (test : QuantumTest) (z : physicalChart) :
    retainedCore test z.val=
      quantized (SourceRealScalarFock.branches (retainedConnection z.val)) (test z.val) := by
  change actualFiber 0 z.val (test z.val)-
    GaussYukawaCoefficient.sourceMap (scalarField z.val) (test z.val)-
    (GaussMatterCore.matterAction test) z.val=_
  rw [actualFiber_components]
  simp only [add_apply,sum_apply,GaussMatterCore.matterAction,LinearMap.sum_apply,
    CanonicalGradedSpatial.sourceMomentum,momentumMatrix_zero,quantized_zero,add_zero]
  change _-(∑ i : Fin 3,∑ b : Fin 3,quantized (GaussMatterCore.localMatrix i b z.val) (test z.val))=_
  abel

theorem actualCore_momentum (p : PhysicalMomentum) :
    actualCore p=actualCore 0+CanonicalGradedSpatial.sourceAction p := by
  apply LinearMap.ext
  intro test
  apply DFunLike.ext
  intro z
  change actualFiber p z (test z)=actualFiber 0 z (test z)+
    CanonicalGradedSpatial.sourceMomentum p z (test z)
  by_cases hz : z∈physicalChart
  · rw [actualFiber_components ⟨z,hz⟩ p,actualFiber_components ⟨z,hz⟩ 0]
    simp only [add_apply,CanonicalGradedSpatial.sourceMomentum,momentumMatrix_zero,
      quantized_zero,add_zero]
  · have outside : z∉tsupport test:=fun h=>hz (test.tsupport_subset h)
    rw [image_eq_zero_of_notMem_tsupport outside,map_zero,map_zero,map_zero,add_zero]

theorem physical_action_decomposition (p : PhysicalMomentum) :
    CanonicalPhysicalSpatial.physicalAction p+GaussYukawaOperator.originalAction=
      GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore := by
  rw [actualCore_momentum,retainedCore,CanonicalPhysicalSpatial.physicalAction,
    GaussDiagonalHistory.diagonalAction]
  change _+CanonicalGradedSpatial.sourceAction p+_=_
  abel

end LowEnergy.PreparationVacuumActionDecomposition
