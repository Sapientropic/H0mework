import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginPrimitiveReturn
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyPreparedWard
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceColourSymbolCovariance
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeSoftVertices

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeOriginPhaseWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage10
open FullQuantum FullSpace YangMills.FullPairing DiracExteriorMatterAction
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNormalizedFullField
open PreparationPhysicalChargedEnergyVariation PreparationPhysicalChargedHamiltonianRead
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalEnergyCurrentWardReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumSourceFieldFamily
open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumNativeLocalWard
open PreparationVacuumNativeFieldInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumVoltageGaussGreen PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization SourceQuantumScalarChart
open SourceQuantumResidualGaugeSlice GaussHistoryHilbert GaussNativeMatter CanonicalGradedSpatialSource
open FullQuantum.CoframeResponse FullQuantum.StateGreen FullQuantum.Triangular
open MeasureTheory Filter
open scoped Matrix Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

private theorem origin_direction : fieldDirection (sourceNativeOriginReal 0)=
    -stateContact (Fin.castAdd 6 (2:Fin 3)) 1 sourceVoltageActualState := by
  rw [sourceNativeOrigin_actionDirection]
  change stateVariation (Fin.castAdd 6 (2:Fin 3)) (-1) 0 sourceVoltageActualState=_
  simp [stateVariation,stateContact,neg_smul]
  funext mu
  simp only [Pi.neg_apply,neg_sub]

/-- The actual full source ray differentiates to the original color commutator. -/
theorem sourceNativeOriginHamiltonianJet (k : Fin 4) :
    sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (sourceNativeOriginReal 0)) k=
      stateHamiltonian sourceVoltageActualState k*nativePrimal (colorGenerator 2)-
        nativePrimal (colorGenerator 2)*stateHamiltonian sourceVoltageActualState k := by
  have ray (r : ℝ) :
      stateHamiltonian (sourceVoltageActualState+r • fieldDirection (sourceNativeOriginReal 0)) k=
        stateHamiltonian sourceVoltageActualState k+r •
          (stateHamiltonian sourceVoltageActualState k*nativePrimal (colorGenerator 2)-
            nativePrimal (colorGenerator 2)*stateHamiltonian sourceVoltageActualState k) := by
    rw [origin_direction,smul_neg,←neg_smul]
    rw [sourceColourHamiltonian_line]
    simp only [neg_smul,smul_sub]
    abel
  have actual:=sourceHamiltonianJetMatrix_derivative sourceVoltageActualState
    (fieldDirection (sourceNativeOriginReal 0)) (PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint) k
  have direct:=((hasDerivAt_id (0:ℝ)).smul_const
    (stateHamiltonian sourceVoltageActualState k*nativePrimal (colorGenerator 2)-
      nativePrimal (colorGenerator 2)*stateHamiltonian sourceVoltageActualState k)).const_add
        (stateHamiltonian sourceVoltageActualState k)
  simp only [one_smul] at direct
  exact actual.unique (direct.congr_of_eventuallyEq (Eventually.of_forall ray))

def sourceNativeOriginGeneratorFiber : FiberOperators:=operator sourceNativeOriginGenerator

private theorem operator_sub (A B : YangMills.FullPairing.Mother) : operator (A-B)=operator A-operator B := by
  ext v
  simp [operator]

private theorem operator_neg (A : YangMills.FullPairing.Mother) : operator (-A)= -operator A := by
  ext v
  simp [operator]

private theorem operator_id : operator (LinearMap.id : YangMills.FullPairing.Mother)=(1:FiberOperators) := by
  ext v
  simp [operator]

private theorem neg_fiber_mul (A B : FiberOperators) : (-A)*B= -(A*B) := by
  ext v
  rfl

private theorem fiber_mul_neg (A B : FiberOperators) : A*(-B)= -(A*B) := by
  apply ContinuousLinearMap.ext
  intro v
  exact map_neg A (B v)

private theorem matrix_read_source (A : YangMills.FullPairing.Mother) :
    sourceEnergyMatrixRead (Quantum.operatorMatrix A)=operator A := by
  change operator (Quantum.operatorMatrix.symm (Quantum.operatorMatrix A))=operator A
  rw [AlgEquiv.symm_apply_apply]

private theorem matrix_read_mul (A B : SourceMatrix) :
    sourceEnergyMatrixRead (A*B)=sourceEnergyMatrixRead A*sourceEnergyMatrixRead B := by
  change operator (Quantum.operatorMatrix.symm (A*B))=
    operator (Quantum.operatorMatrix.symm A)*operator (Quantum.operatorMatrix.symm B)
  rw [map_mul,operator_mul]

attribute [local irreducible] sourceNativeOriginGeneratorFiber sourceNativeOriginGenerator sourceHamiltonianFiber
  sourceEnergyMatrixRead

/-- The phase remains in the same source generator even though its full-Hamiltonian commutator cancels exactly. -/
theorem sourceNativeOriginEnergyFiber (p : PhysicalMomentum) :
    sourceEnergyMatrixRead
      (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState
        (fieldDirection (sourceNativeOriginReal 0))) p)=
      sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber p-
        sourceHamiltonianFiber p*sourceNativeOriginGeneratorFiber := by
  have matrix : affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState
      (fieldDirection (sourceNativeOriginReal 0))) p=
      affineMatrix (stateHamiltonian sourceVoltageActualState) p*nativePrimal (colorGenerator 2)-
        nativePrimal (colorGenerator 2)*affineMatrix (stateHamiltonian sourceVoltageActualState) p := by
    simp only [affineMatrix,sourceNativeOriginHamiltonianJet,add_mul,mul_add,Finset.sum_mul,
      Finset.mul_sum,smul_sub,smul_mul_assoc,mul_smul_comm,Finset.sum_sub_distrib]
    abel
  have generator : nativeMother (colorGenerator 2)=
      SU7MotherLieAlgebra.p286LieBlockEmbed (sourceColorP286Generator 2) := by
    unfold nativeMother colorGenerator
    rw [LinearEquiv.symm_apply_apply]
  have color : sourceEnergyMatrixRead (nativePrimal (colorGenerator 2))=
      operator (diracExteriorMotherLieAction
        (SU7MotherLieAlgebra.p286LieBlockEmbed (sourceColorP286Generator 2))) := by
    rw [nativePrimal_mother,generator,matrix_read_source]
  rw [matrix,map_sub,matrix_read_mul,matrix_read_mul,color,sourceActualHamiltonian_matrix,matrix_read_source]
  simp only [sourceNativeOriginGeneratorFiber,sourceNativeOriginGenerator,sourceHamiltonianFiber,
    operator_sub,operator_neg,operator_smul,operator_id]
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  simp only [neg_fiber_mul,fiber_mul_neg]
  abel

/-- Both source input legs and the complete nonselfadjoint defect are generated by the actual two Green inverses. -/
theorem sourceNativeOriginEnergyWard (p : PhysicalMomentum) :
    (Retarded.diracValue 0 p 0 1).adjoint*
      (sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber p-
        sourceHamiltonianFiber p*sourceNativeOriginGeneratorFiber)*Retarded.diracValue 0 p 0 1=
      (2*Complex.I) • ((Retarded.diracValue 0 p 0 1).adjoint*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 p 0 1)-
      Complex.I • ((Retarded.diracValue 0 p 0 1).adjoint*sourceNativeOriginGeneratorFiber*sourceEnergyTemporalInverse)-
      Complex.I • (sourceEnergyTemporalInverse.adjoint*sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 p 0 1)-
      (Retarded.diracValue 0 p 0 1).adjoint*sourceEnergyYukawaDefect*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 p 0 1 := by
  have split :
      (Retarded.diracValue 0 p 0 1).adjoint*
        (sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber p-
          sourceHamiltonianFiber p*sourceNativeOriginGeneratorFiber)*Retarded.diracValue 0 p 0 1=
      (Retarded.diracValue 0 p 0 1).adjoint*sourceNativeOriginGeneratorFiber*
        (sourceHamiltonianFiber p*Retarded.diracValue 0 p 0 1)-
      ((Retarded.diracValue 0 p 0 1).adjoint*(sourceHamiltonianFiber p).adjoint)*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 p 0 1-
      (Retarded.diracValue 0 p 0 1).adjoint*(sourceHamiltonianFiber p-(sourceHamiltonianFiber p).adjoint)*
        sourceNativeOriginGeneratorFiber*Retarded.diracValue 0 p 0 1 := by noncomm_ring
  rw [split,sourceEnergyDiracGreen_hamiltonian p 0 1 (by norm_num),
    sourceEnergyDiracGreen_dual p 0 1 (by norm_num),sourceHamiltonianFiber_dual_defect]
  simp only [Retarded.spectralParameter,Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add,
    Complex.star_def,Complex.conj_I,mul_sub,add_mul,smul_mul_assoc,mul_smul_comm,neg_smul,mul_assoc]
  simp only [neg_fiber_mul,smul_mul_assoc]
  module

/-- The original normalization of each prepared input is retained on its own external leg. -/
def sourceNativeOriginWardIntegrand (sideL edgeL sideR edgeR : Fin 2) (frequency : Position) : ℂ :=
  (2*Complex.I)*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) frequency))-
  Complex.I*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceNativeOriginGeneratorFiber (sourceEnergyTemporalInverse
      (fourier (sourceEnergyInputPacket sideR edgeR) frequency)))-
  Complex.I*inner ℂ (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideL edgeL) frequency))
    (sourceNativeOriginGeneratorFiber (fourier (sourceChargedFilteredPacket sideR edgeR) frequency))-
  inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
    (sourceEnergyYukawaDefect (sourceNativeOriginGeneratorFiber
      (fourier (sourceChargedFilteredPacket sideR edgeR) frequency)))

theorem sourceNativeOriginWard_generated (sideL edgeL sideR edgeR : Fin 2) :
    (fun frequency : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyMatrixRead
        (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState
          (fieldDirection (sourceNativeOriginReal 0))) (physicalMomentum frequency))
        (fourier (sourceChargedFilteredPacket sideR edgeR) frequency)))=ᵐ[volume]
      sourceNativeOriginWardIntegrand sideL edgeL sideR edgeR := by
  filter_upwards [sourceEnergyFiltered_fourier sideL edgeL,sourceEnergyFiltered_fourier sideR edgeR]
    with frequency left right
  have generated:=congrArg (fun A : FiberOperators=>
    inner ℂ (fourier (sourceEnergyInputPacket sideL edgeL) frequency)
      (A (fourier (sourceEnergyInputPacket sideR edgeR) frequency)))
    (sourceNativeOriginEnergyWard (physicalMomentum frequency))
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,inner_sub_right,inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right] at generated
  simp only [sourceNativeOriginEnergyFiber,sourceNativeOriginWardIntegrand,left,right]
  simpa only [sub_apply,mul_apply_eq_comp,inner_sub_right] using generated

theorem sourceNativeOriginWard_integrable (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceNativeOriginWardIntegrand sideL edgeL sideR edgeR) volume := by
  have price:=sourceChargedEnergyRead_integrable (fieldDirection (sourceNativeOriginReal 0)) 0
    sideL edgeL sideR edgeR
  simp only [sub_zero] at price
  exact price.congr (sourceNativeOriginWard_generated sideL edgeL sideR edgeR)

/-- The same actual Phi energy observation returns its source generator, both input legs and the original Yukawa defect. -/
theorem sourceNativeOriginEnergy_observableReturn (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead (fieldDirection (sourceNativeOriginReal 0)) 0 sideL edgeL sideR edgeR=
      ∫frequency : Position,sourceNativeOriginWardIntegrand sideL edgeL sideR edgeR frequency := by
  rw [sourceChargedEnergyRead_fourier]
  simp only [sub_zero]
  exact integral_congr_ae (sourceNativeOriginWard_generated sideL edgeL sideR edgeR)

open PreparationPhysicalChargedSoftObservable PreparationPhysicalScatteringFrequencyWard

theorem sourceNativeOriginEnergy_NoetherFiber (p : PhysicalMomentum) :
    sourceEnergyMatrixRead
      (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState
        (fieldDirection (sourceNativeOriginReal 0))) p)= -sourceNativeOriginCanonicalFiber 0 := by
  have coefficients (k : Fin 4) :
      sourceHamiltonianJetMatrix sourceVoltageActualState (fieldDirection (sourceNativeOriginReal 0)) k=
        if k=0 then sourceSoftFrequencyMatrix 0 else 0 := by
    rw [←sourceScatteringHamiltonianCoefficients]
    exact sourceSoftHamiltonianCoefficients 0 k
  simp only [affineMatrix,coefficients,Fin.succ_ne_zero,if_false,
    smul_zero,Finset.sum_const_zero,add_zero]
  exact sourceSoftFrequency_Noether 0

/-- The original density/current vertex and the differentiated energy use the same full 252-dimensional operator. -/
theorem sourceNativeOriginEnergy_Noether (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyRead (fieldDirection (sourceNativeOriginReal 0)) 0 sideL edgeL sideR edgeR=
      -sourceChargedQuantumRead sideL edgeL sideR edgeR
        ((sourceNativeOriginCanonicalFiber 0).compLpL 2 volume) := by
  rw [sourceChargedEnergyRead_fourier,sourceChargedQuantumRead_generated,←fourier.inner_map_map,
    GaugeGreen.constant_fourier,L2.inner_def,←integral_neg]
  apply integral_congr_ae
  filter_upwards [(sourceNativeOriginCanonicalFiber 0).coeFn_compLpL
    (fourier (sourceChargedFilteredPacket sideR edgeR))] with frequency read
  simp only [sub_zero,sourceNativeOriginEnergy_NoetherFiber,neg_apply,inner_neg_right,read]

/-- The signed source Noether strength returns through the same actual energy and both original Ward input legs. -/
theorem sourceNativeOriginWard_current (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*
      (∫frequency : Position,sourceNativeOriginWardIntegrand sideL edgeL sideR edgeR frequency)=
      -(∫x : Position,sourceNativeOriginFilteredCurrent 0 sideL edgeL sideR edgeR x) := by
  rw [←sourceNativeOriginEnergy_observableReturn,sourceNativeOriginEnergy_Noether,
    sourceNativeOriginFilteredCurrent_quantum,mul_neg]

end LowEnergy.PreparationPhysicalNativeOriginPhaseWard
