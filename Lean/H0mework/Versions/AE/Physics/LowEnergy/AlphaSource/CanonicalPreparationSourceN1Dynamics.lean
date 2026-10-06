import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceColorBoundaryWard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalN1WardCollapse
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

def sourceN1Projection : H→L[ℂ] H := sourceProjection+sourceExcitedProjection

theorem sourceN1Projection_idempotent : sourceN1Projection*sourceN1Projection=sourceN1Projection := by
  unfold sourceN1Projection sourceProjection sourceExcitedProjection
  simp only [mul_add,add_mul,NativeHistoryGrade.projection_product,
    ite_true,show CanonicalGradedCurrent.sourceLabel≠sourceExcitedLabel from by decide,
    show sourceExcitedLabel≠CanonicalGradedCurrent.sourceLabel from by decide,if_false,add_zero,zero_add]

theorem sourceN1Projection_source (x : H) : sourceN1Projection (sourceProjection x)=sourceProjection x := by
  have h : sourceN1Projection*sourceProjection=sourceProjection := by
    unfold sourceN1Projection sourceProjection sourceExcitedProjection
    simp only [add_mul,NativeHistoryGrade.projection_product,ite_true,
      show sourceExcitedLabel≠CanonicalGradedCurrent.sourceLabel from by decide,if_false,add_zero]
  exact congrArg (fun T : H→L[ℂ] H=>T x) h

theorem sourceN1Projection_excited (x : H) : sourceN1Projection (sourceExcitedProjection x)=sourceExcitedProjection x := by
  have h : sourceN1Projection*sourceExcitedProjection=sourceExcitedProjection := by
    unfold sourceN1Projection sourceProjection sourceExcitedProjection
    simp only [add_mul,NativeHistoryGrade.projection_product,ite_true,
      show CanonicalGradedCurrent.sourceLabel≠sourceExcitedLabel from by decide,if_false,zero_add]
  exact congrArg (fun T : H→L[ℂ] H=>T x) h

theorem actualC_sourceN1 (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute sourceN1Projection (actualC p F) :=
  (actualC_sourceProjection p F).add_left (actualC_excitedProjection p F)

theorem actualA_sourceN1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceN1Projection*actualA p F*sourceN1Projection=actualA p F*sourceN1Projection := by
  unfold sourceN1Projection
  simp only [mul_add,add_mul,actualA_sourceProjection,zero_add,
    actualA_N1G1_zero,add_zero,actualA_N1G0_range]
  rw [mul_assoc sourceExcitedProjection (actualA p F) sourceExcitedProjection,
    actualA_N1G1_zero,mul_zero,add_zero]

private theorem generator_range {B : Type*} [Ring B] (P C A : B)
    (idem : P*P=P) (blocks : Commute P C) (range : P*A*P=A*P) :
    P*(C+A)*P=(C+A)*P := by
  simp only [mul_add,add_mul]
  rw [range]
  exact congrArg (fun X=>X+A*P) (calc
    P*C*P=C*(P*P):=by rw [blocks.eq];simp only [mul_assoc]
    _=C*P:=by rw [idem])

theorem actualGenerator_sourceN1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceN1Projection*sourceHamiltonian p F*sourceN1Projection=sourceHamiltonian p F*sourceN1Projection := by
  rw [sourceHamiltonian,actualGenerator_source]
  exact generator_range _ _ _ sourceN1Projection_idempotent (actualC_sourceN1 p F) (actualA_sourceN1_range p F)

private theorem exp_range {B : Type*} [NormedRing B] [NormedAlgebra ℚ B] [CompleteSpace B]
    (P X : B) (idem : P*P=P) (range : P*X*P=X*P) :
    P*NormedSpace.exp X*P=NormedSpace.exp X*P := by
  have source : SemiconjBy P (P*X*P) X := by
    change P*(P*X*P)=X*P
    calc
      P*(P*X*P)=(P*P)*X*P:=by noncomm_ring
      _=P*X*P:=by rw [idem]
      _=X*P:=range
  have h:=source.exp_right.eq
  calc
    _=P*(NormedSpace.exp X*P):=by rw [mul_assoc]
    _=P*(P*NormedSpace.exp (P*X*P)):=by rw [←h]
    _=(P*P)*NormedSpace.exp (P*X*P):=(mul_assoc P P _).symm
    _=P*NormedSpace.exp (P*X*P):=by rw [idem]
    _=NormedSpace.exp X*P:=h

private theorem scalar_range {B : Type*} [Ring B] [Algebra ℂ B] [Algebra ℝ B]
    (P X : B) (c : ℂ) (t : ℝ) (range : P*X*P=X*P) :
    P*(t • (c • X))*P=(t • (c • X))*P := by
  simp only [mul_smul_comm,smul_mul_assoc]
  exact congrArg (fun Y : B=>t • (c • Y)) range

theorem actualTime_sourceN1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    sourceN1Projection*physicalTime p F t 0*sourceN1Projection=physicalTime p F t 0*sourceN1Projection := by
  unfold physicalTime SourceFiniteUnitary.time
  apply exp_range _ _ sourceN1Projection_idempotent
  exact scalar_range (B:=H→L[ℂ] H) _ _ (-Complex.I) t (actualGenerator_sourceN1_range p F)

end LowEnergy.PreparationVacuumPhysicalN1WardCollapse
