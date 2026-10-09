import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceN1Dynamics

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

theorem sourceBareResolvent_blocks (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (g : Label) (nonreal : z.im≠0) :
    Commute (NativeHistoryGrade.projection g) (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
  unfold CanonicalPhysicalResolvent.finiteResolvent FullYSourceResolventGraphSplice.resolvent
  exact PreparationVacuumYukawaTransport.inverse_commuting _ _
    (FullYSourceResolventGraphSplice.resolvent_isUnit _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z nonreal)
    ((CanonicalPhysicalSpatial.compression_blocks p F g).sub_right ((Commute.one_right _).smul_right z))

private theorem return_range {B : Type*} [Ring B] (L P R A : B)
    (LP : L*P=P) (LR : Commute L R) (PR : Commute P R) (LAP : L*A*P=A*P) :
    L*(R-R*A*R)*P=(R-R*A*R)*P := by
  have base : L*R*P=R*P := by rw [LR.eq,mul_assoc,LP]
  have raised : L*R*A*R*P=R*A*R*P := by
    calc
      _=R*(L*A)*(R*P):=by noncomm_ring [LR.eq]
      _=R*(L*A)*(P*R):=by rw [PR.eq]
      _=R*(L*A*P)*R:=by noncomm_ring
      _=R*(A*P)*R:=by rw [LAP]
      _=R*A*R*P:=by noncomm_ring [PR.eq]
  calc
    _=L*R*P-L*R*A*R*P:=by noncomm_ring
    _=R*P-R*A*R*P:=by rw [base,raised]
    _=_:=by noncomm_ring

private theorem sourceN1_sourceProduct : sourceN1Projection*sourceProjection=sourceProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact sourceN1Projection_source x

private theorem sourceN1_excitedProduct : sourceN1Projection*sourceExcitedProjection=sourceExcitedProjection := by
  apply ContinuousLinearMap.ext
  intro x
  exact sourceN1Projection_excited x

theorem actualResolvent_sourceN1_range (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    sourceN1Projection*jointResolvent p F z 0*sourceProjection=jointResolvent p F z 0*sourceProjection := by
  have h0 : Commute sourceProjection (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
    simpa only [sourceProjection] using sourceBareResolvent_blocks p F z CanonicalGradedCurrent.sourceLabel nonreal
  have h1 : Commute sourceExcitedProjection (CanonicalPhysicalResolvent.finiteResolvent p F z) := by
    simpa only [sourceExcitedProjection] using sourceBareResolvent_blocks p F z sourceExcitedLabel nonreal
  have raised : sourceN1Projection*actualA p F*sourceProjection=actualA p F*sourceProjection := by
    calc
      _=sourceN1Projection*(actualA p F*sourceProjection):=mul_assoc _ _ _
      _=sourceN1Projection*(sourceExcitedProjection*actualA p F*sourceProjection):=
        congrArg (fun X : H→L[ℂ] H=>sourceN1Projection*X) (actualA_N1G0_range p F).symm
      _=(sourceN1Projection*sourceExcitedProjection)*actualA p F*sourceProjection:=by simp only [mul_assoc]
      _=actualA p F*sourceProjection:=by rw [sourceN1_excitedProduct,actualA_N1G0_range]
  rw [mul_assoc,actual_resolvent_N1G0_return p F z nonreal,←mul_assoc]
  rw [return_range _ _ _ _ sourceN1_sourceProduct (h0.add_left h1) h0 raised,
    ←actual_resolvent_N1G0_return p F z nonreal]

private theorem apply_range {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P T : E→L[ℂ] E) (range : P*T*P=T*P) (x : E) (fixed : P x=x) : P (T x)=T x := by
  have h:=congrArg (fun A : E→L[ℂ] E=>A x) range
  simpa only [mul_apply_eq_comp,fixed] using h

def sourceActualN1Primal (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) : H :=
  jointResolvent p q.F z 0 (physicalTime p q.F t 0 (sourcePolePrepared q.epsilon q.precision p state))

theorem sourceActualN1Primal_generated (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceN1Projection (sourceActualN1Primal q p state z t)=sourceActualN1Primal q p state z t := by
  let phi:=sourcePolePrepared q.epsilon q.precision p state
  have phiFixed : sourceProjection phi=phi:=sourcePolePrepared_sourceProjection q.epsilon q.precision p state
  have rFixed : sourceN1Projection (jointResolvent p q.F z 0 phi)=jointResolvent p q.F z 0 phi := by
    have h:=congrArg (fun A : H→L[ℂ] H=>A phi) (actualResolvent_sourceN1_range p q.F z nonreal)
    simpa only [mul_apply_eq_comp,phiFixed] using h
  have commute : Commute (jointResolvent p q.F z 0) (physicalTime p q.F t 0) := by
    simpa only [physicalTime,sourceHamiltonian] using
      SourceFiniteUnitary.time_commutes _ _ (sourceResolvent_commutes p q.F z nonreal) t
  have same : sourceActualN1Primal q p state z t=
      physicalTime p q.F t 0 (jointResolvent p q.F z 0 phi) :=
    congrArg (fun A : H→L[ℂ] H=>A phi) commute.eq
  rw [same]
  exact apply_range _ _ (actualTime_sourceN1_range p q.F t) _ rFixed

theorem sourceActualN1Primal_core (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel (sourceTestApprox q.F (sourceActualN1Primal q p state z t))+
      GaussCoreLabel.project sourceExcitedLabel (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
        sourceTestApprox q.F (sourceActualN1Primal q p state z t) := by
  have fixed:=sourceActualN1Primal_generated q p state z t nonreal
  have h:=congrArg (sourceTestApprox q.F) fixed
  unfold sourceN1Projection at h
  rw [add_apply,sourceTestApprox_add] at h
  simp only [sourceProjection,sourceExcitedProjection,sourceTestApprox_projection] at h
  exact h

theorem sourceActualN1Primal_normalCharge_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (a : Fin 12) :
    normalChargeCore a (sourceTestApprox q.F (sourceActualN1Primal q p state z t))=0 := by
  have fixed:=sourceActualN1Primal_core q p state z t nonreal
  have h:=congrArg (normalChargeCore a) fixed
  simp only [map_add,sourceGradeZero_normalCharge_zero,sourceGradeOne_normalCharge_zero,zero_add] at h
  exact h.symm

end LowEnergy.PreparationVacuumPhysicalN1WardCollapse
