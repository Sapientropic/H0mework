import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceColorCoreWard

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalColorWard
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

theorem sourceRawReader_noether (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    rawReader reader p F 0=noetherReader reader p F 0 := by
  unfold rawReader noetherReader
  exact congrArg (finiteRiesz F) (funext fun i=>funext fun j=>(noetherForm_source reader p (frameTest F i) (frameTest F j)).symm)

def sourceColorRawCore : QuantumTest→ₗ[ℂ] QuantumTest :=
  (1/2 : ℝ) • (rawChargeCore 6-rawChargeCore 7)

def sourceColorWardCore (p k : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  (1/2 : ℝ) • (weightedWardCore p k 6-weightedWardCore p k 7)

private theorem half_linear_read {B D : Type*} [AddCommGroup B] [Module ℝ B]
    [AddCommGroup D] [Module ℝ D] (L : B→ₗ[ℝ] D) (x y : B) :
    (1/2 : ℝ) • (L x-L y)=L ((1/2 : ℝ) • (x-y)) := by rw [map_smul,map_sub]

theorem sourceColorReader_core (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (y : H) :
    sourceColorReader 0 F y=sourceApprox F (embed (sourceColorRawCore (sourceTestApprox F y))) := by
  have h:=congrArg (fun T : H→L[ℂ] H=>T y) (sourceColorReader_generated 0 p F)
  rw [sourceRawReader_noether,sourceRawReader_noether] at h
  change (1/2 : ℝ) • (noetherReader (temporalField 6) p F 0 y-
    noetherReader (temporalField 7) p F 0 y)=sourceColorReader 0 F y at h
  rw [temporalReader_projected_action,temporalReader_projected_action] at h
  rw [←h]
  exact half_linear_read (((sourceApprox F).toLinearMap.comp embed).restrictScalars ℝ) _ _

/-- All four original source compression/uncut defects remain before taking the actual Phi read. -/
def sourceColorWardReturn (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) : H :=
  (1/2 : ℝ) •
    ((sourceApprox q.F (embed (weightedWardCore pR (pL-pR) 6 (sourceTestApprox q.F y)))+
        leftCompressionDefect pL q.F (rawChargeCore 6 (sourceTestApprox q.F y))+
        leftUncutDefect pL q.F (rawChargeCore 6 (sourceTestApprox q.F y))-
        sourceApprox q.F (embed (rawChargeCore 6
          (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y))))-
     (sourceApprox q.F (embed (weightedWardCore pR (pL-pR) 7 (sourceTestApprox q.F y)))+
        leftCompressionDefect pL q.F (rawChargeCore 7 (sourceTestApprox q.F y))+
        leftUncutDefect pL q.F (rawChargeCore 7 (sourceTestApprox q.F y))-
        sourceApprox q.F (embed (rawChargeCore 7
          (rightCompressionDefect pR q.F y+rightUncutDefect pR q.F y)))))

def sourceColorInsertion (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) : H→L[ℂ] H :=
  sourceHamiltonian pL q.F*sourceColorReader 0 q.F-sourceColorReader 0 q.F*sourceHamiltonian pR q.F

private theorem half_commutator {B : Type*} [Ring B] [Algebra ℝ B] (L R X Y : B) :
    L*((1/2 : ℝ) • (X-Y))-((1/2 : ℝ) • (X-Y))*R=
      (1/2 : ℝ) • ((L*X-X*R)-(L*Y-Y*R)) := by
  simp only [mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul,smul_sub]
  abel

theorem sourceColorInsertion_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (y : H) :
    sourceColorInsertion q pL pR y=sourceColorWardReturn q pL pR y := by
  have left:=temporalInsertion_action_return (sourcePhysicalMaterialPoint q pL pR) 6 y
  have right:=temporalInsertion_action_return (sourcePhysicalMaterialPoint q pL pR) 7 y
  unfold noetherTimeInsertion at left right
  simp only [sourcePhysicalMaterialPoint,sourceMaterialTransfer] at left right
  have momentum : pR+(pL-pR)=pL:=by ext i;simp
  rw [momentum] at left right
  unfold sourceColorInsertion sourceColorWardReturn
  rw [←sourceColorReader_generated 0 pR q.F,sourceRawReader_noether,sourceRawReader_noether]
  rw [half_commutator (B:=H→L[ℂ] H)]
  change (1/2 : ℝ) • ((sourceHamiltonian pL q.F*noetherReader (temporalField 6) pR q.F 0-
    noetherReader (temporalField 6) pR q.F 0*sourceHamiltonian pR q.F) y-
    (sourceHamiltonian pL q.F*noetherReader (temporalField 7) pR q.F 0-
    noetherReader (temporalField 7) pR q.F 0*sourceHamiltonian pR q.F) y)=_
  exact congrArg₂ (fun x y : H=>(1/2 : ℝ) • (x-y)) left right

theorem sourceTestApprox_projection (F : GaussUnitaryHistory.Index) (g : Label) (y : H) :
    sourceTestApprox F (NativeHistoryGrade.projection g y)=
      GaussCoreLabel.project g (sourceTestApprox F y) := by
  apply embed_injective
  rw [sourceTestApprox_embed,GaussCoreLabel.embed_project,sourceTestApprox_embed]
  exact (congrArg (fun T : H→L[ℂ] H=>T y) (sourceApprox_blocks F g).symm.eq)

theorem sourcePrepared_testApprox_label (q : PhysicalResponsePoint) (p : PhysicalMomentum) (state : RestStateIndex) :
    GaussCoreLabel.project CanonicalGradedCurrent.sourceLabel
      (sourceTestApprox q.F (sourcePolePrepared q.epsilon q.precision p state))=
      sourceTestApprox q.F (sourcePolePrepared q.epsilon q.precision p state) := by
  have h:=sourceTestApprox_projection q.F CanonicalGradedCurrent.sourceLabel
    (sourcePolePrepared q.epsilon q.precision p state)
  have fixed:=sourcePolePrepared_sourceProjection q.epsilon q.precision p state
  rw [CanonicalGradedCurrent.sourceProjection] at fixed
  exact h.symm.trans (congrArg (sourceTestApprox q.F) fixed)

theorem sourcePrepared_normalCharge_zero (q : PhysicalResponsePoint) (p : PhysicalMomentum)
    (state : RestStateIndex) (a : Fin 12) :
    normalChargeCore a (sourceTestApprox q.F (sourcePolePrepared q.epsilon q.precision p state))=0 := by
  exact (congrArg (normalChargeCore a) (sourcePrepared_testApprox_label q p state)).symm.trans
    (sourceGradeZero_normalCharge_zero a _)

end LowEnergy.PreparationVacuumPhysicalColorWard
