import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutCoulomb
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.SourceRetainerMomentum
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeCoulombIR
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTransferCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUncutMoving
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullFieldRiesz PreparationVacuumFullOriginResponse
open ActualWholeStatic ActualEMCarrierOwn MeasureTheory Filter Set
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldCovector
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard ActualDressedActionPhase
open PhysicalEMTransferCurrent PhysicalEMTransferResolver CanonicalPhysicalYResolvent
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap InnerProductSpace
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩

attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull sourceDressedResponse currentVertex

open ActualDressedFullCoulomb ActualDressedUncutCurrent

open PreparationVacuumTemporalCharge PreparationVacuumJointFieldResponse
open ActualDressedCofinal ActualDressedReaderComponents ActualDressedTemporalCurrent ActualDressedNoether

open ActualDressedUncutCoulomb PreparationVacuumFullPoleContinuation

private theorem sandwich_continuous (T : (H→L[ℂ]H)→L[ℂ]ℂ) (J R : H→L[ℂ]H)
    (L : PhysicalMomentum→H→L[ℂ]H) (continuousL : Continuous L) :
    Continuous (fun k=> -T (L k*J*R)) :=
  (T.continuous.comp ((continuousL.mul continuous_const).mul continuous_const)).neg

/-- Original uncut inverse continuity transports the same full289 actual creation/background current. -/
theorem dressed_uncut_current_continuous (event : DressedEvent) : Continuous (dressedUncutCurrent event) := by
  apply continuous_pi
  intro i
  exact sandwich_continuous (dressedEulerObserver event)
    (currentRestriction (fieldBasis i) event.momentum event.frame 0)
    (jointResolvent event.momentum event.frame event.energy 0)
    (fun k=>jointResolvent (event.momentum+ -k) event.frame event.energy 0)
    ((actualJointResolvent_continuous event.frame event.energy event.nonreal).comp
      (continuous_const.add continuous_id.neg))

/-- The two actual currents use opposite physical transfers of the same full matrix. -/
theorem dressed_uncut_matrix_joint_continuous (detector source : DressedEvent) :
    Continuous (fun p : PhysicalMomentum×WholeMatrix=>dressedUncutMatrixRead detector source p.1 p.2) := by
  have d : Continuous (fun p : PhysicalMomentum×WholeMatrix=>dressedUncutCurrent detector (-p.1)) :=
    (dressed_uncut_current_continuous detector).comp continuous_fst.neg
  have s : Continuous (fun p : PhysicalMomentum×WholeMatrix=>dressedUncutCurrent source p.1) :=
    (dressed_uncut_current_continuous source).comp continuous_fst
  change Continuous (fun p : PhysicalMomentum×WholeMatrix=>
    ∑i,dressedUncutCurrent detector (-p.1) i*∑j,p.2 i j*dressedUncutCurrent source p.1 j)
  exact continuous_finsetSum _ fun i _=>((continuous_apply i).comp d).mul
    (continuous_finsetSum _ fun j _=>
      (((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).mul ((continuous_apply j).comp s)))

/-- The actual moving potential keeps its regular/contact term and all reflected field directions before taking the IR limit. -/
theorem dressed_uncut_moving_potential (detector source : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (r : staticDomain) :
    (r.val^2:ℝ) • dressedUncutMatrixRead detector source (r.val • n) (sourceGreen (sourceSpatialStaticRegularPoint n unit r))=
      (r.val^2:ℝ) • dressedUncutMatrixRead detector source (r.val • n) (wholeRegular (sourceStaticSpatialMomentum n r.val))-
      dressedUncutMatrixRead detector source (r.val • n)
        (wholeFrame (sourceStaticSpatialMomentum n r.val)*(sourceStaticSpatialKernel n unit r)⁻¹*
          (wholeFrame (-(sourceStaticSpatialMomentum n r.val))).transpose) := by
  have paid:=congrArg (dressedUncutMatrixRead detector source (r.val • n)) (whole_static_green_scaled n unit r)
  change dressedUncutMatrixRead detector source (r.val • n)
      ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))=
    dressedUncutMatrixRead detector source (r.val • n)
      ((r.val^2:ℝ) • wholeRegular (sourceStaticSpatialMomentum n r.val)-
        wholeFrame (sourceStaticSpatialMomentum n r.val)*(sourceStaticSpatialKernel n unit r)⁻¹*
          (wholeFrame (-(sourceStaticSpatialMomentum n r.val))).transpose) at paid
  simpa only [map_sub,map_smul] using paid

end LowEnergy.GaussComposite.ActualDressedUncutMoving
