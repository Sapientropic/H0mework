import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualRestLightPhysicalCircuit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3CausalResponseWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceLightCircuit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource SourceQuantumFockGauge
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates ActualSourcePreparationBridge
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullPoleContinuation PreparationVacuumFullFieldRiesz PreparationVacuumPhysicalFeedback
open ActualDressedFullCoulomb ActualDressedNoether ActualElectronWholeNoetherObserver
open ActualElectronFullNoetherMixedSoft ActualElectronPhysicalJointInverse ActualEMJointCurrentMomentum
open ActualCompositeFieldCurrent PhysicalN3CausalWindow ActualElectronWholeChargeSoft
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldPerturbation.Blocks
open PreparationVacuumGaugeSourceInjection
open MeasureTheory intervalIntegral
open scoped Topology InnerProductSpace Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance windowRealOperators : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance windowRationalOperators : NormedAlgebra ℚ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointResolvent jointCurrent physicalTime timeSlope noetherReader noetherReaderContact
  projectedNoetherReader projectedNoetherReaderContact actualPhysicalEulerObserver
  sourceRestLightMap sourceRestRemainderMap actualFullNoetherVariation

/-- Original joint time/current continuity generates the selected source-current circuit at every transfer and age. -/
theorem source_projected_variation_joint (T : FullMaterialMatrix→L[ℂ]FullMaterialMatrix)
    (event : DressedEvent) (reader force : Field289) :
    Continuous (fun kt : PhysicalMomentum×ℝ=>sourceProjectedVariation T event (-kt.1) reader force kt.2) := by
  have momentum : Continuous (fun kt : PhysicalMomentum×ℝ=>event.momentum+kt.1):=
    (continuous_const (y:=event.momentum)).add continuous_fst
  have leftpair : Continuous (fun kt : PhysicalMomentum×ℝ=>(event.momentum+kt.1,-kt.2)):=by fun_prop
  have tl:=(actualJointTime_continuous event.frame).comp leftpair
  have l:=(actual_electron_physical_resolvent_continuous event.frame event.energy event.nonreal).comp momentum
  have dtl:=(physical_n3_time_slope_joint event.frame force).comp leftpair
  have current:=((joint_current_momentum_continuous event.frame event.energy).comp momentum).clm_apply
    (continuous_const (y:=force))
  have dl:=((l.mul current).mul l).neg
  have dJ : Continuous (fun _ : PhysicalMomentum×ℝ=>
    projectedNoetherReaderContact T reader force event.momentum event.frame):=continuous_const
  have J : Continuous (fun _ : PhysicalMomentum×ℝ=>
    projectedNoetherReader T reader event.momentum event.frame 0):=continuous_const
  have R : Continuous (fun _ : PhysicalMomentum×ℝ=>jointResolvent event.momentum event.frame event.energy 0):=continuous_const
  have dR : Continuous (fun _ : PhysicalMomentum×ℝ=>-(jointResolvent event.momentum event.frame event.energy 0*
    jointCurrent event.momentum event.frame event.energy 0 force*jointResolvent event.momentum event.frame event.energy 0)):=continuous_const
  have rightpair : Continuous (fun kt : PhysicalMomentum×ℝ=>(event.momentum,kt.2)):=by fun_prop
  have TR:=(actualJointTime_continuous event.frame).comp rightpair
  have dTR:=(physical_n3_time_slope_joint event.frame force).comp rightpair
  have generated:=(((((dtl.mul l).add (tl.mul dl)).mul J).add ((tl.mul l).mul dJ)).mul R |>.add
    (((tl.mul l).mul J).mul dR)).mul TR |>.add ((((tl.mul l).mul J).mul R).mul dTR)
  simpa only [sourceProjectedVariation,sub_neg_eq_add,Function.comp_def,Pi.mul_apply,Pi.add_apply,
    Pi.neg_apply] using! generated

def sourceProjectedWindowOperator (P : FullMaterialMatrix→L[ℂ]FullMaterialMatrix) (event : DressedEvent)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) : H→L[ℂ]H :=
  ∫age in (0:ℝ)..T,laplaceWeight lambda age • sourceProjectedVariation P event (-k) reader force age

def sourceProjectedPhysicalWindow (P : FullMaterialMatrix→L[ℂ]FullMaterialMatrix) (event : DressedEvent)
    (leg : CompositeLeg) (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) : ℂ :=
  actualPhysicalEulerObserver event leg (sourceProjectedWindowOperator P event k lambda T reader force)

private theorem projected_window_integrable (P : FullMaterialMatrix→L[ℂ]FullMaterialMatrix) (event : DressedEvent)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    IntervalIntegrable (fun age : ℝ=>laplaceWeight lambda age • sourceProjectedVariation P event (-k) reader force age)
      volume 0 T := by
  have weight : Continuous (fun age : ℝ=>laplaceWeight lambda age):=by unfold laplaceWeight;fun_prop
  have field : Continuous (fun age : ℝ=>sourceProjectedVariation P event (-k) reader force age):=by
    simpa only [Function.comp_def,id_eq] using
      (source_projected_variation_joint P event reader force).comp
        ((continuous_const (y:=k)).prodMk continuous_id)
  exact (weight.smul field).intervalIntegrable (μ:=volume) 0 T

/-- The original finite causal/Laplace operator window consumes the actual complete source-current split. -/
theorem actual_physical_n3_window_operator_source_rest_light_partition (event : DressedEvent) (k : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3ResponseWindowOperator event k lambda T reader force=
      sourceProjectedWindowOperator sourceRestLightMap event k lambda T reader force+
        sourceProjectedWindowOperator sourceRestRemainderMap event k lambda T reader force := by
  have light:=projected_window_integrable sourceRestLightMap event k lambda T reader force
  have remainder:=projected_window_integrable sourceRestRemainderMap event k lambda T reader force
  unfold physicalN3ResponseWindowOperator sourceProjectedWindowOperator
  rw [←intervalIntegral.integral_add light remainder]
  apply intervalIntegral.integral_congr
  intro age _
  exact (congrArg (fun A : H→L[ℂ]H=>laplaceWeight lambda age • A)
    (actual_full_noether_source_rest_light_partition event (-k) reader force age)).trans (smul_add _ _ _)

/-- The actual normalized physical N3-minus-background reader receives the exact same finite source-light split. -/
theorem actual_physical_n3_window_source_rest_light_partition (event : DressedEvent) (leg : CompositeLeg)
    (k : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (reader force : Field289) :
    physicalN3ResponseWindow event leg k lambda T reader force=
      sourceProjectedPhysicalWindow sourceRestLightMap event leg k lambda T reader force+
        sourceProjectedPhysicalWindow sourceRestRemainderMap event leg k lambda T reader force := by
  change actualPhysicalEulerObserver event leg (physicalN3ResponseWindowOperator event k lambda T reader force)=_
  exact (congrArg (actualPhysicalEulerObserver event leg)
    (actual_physical_n3_window_operator_source_rest_light_partition event k lambda T reader force)).trans
      ((actualPhysicalEulerObserver event leg).map_add _ _)

end LowEnergy.GaussComposite.ActualSourceLightCircuit
