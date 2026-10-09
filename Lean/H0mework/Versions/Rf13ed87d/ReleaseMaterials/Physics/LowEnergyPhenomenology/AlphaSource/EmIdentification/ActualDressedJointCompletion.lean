import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedJointWard
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedActionPhase

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedJointCompletion
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite.SourceGraph Electromagnetic.Identification
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussUnitaryHistory (Index)
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open PreparationPhysicalDressedSpinChargeReturn
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMDressedCharacter
open scoped BigOperators ContDiff InnerProductSpace Matrix
open PhysicalEMDressedPreparedRead PreparationVacuumSourcePreparedState
open CanonicalScalarPreparation PreparationChartGuard PreparationScalarCoordinates PreparationCoordinates CanonicalPreparationCutoff PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open MeasureTheory Filter Set GaussHistoryHilbert GaussHalfDensity

open ActualDressedSourcePreparation PreparationVacuumMixedFieldReturn
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull

open ActualDressedSourceResponse PreparationPhysicalJointEMCouplingUnitReturn ActualEMOriginWard PreparationPhysicalPhaseGaugeRealization
open CanonicalGradedCharge CanonicalPhysicalWardCore PreparationVacuumActionDecomposition PreparationVacuumFullElectricWard PreparationVacuumFieldConstraintResponse

open ActualDressedJointWard ActualDressedActionPhase
open GaussUnitaryHistory (sourceFilter)
open scoped Topology

/-- The actual frame commutator is retained, rather than assuming the selected finite span is charge invariant. -/
def dressedChargeFrameDefect (F : Index) (x : H) : H :=
  chargeReader sourcePhaseGaugeLie (PreparationVacuumFieldConstraintResponse.sourceApprox F x)-
    PreparationVacuumFieldConstraintResponse.sourceApprox F (chargeReader sourcePhaseGaugeLie x)

theorem dressed_joint_frame_return (epsilon : ℝ) (precision : 0<epsilon) (F : Index) :
    chargeReader sourcePhaseGaugeLie (embed (sourceTestApprox F (sourceDressedUnit epsilon precision)))=
      (1/2:ℂ) • embed (sourceTestApprox F (sourceDressedUnit epsilon precision))+
        embed (sourceTestApprox F (dressedJointInput epsilon precision))+
        dressedChargeFrameDefect F (sourceDressedUnit epsilon precision) := by
  have transported:=congrArg (PreparationVacuumFieldConstraintResponse.sourceApprox F) (dressed_joint_unit_return epsilon precision)
  simp only [map_add,map_smul] at transported
  simp only [sourceTestApprox_embed,dressedChargeFrameDefect]
  rw [transported]
  abel

/-- Complete source approximation removes the exact bounded Noether frame defect, without any invariant-span premise. -/
theorem dressed_joint_frame_defect_limit (x : H) :
    Tendsto (fun F : Index=>dressedChargeFrameDefect F x) sourceFilter (𝓝 0) := by
  have first:=(chargeReader sourcePhaseGaugeLie).continuous.tendsto x |>.comp (same_source_approximation x)
  have second:=same_source_approximation (chargeReader sourcePhaseGaugeLie x)
  have difference:=first.sub second
  simpa only [sourceTestApprox_embed,sub_self,dressedChargeFrameDefect,Function.comp_apply] using difference

theorem dressed_unit_eventually_nonzero (epsilon : ℝ) (precision : 0<epsilon) :
    ∀ᶠ F : Index in sourceFilter,embed (sourceTestApprox F (sourceDressedUnit epsilon precision))≠0 := by
  have unit : sourceDressedUnit epsilon precision≠0 := by
    intro zero
    have h:=source_dressed_unit_norm epsilon precision
    rw [zero,norm_zero] at h
    exact zero_ne_one h
  exact (same_source_approximation (sourceDressedUnit epsilon precision)).eventually_ne unit

/-- Every fixed actual propagated event is nonzero in sufficiently large original source frames. -/
theorem dressed_response_eventually_nonzero (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (responseFrame : Index) (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    ∀ᶠ readFrame : Index in sourceFilter,
      embed (sourceTestApprox readFrame (sourceDressedResponse epsilon precision p responseFrame cut z))≠0 := by
  exact (same_source_approximation _).eventually_ne
    (source_dressed_response_nonzero epsilon precision p responseFrame cut z nonreal)

/-- The original frame pairing of the bounded charge approximation tends to zero for the same actual unit. -/
theorem dressed_joint_frame_pair_limit (epsilon : ℝ) (precision : 0<epsilon) :
    Tendsto (fun F : Index=>inner ℂ (sourceDressedUnit epsilon precision)
      (dressedChargeFrameDefect F (sourceDressedUnit epsilon precision))) sourceFilter (𝓝 0) := by
  have h:=(tendsto_const_nhds : Tendsto (fun _ : Index=>sourceDressedUnit epsilon precision) sourceFilter
    (𝓝 (sourceDressedUnit epsilon precision))).inner (𝕜:=ℂ) (dressed_joint_frame_defect_limit (sourceDressedUnit epsilon precision))
  simpa only [inner_zero_right] using h

end LowEnergy.GaussComposite.ActualDressedJointCompletion
