import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedYNoether
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationElectricWeightedGraph

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedJointGraph
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 Stage10.TemporalGauge CanonicalGradedSpatialSource SourceQuantumScalarChart
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussComposite GaussComposite.SourceGraph
open CanonicalScalarPreparation GaussDensityCore
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent CanonicalGradedCharge
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldConstraintResponse
open PreparationPhysicalDressedSpinChargeReturn PreparationPhysicalJointEMCouplingUnitReturn
open PreparationPhysicalVoltageNoether PreparationVacuumStaticVoltageSource PreparationPhysicalPhaseGaugeRealization
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard
open ActualDressedActionPhase ActualDressedFullCoulomb ActualDressedVoltagePhase
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse
  dressedJointInput chargeReader

open ActualDressedVoltagePreparation ActualDressedVoltageCurrent
open PreparationVacuumNativeFieldInjection GaussNativeMatter
open StageNineHolonomicField StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction

open ActualDressedYJoint PreparationVacuumActionDecomposition PreparationVacuumFullElectricWard CanonicalPhysicalWardCore
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumSourceActionJets FullQuantum.StateGreen FullQuantum.CoframeResponse

open PreparationVacuumElectricConstraint PreparationVacuumTemporalCharge PreparationVacuumSourcePreparedState
open Filter Set MeasureTheory
open PreparationChartGuard PreparationVacuumLowerClassical GaussFockPair

/-- The existing source preparation is an operator-domain point, not a chosen smooth test or replacement time response. -/
theorem source_profile_original_domain (event : DressedEvent) :
    sourceProfile event.epsilon event.precision=
      zeroLocalizedProfile actualNativeLocalizer (sourcePreparation event.epsilon event.precision).point.val := by
  unfold sourceProfile sourceCausalState
  rfl

/-- The original preparation already generates the background Yukawa domain and its concrete cutoff error on the background. -/
theorem source_background_yukawa_domain (event : DressedEvent) :
    ∃ h : prepared (sourceProfile event.epsilon event.precision)∈GaussRadialDomain.closedY.domain,
      ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared (sourceProfile event.epsilon event.precision),h⟩-
        FullYSourceCutoffVolterra.cutoff n (prepared (sourceProfile event.epsilon event.precision))‖ ≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound := by
  unfold sourceProfile
  exact ⟨(sourceCausalState event.epsilon event.precision).yukawaDomain,
    (sourceCausalState event.epsilon event.precision).yukawaCutoff⟩

/-- The original complete configuration orbit graph closes on the actual unit, with both original orbit terms retained. -/
theorem actual_unit_joint_graph (event : DressedEvent) (a : Fin 12) :
    Tendsto (fun readFrame : GaussUnitaryHistory.Index=>
      (embed (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision)),
       embed (orbitAction (originalUnit a) (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision)))))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (sourceDressedUnit event.epsilon event.precision,jointReader a (sourceDressedUnit event.epsilon event.precision))) :=
  sourceApprox_joint_graph a (sourceDressedUnit event.epsilon event.precision)

/-- The unchanged actual prepared background has its own source-generated complete joint graph. -/
theorem actual_background_joint_graph (event : DressedEvent) (a : Fin 12) :
    Tendsto (fun readFrame : GaussUnitaryHistory.Index=>
      (embed (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision))),
       embed (orbitAction (originalUnit a) (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision))))))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (prepared (sourceProfile event.epsilon event.precision),jointReader a (prepared (sourceProfile event.epsilon event.precision)))) :=
  sourceApprox_joint_graph a (prepared (sourceProfile event.epsilon event.precision))

/-- The response frame/cutoff/frequency stay fixed; a separate original read-frame filter supplies its genuine joint graph. -/
theorem actual_response_joint_graph (event : DressedEvent) (a : Fin 12) :
    Tendsto (fun readFrame : GaussUnitaryHistory.Index=>
      (embed (sourceTestApprox readFrame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)),
       embed (orbitAction (originalUnit a) (sourceTestApprox readFrame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy,
        jointReader a (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))) :=
  sourceApprox_joint_graph a (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)

/-- The graph value comes from the closure of the original weighted orbit, not from a new bounded-reader definition. -/
theorem actual_response_joint_domain (event : DressedEvent) (a : Fin 12) :
    (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy,
      jointReader a (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))∈
        closure (jointCoreGraph a) := by
  rw [original_joint_graph_closed]
  rfl

/-- The exact source graph error retains the original read frame and its unchosen preparation approximation. -/
theorem actual_response_joint_error (event : DressedEvent) (a : Fin 12) (readFrame : GaussUnitaryHistory.Index) :
    ‖embed (orbitAction (originalUnit a) (sourceTestApprox readFrame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))-
      jointReader a (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)‖ ≤
      chargePrice a*‖embed (sourceTestApprox readFrame
          (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))-
        sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy‖ := by
  have core : jointReader a (embed (sourceTestApprox readFrame
      (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)))=
      embed (orbitAction (originalUnit a) (sourceTestApprox readFrame
        (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))) :=
    jointReader_core a _
  rw [←core,←map_sub]
  exact ((jointReader a).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (jointReader_price a) (norm_nonneg _))

end LowEnergy.GaussComposite.ActualDressedJointGraph
