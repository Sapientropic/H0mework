import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCofinal

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUncutCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open PreparationVacuumFieldCovector PreparationVacuumRawJointFeedback PreparationVacuumCausalFieldResponse
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport
open ActualDressedTemporalCurrent


open ActualDressedReaderComponents ActualDressedCutReturn ActualDressedNoether
open CanonicalPhysicalYResolvent
attribute [local irreducible] currentVertex currentRestriction temporalReaderCompensation noetherReader
  jointResolvent dressedEulerObserver


open ActualDressedReaderMatching PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial FullYSourceCutoffVolterra
attribute [local irreducible] retainer cutoff uncutOperator


open ActualDressedRetainer
attribute [local irreducible] jointGenerator


open ActualDressedLeftRetained

open ActualDressedCofinal

/-- The complete original current reader consumes the same actual two uncut external responses. -/
def dressedUncutCurrent (event : DressedEvent) (transfer : PhysicalMomentum) : Fin 289→ℂ :=
  fun i=> -dressedEulerObserver event
    (jointResolvent (event.momentum+ -transfer) event.frame event.energy 0*
      currentRestriction (fieldBasis i) event.momentum event.frame 0*
      jointResolvent event.momentum event.frame event.energy 0)

private theorem pair_limit (J : H→L[ℂ]H) (L R : ℕ→H) (l r : H)
    (left : Tendsto L atTop (𝓝 l)) (right : Tendsto R atTop (𝓝 r)) :
    Tendsto (fun cut=>inner ℂ (L cut) (J (R cut))) atTop (𝓝 (inner ℂ l (J r))) := by
  exact left.inner (J.continuous.tendsto r |>.comp right)

/-- All289, including scalar/coframe/fiber/normal readers, share the actual fixed-F cutoff limit. -/
theorem dressed_uncut_current_generated (event : DressedEvent) (transfer : PhysicalMomentum) :
    Tendsto (fun cut=>sourceDressedConnectedCurrent event.epsilon event.precision event.momentum
      (-transfer) event.frame cut event.energy event.energy) atTop
      (𝓝 (dressedUncutCurrent event transfer)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have left:=dressed_two_response_limits event (event.momentum+ -transfer) event.frame
  have right:=dressed_two_response_limits event event.momentum event.frame
  have unit:=pair_limit (currentRestriction (fieldBasis i) event.momentum event.frame 0)
    (fun cut=>(finiteFull (event.momentum+ -transfer) event.frame cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision))
    (fun cut=>finiteFull event.momentum event.frame cut event.energy (sourceDressedUnit event.epsilon event.precision))
    ((jointResolvent (event.momentum+ -transfer) event.frame event.energy 0).adjoint (sourceDressedUnit event.epsilon event.precision))
    (jointResolvent event.momentum event.frame event.energy 0 (sourceDressedUnit event.epsilon event.precision)) left.2.1 right.1
  have background:=pair_limit (currentRestriction (fieldBasis i) event.momentum event.frame 0)
    (fun cut=>(finiteFull (event.momentum+ -transfer) event.frame cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision)))
    (fun cut=>finiteFull event.momentum event.frame cut event.energy (prepared (sourceProfile event.epsilon event.precision)))
    ((jointResolvent (event.momentum+ -transfer) event.frame event.energy 0).adjoint (prepared (sourceProfile event.epsilon event.precision)))
    (jointResolvent event.momentum event.frame event.energy 0 (prepared (sourceProfile event.epsilon event.precision))) left.2.2.2 right.2.2.1
  have pair:=unit.sub background
  simpa only [sourceDressedConnectedCurrent,sourceDressedCurrent,dressedUncutCurrent,
    currentVertex,dressed_euler_observer_original,mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_left,sub_eq_add_neg,neg_add,neg_neg] using pair

private theorem original_current_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (i : Fin 289) (L R : H→L[ℂ]H) (x b : H) (T : (H→L[ℂ]H)→L[ℂ]ℂ)
    (read : ∀A,T A= -inner ℂ x (A x)+inner ℂ b (A b)) :
    -T (L*currentRestriction (fieldBasis i) p F 0*R)=
      sourceCovector p (sourceTestApprox F (L.adjoint x)) (sourceTestApprox F (R x)) i-
      sourceCovector p (sourceTestApprox F (L.adjoint b)) (sourceTestApprox F (R b)) i := by
  rw [read]
  simp only [neg_add,neg_neg,mul_apply_eq_comp]
  exact congrArg₂ (fun u v : ℂ=>u-v)
    ((L.adjoint_inner_left (currentRestriction (fieldBasis i) p F 0 (R x)) x).symm.trans
      (currentRestriction_original_pair (fieldBasis i) p F (L.adjoint x) (R x)))
    ((L.adjoint_inner_left (currentRestriction (fieldBasis i) p F 0 (R b)) b).symm.trans
      (currentRestriction_original_pair (fieldBasis i) p F (L.adjoint b) (R b)))

/-- The original independent-dual source test and the actual background persist after removing the cutoff. -/
theorem dressed_uncut_current_original (event : DressedEvent) (transfer : PhysicalMomentum) :
    dressedUncutCurrent event transfer=
      sourceCovector event.momentum
        (sourceTestApprox event.frame ((jointResolvent (event.momentum+ -transfer) event.frame event.energy 0).adjoint
          (sourceDressedUnit event.epsilon event.precision)))
        (sourceTestApprox event.frame (jointResolvent event.momentum event.frame event.energy 0
          (sourceDressedUnit event.epsilon event.precision)))-
      sourceCovector event.momentum
        (sourceTestApprox event.frame ((jointResolvent (event.momentum+ -transfer) event.frame event.energy 0).adjoint
          (prepared (sourceProfile event.epsilon event.precision))))
        (sourceTestApprox event.frame (jointResolvent event.momentum event.frame event.energy 0
          (prepared (sourceProfile event.epsilon event.precision)))) := by
  funext i
  exact original_current_pair event.momentum event.frame i
    (jointResolvent (event.momentum+ -transfer) event.frame event.energy 0)
    (jointResolvent event.momentum event.frame event.energy 0)
    (sourceDressedUnit event.epsilon event.precision) (prepared (sourceProfile event.epsilon event.precision))
    (dressedEulerObserver event) (dressed_euler_observer_original event)

end LowEnergy.GaussComposite.ActualDressedUncutCurrent
