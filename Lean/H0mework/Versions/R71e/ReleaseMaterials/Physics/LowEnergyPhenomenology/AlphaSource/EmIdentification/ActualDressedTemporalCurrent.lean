import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalForm
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationWeightedChargePreparedActionReturn

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalCurrent
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

/-- This uses the same two actual finite response legs and the original background. -/
def dressedTemporalActionIntegral (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (readFrame : GaussUnitaryHistory.Index) : ℂ :=
  temporalActionForm a event.momentum
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision)))
    (sourceTestApprox readFrame (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))-
  temporalActionForm a event.momentum
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision))))
    (sourceTestApprox readFrame (finiteFull event.momentum event.frame event.cut event.energy
      (prepared (sourceProfile event.epsilon event.precision))))

theorem dressed_temporal_action_integral (event : DressedEvent) (transfer : PhysicalMomentum)
    (a : Fin 12) (readFrame : GaussUnitaryHistory.Index) :
    dressedTemporalActionIntegral event transfer a readFrame=dressedTemporalActionRead event transfer a readFrame := by
  simp only [dressedTemporalActionIntegral,temporal_action_form,dressedTemporalActionRead]

/-- Actual action normalization reaches the same completed joint orbit with the original graph cutoff limit. -/
theorem dressed_temporal_action_limit (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) :
    Tendsto (dressedTemporalActionIntegral event transfer a) GaussUnitaryHistory.sourceFilter
      (𝓝 (-dressedJointOrbitResponse event transfer a)) := by
  have same : dressedTemporalActionIntegral event transfer a=dressedTemporalActionRead event transfer a :=
    funext (dressed_temporal_action_integral event transfer a)
  rw [same]
  exact dressed_temporal_response_limit event transfer a

/-- The weighted Noether core is exactly the original action time-weight core. -/
theorem original_temporal_weight_core : weightCore=sourceTimeWeightCore := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantizer ((4:ℂ) • sourceActionWeight (sourceState z)) (f z)=
    quantizer (sourceTimeWeight (sourceState z)) (f z)
  rw [sourceTimeWeight_original]

/-- The source-generated weighted action core keeps both the time-matrix action and the pair current. -/
theorem temporal_raw_noether_return (a : Fin 12) (p : PhysicalMomentum) (l r : QuantumTest) :
    noetherForm (temporalField a) p l r 0=
      sourcePair l (sourceTimeWeightCore (familyCore (temporalField a) p r))-
        sourcePair l (normalChargeCore a r) := by
  rw [←original_temporal_weight_core,temporalForm_source,weightedTemporalForm_core,rawChargeCore_source]
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,sourcePair,map_sub,inner_sub_right,temporal_core]

/-- The canonical-normalized relative Y unit returns -1 on the unchanged actual source preparation. -/
theorem actual_temporal_Y_action_limit (event : DressedEvent) :
    Tendsto (fun readFrame : GaussUnitaryHistory.Index=>
      temporalActionForm 11 event.momentum
        (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))
        (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))-
      temporalActionForm 11 event.momentum
        (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))
        (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision))))
      GaussUnitaryHistory.sourceFilter (𝓝 (-1:ℂ)) := by
  simp_rw [temporal_action_form]
  exact actual_temporal_Y_source_limit event

private theorem sourceApprox_pair (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (sourceApprox F y)=inner ℂ (sourceApprox F x) y := by
  rw [sourceApprox_frame,sourceApprox_frame]
  simp only [inner_sum,sum_inner,inner_smul_right,inner_smul_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [←inner_conj_symm x (PreparationVacuumFullFieldRiesz.frameVector F i)]
  simp only [starRingEnd_apply]
  ring

/-- The actual raw Noether Riesz operator reads the source-generated time-weight and pair currents on exactly its original finite tests. -/
theorem temporal_noether_reader_return (a : Fin 12) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ x (noetherReader (temporalField a) p F 0 y)=
      sourcePair (sourceTestApprox F x)
        (sourceTimeWeightCore (familyCore (temporalField a) p (sourceTestApprox F y)))-
      sourcePair (sourceTestApprox F x) (normalChargeCore a (sourceTestApprox F y)) := by
  rw [←original_temporal_weight_core,temporalReader_projected_action,sourceApprox_pair,←sourceTestApprox_embed]
  change sourcePair (sourceTestApprox F x) (rawChargeCore a (sourceTestApprox F y))=_
  rw [rawChargeCore_source]
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,sourcePair,map_sub,inner_sub_right,temporal_core]

/-- Literal E uses its own raw action and independent canonical normalization on the same actual legs. -/
def dressedEMActionIntegral (event : DressedEvent) (transfer : PhysicalMomentum)
    (readFrame : GaussUnitaryHistory.Index) : ℂ :=
  emActionForm event.momentum
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision)))
    (sourceTestApprox readFrame (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))-
  emActionForm event.momentum
    (sourceTestApprox readFrame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision))))
    (sourceTestApprox readFrame (finiteFull event.momentum event.frame event.cut event.energy
      (prepared (sourceProfile event.epsilon event.precision))))

/-- This is the literal E completed action response, with the same unchanged prepared background. -/
def dressedEMActionResponse (event : DressedEvent) (transfer : PhysicalMomentum) : ℂ :=
  inner ℂ ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision))
    (chargeReader sourcePhaseGaugeLie (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))-
  inner ℂ ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision)))
    (chargeReader sourcePhaseGaugeLie (finiteFull event.momentum event.frame event.cut event.energy
      (prepared (sourceProfile event.epsilon event.precision))))

private theorem bounded_pair_limit (T : H→L[ℂ]H) (x y : H) :
    Tendsto (fun F : GaussUnitaryHistory.Index=>inner ℂ (embed (sourceTestApprox F x)) (T (embed (sourceTestApprox F y))))
      GaussUnitaryHistory.sourceFilter (𝓝 (inner ℂ x (T y))) := by
  have right : Tendsto (fun F : GaussUnitaryHistory.Index=>T (embed (sourceTestApprox F y)))
      GaussUnitaryHistory.sourceFilter (𝓝 (T y)) := T.continuous.tendsto y |>.comp (same_source_approximation y)
  exact (same_source_approximation x).inner right

private theorem em_pair_limit (p : PhysicalMomentum) (x y : H) :
    Tendsto (fun F : GaussUnitaryHistory.Index=>emActionForm p (sourceTestApprox F x) (sourceTestApprox F y))
      GaussUnitaryHistory.sourceFilter (𝓝 (inner ℂ x (chargeReader sourcePhaseGaugeLie y))) := by
  have paid:=bounded_pair_limit (chargeReader sourcePhaseGaugeLie) x y
  have same : (fun F : GaussUnitaryHistory.Index=>emActionForm p (sourceTestApprox F x) (sourceTestApprox F y))=
      fun F=>inner ℂ (embed (sourceTestApprox F x)) (chargeReader sourcePhaseGaugeLie (embed (sourceTestApprox F y))) := by
    funext F
    rw [em_action_form]
    simp only [sourcePair,←chargeReader_core]
  rw [same]
  exact paid

/-- The full-Fock, original-action literal E integral converges on this actual event without deleting source/input/finite-retainer terms. -/
theorem dressed_em_action_limit (event : DressedEvent) (transfer : PhysicalMomentum) :
    Tendsto (dressedEMActionIntegral event transfer) GaussUnitaryHistory.sourceFilter
      (𝓝 (dressedEMActionResponse event transfer)) := by
  exact (em_pair_limit event.momentum
    ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint (sourceDressedUnit event.epsilon event.precision))
    (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)).sub
    (em_pair_limit event.momentum
      ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint (prepared (sourceProfile event.epsilon event.precision)))
      (finiteFull event.momentum event.frame event.cut event.energy (prepared (sourceProfile event.epsilon event.precision))))

end LowEnergy.GaussComposite.ActualDressedTemporalCurrent
