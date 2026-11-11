import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RCurrentSourcePriceConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRCurrentBSource
open BurnolPhysicalState
namespace D
export OriginalKCombFirstFullSourceDynamics (raw)
end D
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
  (physicalUpdated original_updated_total)
end Recurrence
open private actual_raw_even from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "input" => Recurrence.physicalUpdated observation nontrivial half depth ordinal

private theorem input_even : reflectL2 input=input := by
  rw [Recurrence.original_updated_total,map_sub,
    actual_raw_even observation nontrivial half depth (ordinal+3),
    actual_raw_even observation nontrivial half depth (ordinal+1)]

private theorem input_gap : input ∈ locallyConstantFace burnolUnscaledCommonGapRadius := by
  rw [Recurrence.original_updated_total]
  exact (locallyConstantFace burnolUnscaledCommonGapRadius).sub_mem
    (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth (ordinal+3))
    (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth (ordinal+1))

namespace Current
export OriginalRCurrentSourcePrice (read)
end Current
namespace Physical
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
  (originalPoint original_action)
end Physical
namespace PA
export OriginalKCombCofinalPaAction (E Q)
end PA
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "E" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "Pi" => burnolEvenAmbientProjection
local notation "nativeNext" => OriginalKFiniteOrderRelease.GenericSourceStepBAction.gapSecondNext c input
local notation "unit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private def outsideNext : BurnolL2 :=
  burnolAmbientEvenPart (fourierL2 (E (nativeNext:Hq))-E (S nativeNext:Hq))

/-- Both B legs and the entire outside fibre are computed at the original written point. -/
structure ActionAt (point : BurnolL2) : Prop where
  firstB : burnolAmbientMeanZeroFirstCorrection point= -S nativeNext
  secondB : burnolAmbientMeanZeroSecondCorrection point=nativeNext
  correction : burnolAmbientEvenMeanZeroCorrection point=outsideNext observation nontrivial half depth ordinal
  outsideField : outside point=outsideNext observation nontrivial half depth ordinal
  physical : (Pi point:BurnolL2)=point-outsideNext observation nontrivial half depth ordinal
  inventory : point=(PA.E point:BurnolL2)+(PA.Q point:BurnolL2)+outsideNext observation nontrivial half depth ordinal
  coupledOutside : outsideNext observation nontrivial half depth ordinal=
    (OriginalRSourceCoupledChannels.sourceUpdate c unit (alpha (ordinal+3)-alpha (ordinal+1)) input).2

private theorem consumeAt {point : BurnolL2}
    (same : point=Physical.originalPoint observation nontrivial half depth ordinal)
    (channels : OriginalRSourceCoupledChannels.channels point=
      OriginalRSourceCoupledChannels.sourceUpdate c unit (alpha (ordinal+3)-alpha (ordinal+1)) input) :
    ActionAt observation nontrivial half depth ordinal point := by
  have actual := OriginalKFiniteOrderRelease.GenericSourceStepBAction.actual_forward_R_gap_B c input
    (input_even observation nontrivial half depth ordinal)
    (input_gap observation nontrivial half depth ordinal)
  have written : point=burnolDirectRightResolventCLM c input := by
    rw [same,Physical.original_action,OriginalKCombCofinalRAction.original_R_direct]
    rfl
  have first : burnolAmbientMeanZeroFirstCorrection point= -S nativeNext := by
    rw [written]
    exact actual.1
  have second : burnolAmbientMeanZeroSecondCorrection point=nativeNext := by
    rw [written]
    exact actual.2
  have correction : burnolAmbientEvenMeanZeroCorrection point=outsideNext observation nontrivial half depth ordinal := by
    unfold burnolAmbientEvenMeanZeroCorrection burnolAmbientRawMeanZeroCorrection outsideNext
    rw [first,second]
    simp only [Submodule.coe_neg,map_neg]
    congr 1
    module
  have even : reflectL2 point=point := by
    rw [same,OriginalRSourceCoupledChannels.actual_point_source,map_sub,
      actual_raw_even observation nontrivial half depth ((ordinal+3)+1),
      actual_raw_even observation nontrivial half depth ((ordinal+1)+1)]
  have part : burnolAmbientEvenPart point=point := by
    unfold burnolAmbientEvenPart
    rw [even]
    module
  have physical := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula point
  change (Pi point:BurnolL2)=burnolAmbientEvenPart point-burnolAmbientEvenMeanZeroCorrection point at physical
  rw [part,correction] at physical
  have total := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal point
  change (Pi point:BurnolL2)+outside point=point at total
  have outer : outside point=outsideNext observation nontrivial half depth ordinal := by
    rw [physical] at total
    linear_combination (norm:=module) total
  have split := congrArg (fun value : BurnolPaAmbientCarrier => (value:BurnolL2))
    (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (Pi point))
  change (PA.E point:BurnolL2)+(PA.Q point:BurnolL2)=(Pi point:BurnolL2) at split
  have inventory : point=(PA.E point:BurnolL2)+(PA.Q point:BurnolL2)+outsideNext observation nontrivial half depth ordinal := by
    linear_combination (norm:=module) -split-physical
  have sourceOutside := congrArg Prod.snd channels
  change outside point=(OriginalRSourceCoupledChannels.sourceUpdate c unit
    (alpha (ordinal+3)-alpha (ordinal+1)) input).2 at sourceOutside
  exact ⟨first,second,correction,outer,physical,inventory,outer.symm.trans sourceOutside⟩

local elab "readPoint% " sourceStx:term : term => do
  let source ← Lean.Elab.Term.elabTerm sourceStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType source)
  unless ty.getAppFn.constName? == some ``OriginalRCurrentSourcePrice.SourceReadAt && ty.getAppArgs.size == 6 do
    throwError "expected the original six-argument SourceReadAt"
  return ty.getAppArgs[5]!

private def ResultAt :=
  Σ' current : type_of% (Current.read observation nontrivial half depth ordinal),
    PProd (current=Current.read observation nontrivial half depth ordinal)
      (type_of% (consumeAt observation nontrivial half depth ordinal
        (point := readPoint% current.2.2)
        current.1.1.2.2.2.1 current.1.2.2.2))

attribute [local irreducible] ResultAt

opaque read : ResultAt observation nontrivial half depth ordinal := by
  unfold ResultAt
  let current := Current.read observation nontrivial half depth ordinal
  exact ⟨current,rfl,consumeAt observation nontrivial half depth ordinal
    (point := readPoint% current.2.2)
    current.1.1.2.2.2.1 current.1.2.2.2⟩

end OriginalRCurrentBSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

