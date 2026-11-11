import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RCurrentBSourceConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRCurrentActualGram
open Complex BurnolPhysicalState
open scoped InnerProductSpace
namespace Current
export OriginalRCurrentBSource (read ActionAt)
end Current
namespace Physical
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
  (originalPoint original_action)
end Physical
namespace Successor
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceSuccessorConsumer
  (independent_original_Gram)
end Successor
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence (physicalUpdated)
end Recurrence
namespace D
export OriginalKCombFirstFullSourceDynamics (raw)
end D
namespace PA
export OriginalKCombCofinalPaAction (E Q)
end PA
namespace Outside
export OriginalKFiniteOrderRelease.OutsideQuarterAction
  (outsideEmbedding quarterReturn outsideGram outsideEmbedding_injective outside_of_gap
   outside_R_outside physicalOutsideColumn_embedding incomingAmplitude)
end Outside
open private input_even input_gap from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RCurrentBSourceConsumer
open private actual_raw_even from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source
local notation "Pi" => burnolEvenAmbientProjection
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "b" => burnolAmbientMeanZeroFirstCorrection
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem full_norm_inventory (point:BurnolL2) :
    ‖PA.E point‖^2+‖PA.Q point‖^2+‖outside point‖^2=‖point‖^2 := by
  have physical:=Submodule.norm_sq_eq_add_norm_sq_projection point
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  have inside:=Submodule.norm_sq_eq_add_norm_sq_projection (Pi point)
    burnolCompactCoPoissonClosedRange.toSubmodule
  change ‖point‖^2=‖Pi point‖^2+‖outside point‖^2 at physical
  change ‖Pi point‖^2=‖PA.E point‖^2+‖PA.Q point‖^2 at inside
  linarith

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "input" => Recurrence.physicalUpdated observation nontrivial half depth ordinal
local notation "nativeNext" => OriginalKFiniteOrderRelease.GenericSourceStepBAction.gapSecondNext c input
local notation "unit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half:BurnolL2)
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth
local notation "kappa" => (-2*inner ℂ (fourierL2 (OriginalKSourceResolventReconstruction.generatedK c)) (PA.Q input:BurnolL2))

/-- The native B update executes the complete outside return and the original physical rank-one fee. -/
def quarterNext : BurnolQuarterMeanZeroCarrier :=
  Outside.quarterReturn c (d input)+kappa • OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (barC c)

/-- The same original Q update retains its source unit, Q resolvent and computed incoming outside fee. -/
def qNext : BurnolL2 :=
  (alpha (ordinal+3)-alpha (ordinal+1)) • unit+
    (PA.Q (burnolDirectRightResolventCLM c (PA.Q input:BurnolL2)):BurnolL2)+
    Outside.incomingAmplitude c (d input) • OriginalKSourceResolventReconstruction.generatedK (barC c)

def actualGramPrice (point:BurnolL2) : ℝ :=
  ‖PA.E point‖^2+‖qNext observation nontrivial half depth ordinal‖^2+
    ‖quarterNext observation nontrivial half depth ordinal‖^2-
    ‖S (quarterNext observation nontrivial half depth ordinal)‖^2

structure GramAt (point:BurnolL2) : Prop where
  nativeQuarter : nativeNext=quarterNext observation nontrivial half depth ordinal
  firstB : b point= -S (quarterNext observation nontrivial half depth ordinal)
  secondB : d point=quarterNext observation nontrivial half depth ordinal
  qField : (PA.Q point:BurnolL2)=qNext observation nontrivial half depth ordinal
  outsideField : outside point=Outside.outsideEmbedding (quarterNext observation nontrivial half depth ordinal)
  inventory : point=(PA.E point:BurnolL2)+qNext observation nontrivial half depth ordinal+
    Outside.outsideEmbedding (quarterNext observation nontrivial half depth ordinal)
  norm : actualGramPrice observation nontrivial half depth ordinal point=‖point‖^2
  resolvent : inner ℂ input point+star (inner ℂ input point)=
    -(observation.coordinate/2+star (observation.coordinate/2)-1/2)*
      (actualGramPrice observation nontrivial half depth ordinal point:ℂ)
  xiPositive : 0<actualGramPrice observation nontrivial half depth ordinal point

private theorem consumeAt {point:BurnolL2}
    (actual:Current.ActionAt observation nontrivial half depth ordinal point)
    (same:point=Physical.originalPoint observation nontrivial half depth ordinal)
    (channels:OriginalRSourceCoupledChannels.channels point=
      OriginalRSourceCoupledChannels.sourceUpdate c unit (alpha (ordinal+3)-alpha (ordinal+1)) input) :
    GramAt observation nontrivial half depth ordinal point := by
  have inputEven:=input_even observation nontrivial half depth ordinal
  have inputGap:=input_gap observation nontrivial half depth ordinal
  have pointEven:reflectL2 point=point := by
    rw [same,OriginalRSourceCoupledChannels.actual_point_source,map_sub,
      actual_raw_even observation nontrivial half depth ((ordinal+3)+1),
      actual_raw_even observation nontrivial half depth ((ordinal+1)+1)]
  have pointGap:point∈locallyConstantFace burnolUnscaledCommonGapRadius := by
    rw [same,OriginalRSourceCoupledChannels.actual_point_source]
    exact (locallyConstantFace burnolUnscaledCommonGapRadius).sub_mem
      (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ((ordinal+3)+1))
      (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ((ordinal+1)+1))
  have outsideNative:outside point=Outside.outsideEmbedding nativeNext := by
    rw [Outside.outside_of_gap point pointEven pointGap,actual.secondB]
  have native: nativeNext=quarterNext observation nontrivial half depth ordinal := by
    apply Outside.outsideEmbedding_injective
    calc
      Outside.outsideEmbedding nativeNext=outside point := outsideNative.symm
      _=(OriginalRSourceCoupledChannels.sourceUpdate c unit
          (alpha (ordinal+3)-alpha (ordinal+1)) input).2 :=
        actual.outsideField.trans actual.coupledOutside
      _=Outside.outsideEmbedding (quarterNext observation nontrivial half depth ordinal) := by
        change outside (burnolDirectRightResolventCLM c (outside input))+kappa •
          OriginalKCrossParameterRAdjointSource.PhysicalOutsideSource.physicalOutsideColumn c=_
        rw [Outside.outside_R_outside c input inputEven inputGap,
          Outside.physicalOutsideColumn_embedding]
        change Outside.outsideEmbedding (Outside.quarterReturn c (d input))+kappa •
          Outside.outsideEmbedding (OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (barC c))=
            Outside.outsideEmbedding (Outside.quarterReturn c (d input)+kappa •
              OriginalKDirectRCofinalOutsideVolterraSource.hPowerBColumn (barC c))
        rw [map_add,map_smul]
  have sourceQ:=congrArg Prod.fst channels
  change (PA.Q point:BurnolL2)=(alpha (ordinal+3)-alpha (ordinal+1)) • unit+
    (PA.Q (burnolDirectRightResolventCLM c (PA.Q input:BurnolL2)):BurnolL2)+
    (-2*inner ℂ (OriginalKDirectRCofinalOutsideVolterraSource.hPowerPhysicalCorrection c) (outside input)) •
      OriginalKSourceResolventReconstruction.generatedK (barC c) at sourceQ
  rw [Outside.outside_of_gap input inputEven inputGap] at sourceQ
  have qField:(PA.Q point:BurnolL2)=qNext observation nontrivial half depth ordinal := sourceQ
  have outsideActual:outside point=Outside.outsideEmbedding (quarterNext observation nontrivial half depth ordinal) := by
    rw [outsideNative,native]
  have inventory:=actual.inventory
  rw [←actual.outsideField,outsideActual,qField] at inventory
  have sourceNorm:=full_norm_inventory point
  change ‖PA.E point‖^2+‖(PA.Q point:BurnolL2)‖^2+‖outside point‖^2=‖point‖^2 at sourceNorm
  rw [qField,outsideActual,Outside.outsideGram] at sourceNorm
  have normPrice:actualGramPrice observation nontrivial half depth ordinal point=‖point‖^2 := by
    unfold actualGramPrice
    linarith
  have written:point=burnolDirectRightResolvent (observation.coordinate/2) input := by
    rw [same,Physical.original_action,OriginalKCombCofinalRAction.original_R_direct]
  have originalGram:=burnolDirectRightResolvent_gram (observation.coordinate/2) (observation.coordinate/2)
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) input
  rw [←written,inner_self_eq_norm_sq_to_K] at originalGram
  have resolvent:inner ℂ input point+star (inner ℂ input point)=
      -(observation.coordinate/2+star (observation.coordinate/2)-1/2)*
        (actualGramPrice observation nontrivial half depth ordinal point:ℂ) := by
    rw [normPrice,Complex.ofReal_pow]
    exact originalGram
  have nonzero:point≠0 := by
    intro zero
    exact Successor.independent_original_Gram observation nontrivial half depth ordinal (same.symm.trans zero)
  have positive:0<actualGramPrice observation nontrivial half depth ordinal point := by
    rw [normPrice]
    exact sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  exact ⟨native,actual.firstB.trans (congrArg (fun state=> -S state) native),
    actual.secondB.trans native,qField,outsideActual,inventory,normPrice,resolvent,positive⟩

private def ResultAt :=
  Σ' current:type_of% (Current.read observation nontrivial half depth ordinal),
    PProd (current=Current.read observation nontrivial half depth ordinal)
      (type_of% (consumeAt observation nontrivial half depth ordinal
        current.2.2 current.1.1.1.2.2.2.1 current.1.1.2.2.2))

attribute [local irreducible] ResultAt

opaque read : ResultAt observation nontrivial half depth ordinal := by
  unfold ResultAt
  let current:=Current.read observation nontrivial half depth ordinal
  exact ⟨current,rfl,consumeAt observation nontrivial half depth ordinal
    current.2.2 current.1.1.1.2.2.2.1 current.1.1.2.2.2⟩

end OriginalRCurrentActualGram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
