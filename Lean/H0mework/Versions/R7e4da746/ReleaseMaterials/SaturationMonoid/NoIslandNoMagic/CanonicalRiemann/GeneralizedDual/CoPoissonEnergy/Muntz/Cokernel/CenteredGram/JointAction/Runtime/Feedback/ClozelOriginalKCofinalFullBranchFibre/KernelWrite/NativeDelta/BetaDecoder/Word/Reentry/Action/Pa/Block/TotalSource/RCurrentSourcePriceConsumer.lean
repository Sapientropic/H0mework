import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RSourceChannelsConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterCurrentEffect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerJordanMaterialConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRCurrentSourcePrice
open BurnolPhysicalState OriginalKFiniteOrderRelease
open scoped InnerProductSpace
namespace Written
export OriginalRSourceCoupledChannels (read)
end Written
namespace Physical
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
  (originalPoint original_action)
end Physical
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence (physicalUpdated)
end Recurrence
open private source_complete_price from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerMaterialConsumer

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "query" => UnitPowerJordanSource.sourceField c (m-1)
local notation "H" => UnitPowerSource.fulladjointPowerZ observation half
local notation "input" => Recurrence.physicalUpdated observation nontrivial half depth ordinal
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Hq" => BurnolQuarterIntervalL2

private def outsideAt : BurnolL2 :=
  E (QuarterCurrentSource.currentBNext c query:Hq)-
    fourierL2 (E (S (QuarterCurrentSource.currentBNext c query):Hq))

private def qAt : BurnolL2 :=
  H-(UnitPowerSource.paPowerField observation half:BurnolL2)-outsideAt observation half

private def priceAt (value : BurnolL2) : ℂ :=
  UnitPowerMaterialConsumer.actualPaFee observation half value+
    inner ℂ (qAt observation half) value+inner ℂ (outsideAt observation half) value

/-- The source effects belong to the literal adjoint query; only writtenPrice reads the original R point. -/
structure SourceReadAt (point : BurnolL2) : Prop where
  sourceNativeStep : UnitPowerJordanSource.sourceStep c query=H
  sourceFirstB : burnolAmbientMeanZeroFirstCorrection H=QuarterCurrentSource.currentBNext c query
  sourceSecondB : burnolAmbientMeanZeroSecondCorrection H= -S (QuarterCurrentSource.currentBNext c query)
  sourceCorrection : burnolAmbientEvenMeanZeroCorrection H=outsideAt observation half
  sourceOutside : OriginalKCombPhysicalAction.physicalRemainder H=outsideAt observation half
  sourcePhysical : (burnolEvenAmbientProjection H:BurnolL2)=H-outsideAt observation half
  sourceQ : (OriginalKCombCofinalPaAction.Q H:BurnolL2)=qAt observation half
  sourceInventory : H=(UnitPowerSource.paPowerField observation half:BurnolL2)+
    qAt observation half+outsideAt observation half
  sourceQPrice : ∀ value : BurnolL2, UnitPowerJordanMaterialConsumer.actualQPrice observation half value=
    inner ℂ (qAt observation half) value
  sourceOutsidePrice : ∀ value : BurnolL2, UnitPowerJordanMaterialConsumer.actualOutsidePrice observation half value=
    inner ℂ (outsideAt observation half) value
  sourceFullPrice : ∀ value : BurnolL2, inner ℂ H value=priceAt observation half value
  writtenPrice : inner ℂ query point=priceAt observation half input

private theorem consumeAt {point : BurnolL2}
    (same : point=Physical.originalPoint observation nontrivial half depth ordinal) :
    SourceReadAt observation nontrivial half depth ordinal point := by
  have positive : 0<m := generatedRiemannXiZeroOrder_pos observation nontrivial
  have nextOrder : (m-1)+1=m := Nat.sub_add_cancel positive
  have sourceWord := UnitPowerJordanSource.actual_sourceField observation half
  have nativeStep : UnitPowerJordanSource.sourceStep c query=H := by
    change UnitPowerJordanSource.sourceField c ((m-1)+1)=H
    rw [nextOrder]
    exact sourceWord
  have first := QuarterCurrentSource.actual_sourceStep_B_current c (m-1)
  have second := QuarterCurrentEffect.actual_sourceStep_second_B c (m-1)
  have correction := QuarterCurrentEffect.actual_sourceStep_correction c (m-1)
  have outside := QuarterCurrentEffect.actual_sourceStep_outside c (m-1)
  have physical := QuarterCurrentEffect.actual_sourceStep_physical c (m-1)
  rw [nativeStep] at first second correction outside physical
  change (burnolEvenAmbientProjection H:BurnolL2)=H-outsideAt observation half at physical
  have fullOutside : H-(burnolEvenAmbientProjection H:BurnolL2)=outsideAt observation half := by
    rw [physical]
    module
  have outsideSource : UnitPowerJordanSource.sourceOutside c m=outsideAt observation half := by
    have actual := UnitPowerJordanSource.source_outside_actual c m
    rw [sourceWord] at actual
    exact actual.symm.trans fullOutside
  have qSource : UnitPowerJordanSource.sourceQ observation half=qAt observation half := by
    unfold UnitPowerJordanSource.sourceQ UnitPowerJordanSource.sourcePhysical qAt
    rw [sourceWord,outsideSource]
    module
  have qPrice (value : BurnolL2) :
      UnitPowerJordanMaterialConsumer.actualQPrice observation half value=
        inner ℂ (qAt observation half) value := by
    change inner ℂ (UnitPowerJordanSource.sourceQ observation half) value=_
    rw [qSource]
  have outsidePrice (value : BurnolL2) :
      UnitPowerJordanMaterialConsumer.actualOutsidePrice observation half value=
        inner ℂ (outsideAt observation half) value := by
    rw [←outsideSource]
    simp only [UnitPowerJordanMaterialConsumer.actualOutsidePrice,
      UnitPowerJordanSource.sourceOutside,sum_inner,inner_smul_left,starRingEnd_apply]
  have price (value : BurnolL2) :
      UnitPowerJordanMaterialConsumer.completePrice observation half value=priceAt observation half value := by
    unfold UnitPowerJordanMaterialConsumer.completePrice priceAt
    rw [qPrice,outsidePrice]
  have fullPrice (value : BurnolL2) : inner ℂ H value=priceAt observation half value := by
    have generated := source_complete_price observation nontrivial half value
    rw [UnitPowerSource.actual_full_power_read observation half] at generated
    exact generated.trans
      ((UnitPowerJordanMaterialConsumer.complete_price_generated observation nontrivial half value).trans
        (price value))
  have writtenPrice : inner ℂ query point=priceAt observation half input := by
    rw [same,Physical.original_action,OriginalKCombCofinalRAction.original_R_direct]
    change inner ℂ query (burnolDirectRightResolventCLM c input)=_
    rw [←ContinuousLinearMap.adjoint_inner_left,UnitPowerJordanSource.sourceStep_actual,nativeStep]
    exact fullPrice input
  exact {
    sourceNativeStep := nativeStep
    sourceFirstB := first
    sourceSecondB := second
    sourceCorrection := correction
    sourceOutside := outside
    sourcePhysical := physical
    sourceQ := (UnitPowerJordanSource.sourceQ_actual observation nontrivial half).trans qSource
    sourceInventory := by
      rw [←qSource,←outsideSource]
      exact UnitPowerJordanSource.source_full_inventory observation half
    sourceQPrice := qPrice
    sourceOutsidePrice := outsidePrice
    sourceFullPrice := fullPrice
    writtenPrice := writtenPrice }

private def ResultAt :=
  Σ' written : type_of% (Written.read observation nontrivial half depth ordinal),
    PProd (written=Written.read observation nontrivial half depth ordinal)
      (type_of% (consumeAt observation nontrivial half depth ordinal written.1.2.2.2.1))

attribute [local irreducible] ResultAt

/-- One original written whole/next consumes the actual current-source adjoint price. -/
opaque read : ResultAt observation nontrivial half depth ordinal := by
  unfold ResultAt
  let written := Written.read observation nontrivial half depth ordinal
  exact ⟨written,rfl,consumeAt observation nontrivial half depth ordinal written.1.2.2.2.1⟩

end OriginalRCurrentSourcePrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
