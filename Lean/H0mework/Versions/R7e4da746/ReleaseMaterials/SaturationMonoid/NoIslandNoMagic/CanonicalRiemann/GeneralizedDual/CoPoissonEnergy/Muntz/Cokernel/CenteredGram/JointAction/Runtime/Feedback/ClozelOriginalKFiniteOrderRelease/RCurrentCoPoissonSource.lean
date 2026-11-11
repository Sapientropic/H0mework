import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalMobiusL2Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RCurrentBSourceConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.RCurrentCoPoissonSource
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped InnerProductSpace Topology
namespace CM
export CofinalCanonicalSourceMaterial (sourceIndex actual_raw_field)
end CM
namespace Source
export CofinalMobiusL2Source
  (sourceRaw sourceField valueField source_raw_read source_raw_gap source_realizes_integral reciprocalMoment)
end Source
namespace Physical
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer
  (originalPoint original_action)
end Physical
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
  (physicalUpdated original_updated_total)
end Recurrence
namespace D
export OriginalKCombFirstFullSourceDynamics (raw)
end D
namespace PA
export OriginalKCombCofinalPaAction (E Q)
end PA
namespace V
export OriginalKDirectRCofinalMobiusSourceAction (generatedCorrection)
end V
namespace Reentry
export OriginalKDirectRCofinalReentrySourceAction (actual_Pa_successor_Q_reentry sourceReentryVector)
end Reentry
open private input_even input_gap from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RCurrentBSourceConsumer
open private actual_raw_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source
local notation "q" => (1/4:ℝ)
local notation "Pi" => burnolEvenAmbientProjection
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
local notation "J" => OutsideQuarterAction.outsideEmbedding
local notation "d" => burnolAmbientMeanZeroSecondCorrection
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem source_raw_even (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) :
    Source.sourceRaw c j (-x)=Source.sourceRaw c j x := by
  cases j with
  | zero => simp only [Source.sourceRaw,CofinalCanonicalSourceMaterial.rawIterate,
      CofinalMobiusL2Source.seedSourceRaw,burnolTateStepBoxRaw,abs_neg]
  | succ j => simp only [Source.sourceRaw,CofinalCanonicalSourceMaterial.rawIterate,
      OriginalKCenteredMobiusRSource.sourceRRaw,abs_neg]

/-- The actual global co-sum retains the reciprocal mean of the same generated inverse source. -/
def sourceValueRaw (c:BurnolCompletedMellinCoordinate) (j:Nat) (x:ℝ) : ℂ :=
  burnolInnerGapForward (Source.sourceRaw c j) x-Source.reciprocalMoment c j

private theorem source_value_read (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    (Source.valueField c j:ℝ → ℂ)=ᵐ[volume]sourceValueRaw c j := by
  have sourceEven:reflectL2 (Source.sourceField c j)=Source.sourceField c j :=
    burnolReflectL2_eq_of_even_raw _ _ (Source.source_raw_read c j) (source_raw_even c j)
  have sourceGap:(Source.sourceField c j:ℝ → ℂ)=ᵐ[volume.restrict (symmetricInterval q)]fun _=>0 := by
    filter_upwards [ae_restrict_of_ae (Source.source_raw_read c j),
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x native inside
    rw [native,Source.source_raw_gap c j (by have small:=abs_le.mpr inside;linarith)]
  obtain ⟨raw,native,gap,realized⟩:=burnolRemainderSourceRead_realization_ae
    (Source.sourceField c j) (Source.valueField c j) sourceEven sourceGap
    (Source.source_realizes_integral c j)
  have same:raw=ᵐ[volume]Source.sourceRaw c j:=native.symm.trans (Source.source_raw_read c j)
  have forward:=burnolInnerGapForward_ae_congr raw (Source.sourceRaw c j) same
  have mean:(∫ u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u)=Source.reciprocalMoment c j := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae same] with u actual
    rw [actual]
  apply realized.trans
  filter_upwards [forward] with x actual
  rw [actual,mean]
  rfl

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "plus" => CM.sourceIndex observation (ordinal+4)
local notation "minus" => CM.sourceIndex observation (ordinal+2)
local notation "p" => Physical.originalPoint observation nontrivial half depth ordinal
local notation "input" => Recurrence.physicalUpdated observation nontrivial half depth ordinal
local notation "nativeNext" => GenericSourceStepBAction.gapSecondNext c input
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth
local notation "wholeUnit" => OriginalKDirectRCofinalPaUpdate.sourceWholeUnit observation nontrivial half
local notation "unitTest" => fourierL2 (burnolUnitTailResponse (barC c) 4)

theorem original_source_indices : plus=m+(ordinal+6) ∧ minus=m+(ordinal+4) := by
  change m+((ordinal+4)+2)=m+(ordinal+6) ∧ m+((ordinal+2)+2)=m+(ordinal+4)
  constructor <;> omega

def Praw (x:ℝ) : ℂ := sourceValueRaw c plus x-sourceValueRaw c minus x

private theorem Praw_read :
    (Source.valueField c plus-Source.valueField c minus:BurnolL2)=ᵐ[volume]
      Praw observation half ordinal := by
  filter_upwards [Lp.coeFn_sub (Source.valueField c plus) (Source.valueField c minus),
    source_value_read c plus,source_value_read c minus] with x subtraction first second
  rw [subtraction,Pi.sub_apply,first,second]
  rfl

theorem Praw_native : MemLp (Praw observation half ordinal) 2 volume :=
  (Lp.memLp (Source.valueField c plus-Source.valueField c minus)).ae_eq
    (Praw_read observation half ordinal)

/-- This L2 field is constructed from the executed full source co-sum, before the original point is identified. -/
def Pfield : BurnolL2 := (Praw_native observation half ordinal).toLp (Praw observation half ordinal)

theorem Pfield_coeFn : (Pfield observation half ordinal:ℝ → ℂ)=ᵐ[volume]Praw observation half ordinal :=
  (Praw_native observation half ordinal).coeFn_toLp

theorem Pfield_actual : Pfield observation half ordinal=p := by
  have native:Pfield observation half ordinal=Source.valueField c plus-Source.valueField c minus := by
    apply Lp.ext
    exact (Pfield_coeFn observation half ordinal).trans (Praw_read observation half ordinal).symm
  have written:=OriginalRSourceCoupledChannels.actual_point_source observation nontrivial half depth ordinal
  rw [CM.actual_raw_field,CM.actual_raw_field] at written
  change p=Source.valueField c (CM.sourceIndex observation ((ordinal+3)+1))-
    Source.valueField c (CM.sourceIndex observation ((ordinal+1)+1)) at written
  rw [show (ordinal+3)+1=ordinal+4 by omega,show (ordinal+1)+1=ordinal+2 by omega] at written
  exact native.trans written.symm

/-- The Pa source action includes the full original unit and the actual Q reentry fee. -/
def Eprog : BurnolPaAmbientCarrier :=
  V.generatedCorrection observation nontrivial half depth (ordinal+3)-
    V.generatedCorrection observation nontrivial half depth (ordinal+1)+
    (alpha (ordinal+3)-alpha (ordinal+1)) • PA.E (wholeUnit:BurnolL2)+
    inner ℂ unitTest (PA.Q input:BurnolL2) • (Reentry.sourceReentryVector c:BurnolPaAmbientCarrier)

theorem Eprog_actual : PA.E p=Eprog observation nontrivial half depth ordinal := by
  have first:=Reentry.actual_Pa_successor_Q_reentry observation nontrivial half depth (ordinal+3)
  have second:=Reentry.actual_Pa_successor_Q_reentry observation nontrivial half depth (ordinal+1)
  change PA.E (D.raw observation nontrivial half depth ((ordinal+3)+1))=_ at first
  change PA.E (D.raw observation nontrivial half depth ((ordinal+1)+1))=_ at second
  have fee:inner ℂ unitTest (PA.Q input:BurnolL2)=
      inner ℂ unitTest (PA.Q (D.raw observation nontrivial half depth (ordinal+3)):BurnolL2)-
      inner ℂ unitTest (PA.Q (D.raw observation nontrivial half depth (ordinal+1)):BurnolL2) := by
    rw [Recurrence.original_updated_total,map_sub,Submodule.coe_sub,inner_sub_right]
  rw [OriginalRSourceCoupledChannels.actual_point_source,map_sub,first,second]
  unfold Eprog
  rw [fee,sub_smul,sub_smul]
  module

/-- Both complete generated source fields are retained; no compressed Q-resolvent query occurs in this body. -/
def qComputed : BurnolL2 :=
  Pfield observation half ordinal-(Eprog observation nontrivial half depth ordinal:BurnolL2)-J nativeNext

theorem qComputed_actual : (PA.Q p:BurnolL2)=qComputed observation nontrivial half depth ordinal := by
  have actual:=GenericSourceStepBAction.actual_forward_R_gap_B c input
    (input_even observation nontrivial half depth ordinal) (input_gap observation nontrivial half depth ordinal)
  have action:p=burnolDirectRightResolventCLM c input := by
    rw [Physical.original_action,OriginalKCombCofinalRAction.original_R_direct]
    rfl
  have pointEven:reflectL2 p=p := by
    rw [OriginalRSourceCoupledChannels.actual_point_source,map_sub,
      actual_raw_even observation nontrivial half depth ((ordinal+3)+1),
      actual_raw_even observation nontrivial half depth ((ordinal+1)+1)]
  have pointGap:p∈locallyConstantFace burnolUnscaledCommonGapRadius := by
    rw [OriginalRSourceCoupledChannels.actual_point_source]
    exact (locallyConstantFace burnolUnscaledCommonGapRadius).sub_mem
      (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ((ordinal+3)+1))
      (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ((ordinal+1)+1))
  have second:d p=nativeNext := by rw [action];exact actual.2
  have outsideField:=OutsideQuarterAction.outside_of_gap p pointEven pointGap
  rw [second] at outsideField
  have whole:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal p
  change (Pi p:BurnolL2)+outside p=p at whole
  have inside:=congrArg (fun state:BurnolPaAmbientCarrier=>(state:BurnolL2))
    (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (Pi p))
  change (PA.E p:BurnolL2)+(PA.Q p:BurnolL2)=(Pi p:BurnolL2) at inside
  unfold qComputed
  rw [Pfield_actual observation nontrivial half depth ordinal,
    ←Eprog_actual observation nontrivial half depth ordinal,←outsideField]
  linear_combination (norm:=module) inside+whole

end OriginalKFiniteOrderRelease.RCurrentCoPoissonSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
