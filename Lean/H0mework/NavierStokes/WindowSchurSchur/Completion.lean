import H0mework.NavierStokes.WindowSchurSchur.TemporalControl
import H0mework.NavierStokes.WindowSchurMean.Time

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurCompletion
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation meanOperator)
open NativeWindowHistoryMeanBlocks (bath annihilation)
open NativeWindowHistorySchurAction (response effective remainder)
open NativeWindowTraceWholeHistory (finiteHistory projected)
noncomputable section
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

theorem residual_embed (v : wholePhysical) : Q (embed v)=0 := by
  change embed v-embed (mean (embed v))=0
  rw [NativeWindowHistoryMeanProjection.mean_embed,sub_self]

theorem mean_response (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    mean (response seed M time v)=0 :=
  (congrArg mean (NativeWindowHistorySchurAction.response_centered seed M time v)).symm.trans
    (NativeWindowHistoryMeanProjection.mean_residual _)

def complete (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) : H :=
  embed v+response seed M time v

theorem complete_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    mean (complete seed M time v)=v := by
  change mean (embed v+response seed M time v)=v
  rw [map_add,NativeWindowHistoryMeanProjection.mean_embed,mean_response,add_zero]

theorem complete_residual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    Q (complete seed M time v)=response seed M time v := by
  change Q (embed v+response seed M time v)=_
  exact ((Q).map_add _ _).trans ((congrArg₂ (fun a b : H => a+b) (residual_embed v)
    (NativeWindowHistorySchurAction.response_centered seed M time v)).trans (zero_add _))

theorem annihilation_residual (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    annihilation seed M time (Q v)=annihilation seed M time v := by
  change mean (action seed M time (Q (Q v)))=_
  rw [NativeWindowHistoryBathResolvent.residual_square]
  rfl

theorem complete_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    complete seed M time v-action seed M time (complete seed M time v)=embed (v-effective seed M time v) := by
  let x:=complete seed M time v
  have bathRead:bath seed M time x=bath seed M time (response seed M time v) :=
    (NativeWindowHistoryBathResolvent.bath_residual seed M time x).symm.trans
      (congrArg (bath seed M time) (complete_residual seed M time v))
  have qaction:Q (action seed M time x)=creation seed M time v+bath seed M time (response seed M time v) :=
    (NativeWindowHistoryMeanBlocks.residual_action_split seed M time x).trans
      (congrArg₂ (fun a b : H => a+b) (congrArg (creation seed M time) (complete_mean seed M time v)) bathRead)
  have qzero:Q (x-action seed M time x)=0 := by
    have paired:=(Q).map_sub x (action seed M time x)
    have generated:=NativeWindowHistorySchurAction.response_equation seed M time v
    exact paired.trans ((congrArg₂ (fun a b : H => a-b) (complete_residual seed M time v) qaction).trans
      (by rw [← generated]; abel))
  have annRead:annihilation seed M time x=annihilation seed M time (response seed M time v) :=
    (annihilation_residual seed M time x).symm.trans (congrArg (annihilation seed M time) (complete_residual seed M time v))
  have maction:mean (action seed M time x)=meanOperator seed M time v+annihilation seed M time (response seed M time v) :=
    (NativeWindowHistoryMeanBlocks.mean_action_split seed M time x).trans
      (congrArg₂ (fun a b : wholePhysical => a+b) (congrArg (meanOperator seed M time) (complete_mean seed M time v)) annRead)
  have meanRead:mean (x-action seed M time x)=v-effective seed M time v := by
    have paired:=mean.map_sub x (action seed M time x)
    exact paired.trans (congrArg₂ (fun a b : wholePhysical => a-b) (complete_mean seed M time v) maction)
  have split:=NativeWindowHistoryMeanProjection.split (x-action seed M time x)
  change embed (mean (x-action seed M time x))+Q (x-action seed M time x)=_ at split
  exact split.symm.trans ((congrArg₂ (fun a b : H => a+b) (congrArg embed meanRead) qzero).trans (add_zero _))

def completion (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  complete seed M time (mean (finiteHistory seed time M))

def commonForce (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  mean (finiteHistory seed time M)-mean (rateHistory seed M time)+remainder seed M time

theorem completion_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    completion seed M time=finiteHistory seed time M-NativeWindowHistorySchurTemporalControl.temporalResponse seed M time := by
  rw [NativeWindowHistorySchurTemporalControl.temporal_original]
  have split:=NativeWindowHistoryMeanProjection.split (finiteHistory seed time M)
  change embed (mean (finiteHistory seed time M))+Q (finiteHistory seed time M)=_ at split
  change embed (mean (finiteHistory seed time M))+response seed M time (mean (finiteHistory seed time M))=_
  exact (show embed (mean (finiteHistory seed time M))+response seed M time (mean (finiteHistory seed time M))=
      (embed (mean (finiteHistory seed time M))+Q (finiteHistory seed time M))-
        (Q (finiteHistory seed time M)-response seed M time (mean (finiteHistory seed time M))) by abel).trans
    (congrArg (fun x : H => x-(Q (finiteHistory seed time M)-response seed M time (mean (finiteHistory seed time M)))) split)

theorem completion_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    completion seed M time-action seed M time (completion seed M time)=embed (commonForce seed M time) := by
  have source:=complete_equation seed M time (mean (finiteHistory seed time M))
  have rate:=NativeWindowHistorySchurAction.source_rate seed M time
  have read:mean (finiteHistory seed time M)-effective seed M time (mean (finiteHistory seed time M))=commonForce seed M time := by
    unfold commonForce
    rw [rate]
    abel
  exact source.trans (congrArg embed read)

open NativeForwardWindowPairingReadout (averageMeasure)

theorem completion_equation_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ∀ᵐ lag ∂averageMeasure,completion seed M time lag-
      NativeWindowHistoryOseen.forwardFiber seed M (time-lag) (completion seed M time lag)=commonForce seed M time := by
  have source:=completion_equation seed M time
  filter_upwards [Lp.coeFn_sub (completion seed M time) (action seed M time (completion seed M time)),
    NativeWindowHistoryOseen.action_ae seed M time (completion seed M time),
    NativeWindowTraceWholeHistory.constant_ae (commonForce seed M time)] with lag subtract acted fixed
  have identity:=congrArg (fun h : H => h lag) source
  rw [subtract,Pi.sub_apply,acted] at identity
  exact identity.trans fixed

theorem completion_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (completion seed M time)=mean (finiteHistory seed time M) := complete_mean seed M time _

theorem projected_centered_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (h : H) :
    projected M (Q (action seed M time h))=Q (action seed M time h) :=
  (NativeWindowHistoryMeanProjection.residual_comp (NativeWindowTraceWholeHistory.projection M) (action seed M time h)).symm.trans
    (congrArg Q (NativeWindowHistoryOseenGap.projected_action seed M time h))

theorem response_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    projected M (response seed M time v)=response seed M time v := by
  have source:=NativeWindowHistorySchurAction.response_equation seed M time v
  have mapped:=congrArg ((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure) source
  have distribute:=((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure).map_sub
    (response seed M time v) (bath seed M time (response seed M time v))
  have bathRead:projected M (bath seed M time (response seed M time v))=bath seed M time (response seed M time v) :=
    projected_centered_action seed M time _
  have creationRead:projected M (creation seed M time v)=creation seed M time v := projected_centered_action seed M time _
  have same:projected M (response seed M time v)-bath seed M time (response seed M time v)=creation seed M time v :=
    (congrArg (fun x : H => projected M (response seed M time v)-x) bathRead).symm.trans
      (distribute.symm.trans (mapped.trans creationRead))
  exact (sub_left_inj).mp (same.trans source.symm)

theorem completion_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    projected M (completion seed M time)=completion seed M time := by
  have original:=NativeWindowHistoryMeanProjection.mean_comp (NativeWindowTraceWholeHistory.projection M) (finiteHistory seed time M)
  have mRead:NativeWindowTraceWholeHistory.projection M (mean (finiteHistory seed time M))=mean (finiteHistory seed time M) :=
    original.symm.trans (congrArg mean (NativeWindowHistoryOseenGap.projected_finiteHistory seed time M))
  have fixed:projected M (embed (mean (finiteHistory seed time M)))=embed (mean (finiteHistory seed time M)) :=
    (NativeWindowHistoryMeanProjection.comp_embed (NativeWindowTraceWholeHistory.projection M) _).trans (congrArg embed mRead)
  change projected M (embed (mean (finiteHistory seed time M))+response seed M time (mean (finiteHistory seed time M)))=_
  exact (((NativeWindowTraceWholeHistory.projection M).compLpL 2 averageMeasure).map_add _ _).trans
    (congrArg₂ (fun a b : H => a+b) fixed (response_projected seed M time _))

theorem source_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    finiteHistory seed time M=completion seed M time+NativeWindowHistorySchurTemporalControl.temporalResponse seed M time :=
  eq_add_of_sub_eq (completion_original seed M time).symm

def pair (wave : IntegerWavevector) (output input : Coordinate) (u v : H) : ℂ :=
  inner ℂ ((NativeWindowTraceWholeHistory.component (wave,output)).compLpL 2 averageMeasure u)
    ((NativeWindowTraceWholeHistory.component (0,input)).compLpL 2 averageMeasure v)

theorem pair_add (wave : IntegerWavevector) (output input : Coordinate) (u v x y : H) :
    pair wave output input (u+v) (x+y)=pair wave output input u x+pair wave output input u y+
      pair wave output input v x+pair wave output input v y := by
  simp only [pair,map_add,inner_add_left,inner_add_right]
  ring

theorem source_stress_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    pair wave output input (finiteHistory seed time M) (finiteHistory seed time M)=
      pair wave output input (completion seed M time) (completion seed M time)+
      pair wave output input (completion seed M time) (NativeWindowHistorySchurTemporalControl.temporalResponse seed M time)+
      pair wave output input (NativeWindowHistorySchurTemporalControl.temporalResponse seed M time) (completion seed M time)+
      pair wave output input (NativeWindowHistorySchurTemporalControl.temporalResponse seed M time)
        (NativeWindowHistorySchurTemporalControl.temporalResponse seed M time) :=
  (congrArg₂ (pair wave output input) (source_split seed M time) (source_split seed M time)).trans (pair_add _ _ _ _ _ _ _)

theorem source_residual_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    let z:=response seed M time (mean (finiteHistory seed time M))
    let w:=NativeWindowHistorySchurTemporalControl.temporalResponse seed M time
    pair wave output input (Q (finiteHistory seed time M)) (Q (finiteHistory seed time M))=
      pair wave output input z z+pair wave output input z w+pair wave output input w z+pair wave output input w w := by
  dsimp only
  exact (congrArg₂ (pair wave output input) (NativeWindowHistorySchurAction.source_residual seed M time)
    (NativeWindowHistorySchurAction.source_residual seed M time)).trans (pair_add _ _ _ _ _ _ _)

theorem original_stress_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    pair wave output input (NativeWindowTraceWholeHistory.history seed time) (NativeWindowTraceWholeHistory.history seed time)=
      -NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input :=
  NativeWindowTraceWholeHistory.stress_read seed time wave output input

theorem original_residual_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    pair wave output input (NativeWindowTraceWholeHistory.centered seed time) (NativeWindowTraceWholeHistory.centered seed time)=
      -(NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input-
        NativeStressSource.quadraticFlux (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
          wave output input) := NativeWindowTraceWholeHistory.residual_read seed time wave output input

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem completion_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    completion seed M (step.2.clockAdvance+time)=completion step.1 M time := by
  simp only [completion_original,NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M,
    NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurCompletion
