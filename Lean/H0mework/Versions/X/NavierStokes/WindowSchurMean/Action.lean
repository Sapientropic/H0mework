import H0mework.Versions.X.NavierStokes.WindowSchurMean.Projection
import H0mework.Versions.X.NavierStokes.StressEvolutionRegeneration.Affine

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryOseen (H action lift)
open NativeWindowHistoryMeanProjection (embed mean residual)
open NativeWindowTraceAdjoint (value curlMap)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem curl_reality (M : ℕ) (v : physicalSpace (modes M)) :
    FiniteStateFourierReality (curlMap M v) := by
  rw [NativeWindowTraceAdjoint.curlMap_apply]
  exact curlLift_reality (modes M) (modes_closed M) _ (physical_reality (fun {_} h => modes_closed M _ h) v)

def frozen (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) :
    physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) :=
  LinearMap.toContinuousLinearMap (physicalOperator (modes M) (modes_zero M) (modes_closed M) nu
    (curlMap M v) (curl_reality M v))

theorem frozen_source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    frozen nu M (value seed M time)=NativeWindowTraceAdjoint.forward seed M time := rfl

theorem frozen_difference (nu : Viscosity) (M : ℕ) (u v w : physicalSpace (modes M)) :
    ((frozen nu M u-frozen nu M v) w).1=
      NativeAffineTransport.transport (modes M) nu (curlMap M (u-v)) w.1 := by
  change frozenOperator (modes M) nu (curlMap M u) w.1-frozenOperator (modes M) nu (curlMap M v) w.1=_
  rw [map_sub,map_sub,sub_apply]
  change _=(frozenOperator (modes M) nu (curlMap M u) w.1-frozenOperator (modes M) nu 0 w.1)-
    (frozenOperator (modes M) nu (curlMap M v) w.1-frozenOperator (modes M) nu 0 w.1)
  abel

def meanValue (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (mean (NativeWindowTraceWholeHistory.history seed time))

theorem mean_source (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    (mean (NativeWindowTraceWholeHistory.history seed time)).1=(NativeForwardWindowSource.source seed time).fst :=
  NativeWindowHistoryMeanProjection.source_mean seed time

private theorem profile_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (continuous : Continuous f) (time : ℝ) :
    Integrable (fun lag => f (time-lag)) averageMeasure :=
  ((Lp.memLp (NativeWindowHistoryOseen.profile f continuous time)).integrable (by simp)).congr
    (NativeWindowHistoryOseen.profile_ae f continuous time)

theorem value_average (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (∫ lag,value seed M (time-lag) ∂averageMeasure)=meanValue seed M time := by
  have paid : Integrable (NativeWindowTraceWholeHistory.history seed time) averageMeasure :=
    (Lp.memLp _).integrable (by norm_num)
  have same : (fun lag => value seed M (time-lag))=ᵐ[averageMeasure] fun lag =>
      restrictCLM (modes M) (modes_zero M) (modes_closed M) (NativeWindowTraceWholeHistory.history seed time lag) := by
    filter_upwards [NativeWindowTraceWholeHistory.history_ae seed time] with lag actual
    rw [actual]
    exact (NativeWindowHistoryOseen.restrict_original_total seed (time-lag) M).symm
  rw [integral_congr_ae same,meanValue,NativeWindowHistoryMeanProjection.mean_original]
  exact (restrictCLM (modes M) (modes_zero M) (modes_closed M)).integral_comp_comm paid

theorem forward_average (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (w : physicalSpace (modes M)) :
    (∫ lag,NativeWindowTraceAdjoint.forward seed M (time-lag) w ∂averageMeasure)=frozen nu M (meanValue seed M time) w := by
  let read := (ContinuousLinearMap.apply ℝ ComplexVorticityHilbertState w.1).comp (NativeAffineTransport.transport (modes M) nu)
  have advectorPaid := profile_integrable (NativeWindowTraceAdjoint.advector seed M)
    (NativeWindowTraceAdjoint.advector_continuous seed M) time
  have forwardPaid := profile_integrable (fun t => NativeWindowTraceAdjoint.forward seed M t w)
    ((NativeWindowTraceAdjoint.forward_continuous seed M).clm_apply continuous_const) time
  have valuePaid := profile_integrable (value seed M) (NativeWindowTraceAdjoint.value_continuous seed M) time
  have average : (∫ lag,NativeWindowTraceAdjoint.advector seed M (time-lag) ∂averageMeasure)=curlMap M (meanValue seed M time) := by
    change (∫ lag,curlMap M (value seed M (time-lag)) ∂averageMeasure)=_
    rw [(curlMap M).integral_comp_comm valuePaid,value_average]
  apply Subtype.ext
  have included := (physicalSpace (modes M)).subtypeL.integral_comp_comm forwardPaid
  change (∫ lag,(NativeWindowTraceAdjoint.forward seed M (time-lag) w).1 ∂averageMeasure)=
    (∫ lag,NativeWindowTraceAdjoint.forward seed M (time-lag) w ∂averageMeasure).1 at included
  rw [← included]
  have split : (fun lag => (NativeWindowTraceAdjoint.forward seed M (time-lag) w).1)=fun lag =>
      read (NativeWindowTraceAdjoint.advector seed M (time-lag))+frozenOperator (modes M) nu 0 w.1 := by
    funext lag
    exact congrArg (fun A : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState => A w.1)
      (NativeAffineTransport.frozen_split (modes M) nu _)
  rw [split,integral_add (read.integrable_comp advectorPaid) (integrable_const _),
    read.integral_comp_comm advectorPaid,average]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  exact (congrArg (fun A : ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState => A w.1)
    (NativeAffineTransport.frozen_split (modes M) nu (curlMap M (meanValue seed M time)))).symm

def meanOperator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  lift M (frozen nu M (meanValue seed M time))

theorem mean_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    mean (action seed M time (embed v))=meanOperator seed M time v := by
  let w:=restrictCLM (modes M) (modes_zero M) (modes_closed M) v
  have paid := profile_integrable (fun t => NativeWindowTraceAdjoint.forward seed M t w)
    ((NativeWindowTraceAdjoint.forward_continuous seed M).clm_apply continuous_const) time
  rw [NativeWindowHistoryMeanProjection.mean_original]
  have same : action seed M time (embed v)=ᵐ[averageMeasure] fun lag =>
      includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.forward seed M (time-lag) w) := by
    filter_upwards [NativeWindowHistoryOseen.action_ae seed M time (embed v),NativeWindowTraceWholeHistory.constant_ae v]
      with lag actual constant
    rw [actual,show embed v lag=v from constant]
    rfl
  rw [integral_congr_ae same,(includeCLM (modes M) (modes_closed M)).integral_comp_comm paid,forward_average]
  rfl

def creation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical →L[ℝ] H :=
  residual.comp ((action seed M time).comp embed)

theorem creation_value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    creation seed M time v=action seed M time (embed v)-embed (meanOperator seed M time v) := by
  simpa only [creation,ContinuousLinearMap.comp_apply,NativeWindowHistoryMeanProjection.residual,sub_apply,ContinuousLinearMap.id_apply,
    NativeWindowHistoryMeanProjection.projection] using!
      congrArg (fun w : wholePhysical => action seed M time (embed v)-embed w) (mean_action seed M time v)

private theorem lift_sub (M : ℕ) (A B : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M))
    (v : wholePhysical) : lift M A v-lift M B v=lift M (A-B) v := by
  simp only [lift,ContinuousLinearMap.comp_apply,sub_apply,map_sub]

theorem constant_action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    action seed M time (embed v)=ᵐ[averageMeasure] fun lag => lift M (frozen nu M (value seed M (time-lag))) v := by
  filter_upwards [NativeWindowHistoryOseen.action_ae seed M time (embed v),NativeWindowTraceWholeHistory.constant_ae v]
    with lag actual constant
  rw [actual,show embed v lag=v from constant,frozen_source]
  rfl

theorem creation_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    creation seed M time v=ᵐ[averageMeasure] fun lag =>
      lift M (frozen nu M (value seed M (time-lag))-frozen nu M (meanValue seed M time)) v := by
  rw [creation_value]
  filter_upwards [Lp.coeFn_sub (action seed M time (embed v)) (embed (meanOperator seed M time v)),
    constant_action_ae seed M time v,NativeWindowTraceWholeHistory.constant_ae (meanOperator seed M time v)] with lag split actual averaged
  rw [split,Pi.sub_apply,actual,show embed (meanOperator seed M time v) lag=meanOperator seed M time v from averaged]
  exact lift_sub M _ _ v

theorem creation_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    mean (creation seed M time v)=0 := NativeWindowHistoryMeanProjection.mean_residual _

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanAction
