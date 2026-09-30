import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.Cross.Bound

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredCrossWork
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent (physicalSpace pairing coefficients)
open NativeCommonAdvectorAction (curlPair)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryDynamicKernel (transport)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeWindowHistorySpatialWords (history fiber operator)
open NativeWindowHistoryCreationCovariance (centered)
open NativeWindowHistoryCreationFirstJet (firstJet)
open NativeWindowHistoryAdjointSpatialHalf (moment cap energyCap)
open NativeWindowHistoryAdjointSpatialFeedback (sample read lift)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance balanceHistorySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
local instance balancePhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance balancePhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local notation "Q" => NativeWindowHistoryMeanProjection.residual
variable {nu : Viscosity}
def pureWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) : ℝ :=
  ∫lag,pairing (modes M) (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
    (transport nu M (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
      (centered seed M time (time-lag))) ∂averageMeasure

private theorem centered_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    MemLp (fun lag => centered seed M time (time-lag)) 1 averageMeasure :=
  NativeWindowTraceTerminalGraph.continuous_memLp time _
    (NativeWindowHistoryCreationCovariance.centered_continuous seed M time) 1

private theorem centered_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (∫lag,centered seed M time (time-lag) ∂averageMeasure)=0 := by
  have regular:=(NativeWindowTraceTerminalGraph.continuous_memLp time (NativeWindowTraceAdjoint.value seed M)
    (NativeWindowTraceAdjoint.value_continuous seed M) 1).integrable le_rfl
  unfold centered
  rw [integral_sub regular (integrable_const _),NativeWindowHistoryMeanAction.value_average]
  simp

private def testing (M : ℕ) (p : physicalSpace (modes M)) : physicalSpace (modes M) →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap (pairing (modes M) p)).comp (transport nu M p)

set_option backward.isDefEq.respectTransparency false in
private theorem mean_term_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (p : physicalSpace (modes M)) :
    (∫lag,pairing (modes M) p (transport nu M p (centered seed M time (time-lag))) ∂averageMeasure)=0 := by
  change (∫lag,testing (nu := nu) M p (centered seed M time (time-lag)) ∂averageMeasure)=0
  rw [(testing (nu := nu) M p).integral_comp_comm ((centered_memLp seed M time).integrable le_rfl),centered_zero,map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem pure_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    Integrable (fun lag => pairing (modes M) (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
      (transport nu M (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
        (centered seed M time (time-lag)))) averageMeasure := by
  have cc : Continuous (fun v : physicalSpace (modes M) => coefficients (modes M) v) :=
    (LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous
  have qc:=NativeWindowHistoryCreationCovariance.centered_continuous seed M time
  have rc:=(NativeWindowHistorySpatialTransport.finite M j).continuous.comp qc
  have product:=((transport nu M).continuous.comp rc).clm_apply qc
  have continuous:=(cc.comp rc).inner (𝕜 := ℝ) (cc.comp product)
  have actual : Continuous (fun s => pairing (modes M)
      (NativeWindowHistorySpatialTransport.finite M j (centered seed M time s))
      (transport nu M (NativeWindowHistorySpatialTransport.finite M j (centered seed M time s))
        (centered seed M time s))) := by
    simpa only [NativeFiniteActionResolvent.pairing,LinearMap.mk₂_apply,Function.comp_def] using continuous
  exact (NativeWindowTraceTerminalGraph.continuous_memLp time _ actual 1).integrable le_rfl

private theorem point_split (M : ℕ) (p r q : physicalSpace (modes M)) :
    pairing (modes M) (p+r) (transport nu M (p+r) q)=
      (point (nu := nu) M p r q+pairing (modes M) p (transport nu M p q))+
        pairing (modes M) r (transport nu M r q) := by
  simp only [point,map_add,add_apply,LinearMap.add_apply]
  ring

private theorem word_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time s : ℝ) :
    NativeWindowHistorySpatialTransport.finite M j (NativeWindowTraceAdjoint.value seed M s)=
      firstJet seed M 0 j time+NativeWindowHistorySpatialTransport.finite M j (centered seed M time s) := by
  rw [firstJet,NativeWindowHistoryMeanResidualLoad.jet_zero_mean]
  change NativeWindowHistorySpatialTransport.finite M j (NativeWindowTraceAdjoint.value seed M s)=
    NativeWindowHistorySpatialTransport.finite M j (NativeWindowHistoryMeanAction.meanValue seed M time)+
      NativeWindowHistorySpatialTransport.finite M j
        (NativeWindowTraceAdjoint.value seed M s-NativeWindowHistoryMeanAction.meanValue seed M time)
  rw [map_sub]
  abel

private theorem first_history_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    history seed M [j] time=ᵐ[averageMeasure] fun lag => NativePhysicalPairing.includeCLM (modes M) (modes_closed M)
      (NativeWindowHistorySpatialTransport.finite M j (NativeWindowTraceAdjoint.value seed M (time-lag))) := by
  filter_upwards [(fiber M [j]).coeFn_compLpL (finiteHistory seed time M),
    NativeWindowHistoryOseen.history_original seed M time] with lag actual original
  change history seed M [j] time lag=fiber M [j] (finiteHistory seed time M lag) at actual
  rw [actual,original]
  exact NativeWindowHistoryOseen.lift_included M _ _

set_option backward.isDefEq.respectTransparency false in
theorem fluctuation_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (j : Coordinate) (time : ℝ) :
    inner ℝ (history seed M [j] time) (NativeWindowHistoryMeanStrainSource.fluctuation seed M j time)=
      work seed M j time+pureWork seed M j time := by
  have original : inner ℝ (history seed M [j] time) (NativeWindowHistoryMeanStrainSource.fluctuation seed M j time)=
      ∫lag,pairing (modes M) (NativeWindowHistorySpatialTransport.finite M j (NativeWindowTraceAdjoint.value seed M (time-lag)))
        (transport nu M (NativeWindowHistorySpatialTransport.finite M j (NativeWindowTraceAdjoint.value seed M (time-lag)))
          (centered seed M time (time-lag))) ∂averageMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [first_history_ae seed M j time,NativeWindowHistoryMeanStrainSource.fluctuation_original seed M j time]
      with lag first last
    rw [first,last,NativePhysicalPairing.include_inner (modes M) (modes_zero M),NativePhysicalPairing.restrict_include,
      NativeWindowHistoryDynamicKernel.transport_apply]
  rw [original]
  have expanded := integral_congr_ae (μ := averageMeasure) (Eventually.of_forall fun lag =>
    (congrArg (fun v : physicalSpace (modes M) => pairing (modes M) v (transport nu M v
      (centered seed M time (time-lag)))) (word_split seed M j time (time-lag))).trans
        (point_split M _ _ _))
  rw [expanded]
  have mi := (testing (nu := nu) M (firstJet seed M 0 j time)).integrable_comp ((centered_memLp seed M time).integrable le_rfl)
  change Integrable (fun lag => pairing (modes M) (firstJet seed M 0 j time)
    (transport nu M (firstJet seed M 0 j time) (centered seed M time (time-lag)))) averageMeasure at mi
  have sumPaid : Integrable (fun lag => point (nu := nu) M (firstJet seed M 0 j time)
      (NativeWindowHistorySpatialTransport.finite M j (centered seed M time (time-lag)))
      (centered seed M time (time-lag))+pairing (modes M) (firstJet seed M 0 j time)
      (transport nu M (firstJet seed M 0 j time) (centered seed M time (time-lag)))) averageMeasure :=
    (work_integrable seed M j time).add mi
  rw [integral_add sumPaid (pure_integrable seed M j time),
    integral_add (work_integrable seed M j time) mi,mean_term_zero,add_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem source_first_word_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃K C : ℝ,0 ≤ K ∧ 0 ≤ C ∧ ∀M (j : Coordinate) (a : ℝ) (start : a∈Icc 0 horizon)
      (t : ℝ),t∈Ioo a horizon →
      deriv (NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2) t+
        (nu.coeff/8)*gradient M (history seed M [j] t) ≤
          K*NativeWindowHistoryAllOrderJointEnergy.energy seed M [j] a horizon start.2 t+C+
            2*pureWork seed M j t+
            2*inner ℝ (history seed M [j] t) (operator M [j] (NativeWindowHistoryOseen.forcingHistory seed M t))-
            2*inner ℝ (NativeWindowHistoryAllOrderCausal.created seed M [j] a horizon start.2 t)
              (NativeWindowHistoryAllOrderCausal.load seed M [j] t) := by
  obtain ⟨K,K0,full⟩:=NativeWindowHistoryMeanStrainJoint.source_first_word_generator seed horizon
  obtain ⟨C,C0,cross⟩:=source seed horizon (nu.coeff/8) (by positivity [nu.coeff_pos])
  refine ⟨K,C,K0,C0,fun M j a start t inside => ?_⟩
  have actual:=full M j a start t inside
  rw [inner_add_right,fluctuation_split] at actual
  have paid:=cross M j t ⟨start.1.trans inside.1.le,inside.2.le⟩
  have upper := (le_abs_self (2*work seed M j t)).trans paid
  linarith only [actual,upper]
end
end SaturationMonoid.NavierStokes.NativeCenteredCrossWork
