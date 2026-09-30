import H0mework.Versions.X.NavierStokes.WindowSchurSchur.Transpose

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurMomentum
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistorySchurCompletion (completion commonForce)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeWindowHistorySchurAdvectorFiber (family rawProfile xProfile wProfile)
open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowHistorySchurTranspose (transposeAction)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def rawAction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (family nu M).holderL averageMeasure ∞ 2 2 (rawProfile seed M time)

theorem rawAction_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    rawAction seed M time r=ᵐ[averageMeasure] fun lag => family nu M (finiteHistory seed time M lag) (r lag) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical) (F := wholePhysical) (G := wholePhysical)
    (r := 2) (family nu M) (rawProfile seed M time) r,NativeWindowHistorySchurAdvectorFiber.rawProfile_ae seed M time]
    with lag applied source
  change rawAction seed M time r lag=family nu M (rawProfile seed M time lag) (r lag) at applied
  rw [applied,source]

theorem rawAction_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rawAction seed M time=xAction seed M time+wAction seed M time := by
  have split:rawProfile seed M time=xProfile seed M time+wProfile seed M time := by
    unfold wProfile
    abel
  exact (congrArg ((family nu M).holderL averageMeasure ∞ 2 2) split).trans
    (((family nu M).holderL averageMeasure ∞ 2 2).map_add _ _)

theorem rawAction_source (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    action seed M time=(diffusion nu M).compLpL 2 averageMeasure+rawAction seed M time := by
  exact (NativeWindowHistorySchurAdvectorAction.source_action_split seed M time).trans
    ((add_assoc ((diffusion nu M).compLpL 2 averageMeasure) (xAction seed M time) (wAction seed M time)).trans
      (congrArg (fun T : H →L[ℝ] H => (diffusion nu M).compLpL 2 averageMeasure+T) (rawAction_split seed M time).symm))

def rawNonlinear (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  rawAction seed M time (finiteHistory seed time M)

def xJoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  xAction seed M time (completion seed M time)+wAction seed M time (completion seed M time)

def xMixed (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  xAction seed M time (temporalResponse seed M time)

def wSelf (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H :=
  wAction seed M time (temporalResponse seed M time)

theorem nonlinear_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    rawNonlinear seed M time=xJoint seed M time+xMixed seed M time+wSelf seed M time := by
  have split:=congrArg (rawAction seed M time) (NativeWindowHistorySchurCompletion.source_split seed M time)
  have first:=congrArg (fun T : H →L[ℝ] H => T (completion seed M time)) (rawAction_split seed M time)
  have last:=congrArg (fun T : H →L[ℝ] H => T (temporalResponse seed M time)) (rawAction_split seed M time)
  exact split.trans (((rawAction seed M time).map_add (completion seed M time) (temporalResponse seed M time)).trans
    ((congrArg₂ (fun u v : H => u+v) first last).trans
      (add_assoc (xJoint seed M time) (xMixed seed M time) (wSelf seed M time)).symm))

theorem xJoint_transpose (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    xJoint seed M time=transposeAction seed M time (finiteHistory seed time M) := by
  apply Lp.ext
  filter_upwards [NativeWindowHistorySchurTranspose.transpose_ae seed M time (finiteHistory seed time M),
    NativeWindowHistorySchurAdvectorAction.xAction_ae seed M time (completion seed M time),
    NativeWindowHistorySchurAdvectorAction.wAction_ae seed M time (completion seed M time),
    Lp.coeFn_add (xAction seed M time (completion seed M time)) (wAction seed M time (completion seed M time)),
    Lp.coeFn_add (completion seed M time) (temporalResponse seed M time)] with lag trans x w added split
  have source:=congrArg (fun h : H => h lag) (NativeWindowHistorySchurCompletion.source_split seed M time)
  rw [split,Pi.add_apply] at source
  have left:=added.trans (congrArg₂ (fun u v : wholePhysical => u+v) x w)
  have right:=trans.trans ((congrArg (fun u : wholePhysical => family nu M u (completion seed M time lag)) source).trans
    (congrArg (fun T : wholePhysical →L[ℝ] wholePhysical => T (completion seed M time lag)) ((family nu M).map_add _ _)))
  exact left.trans right.symm

theorem xJoint_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    xJoint seed M time=completion seed M time-(diffusion nu M).compLpL 2 averageMeasure (completion seed M time)-
      embed (commonForce seed M time) := by
  have expansion:=congrArg (fun T : H →L[ℝ] H => T (completion seed M time))
    (NativeWindowHistorySchurAdvectorAction.source_action_split seed M time)
  change action seed M time (completion seed M time)=
    (diffusion nu M).compLpL 2 averageMeasure (completion seed M time)+
      xAction seed M time (completion seed M time)+wAction seed M time (completion seed M time) at expansion
  have equation:=NativeWindowHistorySchurCompletion.completion_equation seed M time
  rw [expansion] at equation
  have solved:=sub_eq_iff_eq_add.mp equation
  calc
    xJoint seed M time=(embed (commonForce seed M time)+
        ((diffusion nu M).compLpL 2 averageMeasure (completion seed M time)+
          xAction seed M time (completion seed M time)+wAction seed M time (completion seed M time)))-
        (diffusion nu M).compLpL 2 averageMeasure (completion seed M time)-embed (commonForce seed M time) := by unfold xJoint; abel
    _ = _ := congrArg (fun v : H => v-(diffusion nu M).compLpL 2 averageMeasure (completion seed M time)-
      embed (commonForce seed M time)) solved.symm

theorem xJoint_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (xJoint seed M time)=mean (finiteHistory seed time M)-
      diffusion nu M (mean (finiteHistory seed time M))-commonForce seed M time := by
  have original:=congrArg mean (xJoint_equation seed M time)
  have first:=mean.map_sub (completion seed M time) ((diffusion nu M).compLpL 2 averageMeasure (completion seed M time))
  have heat:mean ((diffusion nu M).compLpL 2 averageMeasure (completion seed M time))=
      diffusion nu M (mean (finiteHistory seed time M)) :=
    (NativeWindowHistoryMeanProjection.mean_comp (diffusion nu M) (completion seed M time)).trans
      (congrArg (diffusion nu M) (NativeWindowHistorySchurCompletion.completion_mean seed M time))
  exact original.trans ((mean.map_sub _ _).trans
    (congrArg₂ (fun u v : wholePhysical => u-v)
      (first.trans (congrArg₂ (fun u v : wholePhysical => u-v)
        (NativeWindowHistorySchurCompletion.completion_mean seed M time) heat))
      (NativeWindowHistoryMeanProjection.mean_embed (commonForce seed M time))))

theorem source_momentum (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (rateHistory seed M time)=mean (finiteHistory seed time M)-commonForce seed M time+
      mean (xMixed seed M time)+mean (wSelf seed M time)+mean (forcingHistory seed M time) := by
  have source:=congrArg mean (NativeWindowHistoryOseen.source_equation seed M time)
  have acted:=congrArg (fun T : H →L[ℝ] H => T (finiteHistory seed time M)) (rawAction_source seed M time)
  change action seed M time (finiteHistory seed time M)=
    (diffusion nu M).compLpL 2 averageMeasure (finiteHistory seed time M)+rawNonlinear seed M time at acted
  have actedMean:mean (action seed M time (finiteHistory seed time M))=
      diffusion nu M (mean (finiteHistory seed time M))+mean (rawNonlinear seed M time) :=
    (congrArg mean acted).trans
      ((mean.map_add ((diffusion nu M).compLpL 2 averageMeasure (finiteHistory seed time M)) (rawNonlinear seed M time)).trans
        (congrArg (fun u : wholePhysical => u+mean (rawNonlinear seed M time))
          (NativeWindowHistoryMeanProjection.mean_comp (diffusion nu M) (finiteHistory seed time M))))
  have rateMean:=source.trans ((mean.map_add (action seed M time (finiteHistory seed time M)) (forcingHistory seed M time)).trans
    (congrArg (fun u : wholePhysical => u+mean (forcingHistory seed M time)) actedMean))
  have nonlinearMean:mean (rawNonlinear seed M time)=
      mean (xJoint seed M time)+mean (xMixed seed M time)+mean (wSelf seed M time) :=
    (congrArg mean (nonlinear_split seed M time)).trans
      ((mean.map_add (xJoint seed M time+xMixed seed M time) (wSelf seed M time)).trans
        (congrArg (fun u : wholePhysical => u+mean (wSelf seed M time)) (mean.map_add (xJoint seed M time) (xMixed seed M time))))
  have paid:=rateMean.trans ((congrArg (fun u : wholePhysical => diffusion nu M (mean (finiteHistory seed time M))+u+
      mean (forcingHistory seed M time)) nonlinearMean).trans
    (congrArg (fun u : wholePhysical => diffusion nu M (mean (finiteHistory seed time M))+
      (u+mean (xMixed seed M time)+mean (wSelf seed M time))+mean (forcingHistory seed M time)) (xJoint_mean seed M time)))
  exact paid.trans (by abel)

theorem read_wave (M : ℕ) (v : NativeResolventCompactness.State) (wave : IntegerWavevector) :
    NativeEndpointVelocityCarrier.wholeVelocity (NativeWindowHistoryMeanTime.read M v) wave=
      if wave∈modes M then NativeEndpointVelocityCarrier.wholeVelocity v wave else 0 := by
  by_cases zero:wave=0
  · subst wave
    simp only [NativeEndpointVelocityCarrier.wholeVelocity_zero,if_neg (modes_zero M)]
  · funext i
    rw [NativeWindowHistoryMeanTime.read_original,NativeEndpointVelocityCarrier.wholeVelocity_nonzero _ ⟨wave,zero⟩,
      wholeRestartVelocityEndpointGalerkinInitialVelocity_apply]
    by_cases included:wave∈modes M
    · have covered:wave∈ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay.wholeRestartModes M:=included
      rw [if_pos covered,if_pos included,NativeEndpointVelocityCarrier.wholeVelocity_nonzero v ⟨wave,zero⟩]
    · have covered:wave∉ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay.wholeRestartModes M:=included
      rw [if_neg covered,if_neg included]
      rfl

theorem native_rate_row (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time)
    (wave : NonzeroIntegerWavevector) :
    NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowEvolution.velocityJet seed 1 time) wave.1=
      NativeCompleteAction.momentum nu (NativeForwardWindowSource.source seed time) wave.1 := by
  have actual:=congrArg (fun v : NativeResolventCompactness.State => integerWaveNormSq wave.1^2 • v wave)
    (NativeForwardWindowEvolution.source_physical_rate seed time valid)
  rw [NativeNegativeFourMomentum.embed_reconstruct,NativeCompleteActionOperator.momentum_complete_row,
    NativeCompleteFilteredWrite.decode_weighted_row] at actual
  funext i
  exact (NativeEndpointVelocityCarrier.wholeVelocity_nonzero _ wave i).trans
    (congrArg (fun v => v i) actual)

theorem complete_stress_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (valid : -1 < time)
    (wave : IntegerWavevector) :
    NativeEndpointVelocityCarrier.wholeVelocity
      (mean (finiteHistory seed time M)-commonForce seed M time+
        mean (xMixed seed M time)+mean (wSelf seed M time)+mean (forcingHistory seed M time)).1 wave=
      if wave∈modes M then NativeCompleteAction.momentum nu (NativeForwardWindowSource.source seed time) wave else 0 := by
  have original:=(congrArg (fun v : wholePhysical => v.1) (source_momentum seed M time)).symm.trans
    (NativeWindowHistoryMeanTime.source_rate seed M time)
  have projected:=(congrArg (fun v : NativeResolventCompactness.State => NativeEndpointVelocityCarrier.wholeVelocity v wave) original).trans
    (read_wave M (NativeForwardWindowEvolution.velocityJet seed 1 time) wave)
  apply projected.trans
  by_cases included:wave∈modes M
  · rw [if_pos included,if_pos included]
    exact native_rate_row seed time valid ⟨wave,fun zero => modes_zero M (zero ▸ included)⟩
  · rw [if_neg included,if_neg included]

theorem mean_square_le (v : H) : ‖mean v‖^2 ≤ ‖v‖^2 := by
  have split:=NativeWindowHistoryMeanProjection.energy_split v
  have same:‖NativeWindowHistoryMeanProjection.projection v‖=‖mean v‖:=NativeWindowHistoryMeanProjection.embed_norm _
  rw [same] at split
  nlinarith only [split,sq_nonneg ‖NativeWindowHistoryMeanProjection.residual v‖]

theorem source_joint_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖xJoint seed M time‖^2 ≤ epsilon*‖NativeWindowHistoryAnnihilationControl.laplacianAction nu M
        (finiteHistory seed time M)‖^2+C := by
  obtain ⟨low,K,K0,source⟩:=NativeWindowHistorySchurTranspose.source_graph_bound seed horizon nonnegative epsilon positive
  refine ⟨low,K*NativeWindowHistorySchurTemporalControl.massBudget seed,
    mul_nonneg K0 (NativeWindowHistorySchurTemporalControl.massBudget_nonnegative seed),fun M above time inside => ?_⟩
  have bounded:=(source M above time inside (finiteHistory seed time M)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (NativeWindowHistorySchurTemporalControl.source_mass seed M time inside.1) K0))
  exact (congrArg (fun v : H => ‖v‖^2) (xJoint_transpose seed M time)).trans_le bounded

theorem source_mean_joint_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ M ≥ low,∀ time∈Icc 0 horizon,
      ‖mean (finiteHistory seed time M)-diffusion nu M (mean (finiteHistory seed time M))-commonForce seed M time‖^2 ≤
        epsilon*‖NativeWindowHistoryAnnihilationControl.laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  obtain ⟨low,C,C0,source⟩:=source_joint_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above time inside => ?_⟩
  exact (congrArg (fun v : wholePhysical => ‖v‖^2) (xJoint_mean seed M time)).symm.trans_le
    ((mean_square_le (xJoint seed M time)).trans (source M above time inside))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem terms_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (xJoint seed M (step.2.clockAdvance+time),xMixed seed M (step.2.clockAdvance+time),wSelf seed M (step.2.clockAdvance+time))=
      (xJoint step.1 M time,xMixed step.1 M time,wSelf step.1 M time) := by
  have actions:=NativeWindowHistorySchurAdvectorAction.actions_next seed M step generated time nonnegative
  have first:=congrArg Prod.fst actions
  have last:=congrArg Prod.snd actions
  change xAction seed M (step.2.clockAdvance+time)=xAction step.1 M time at first
  change wAction seed M (step.2.clockAdvance+time)=wAction step.1 M time at last
  simp only [xJoint,xMixed,wSelf,first,last,NativeWindowHistorySchurCompletion.completion_next seed M step generated time nonnegative,
    NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurMomentum
