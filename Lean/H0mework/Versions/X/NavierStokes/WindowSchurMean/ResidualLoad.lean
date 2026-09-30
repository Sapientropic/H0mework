import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.InverseSourceSlots
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Half
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Mean

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanResidualLoad
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanPhysicalJet (physicalJet)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowHistorySchurAction (feedback)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
open NativeWindowHistoryAdjointSpatialHalf (moment outputSquare)
open NativeWindowHistoryAdjointSpatialFeedback (transportCap transportCap_nonnegative)
open NativeUnheatedSexticLatticePower (radical)
noncomputable section
variable {nu : Viscosity}

theorem jet_zero_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    physicalJet seed M 0 time=NativeWindowHistoryMeanAction.meanValue seed M time := by
  rw [NativeWindowHistoryMeanPhysicalJet.physicalJet_zero]
  exact NativeWindowHistoryCreationHalf.mean_restrict seed M time

theorem include_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (physicalJet seed M 0 time)=mean (finiteHistory seed time M) := by
  rw [NativeWindowHistoryMeanPhysicalJet.physicalJet_zero,NativeWindowHistoryMeanPhysicalJet.include_mean]

private theorem moment_two_le_three (F : Finset IntegerWavevector) (v : physicalSpace F) :
    moment F 2 v≤ moment F 3 v := by
  rw [NativeWindowHistoryAdjointSpatialHalf.moment_original,NativeWindowHistoryAdjointSpatialHalf.moment_original]
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact pow_le_pow_right₀ (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (NativeUnheatedSexticLatticePower.mass_one k))) (by norm_num)

private theorem strong_square (M : ℕ) (v : physicalSpace (modes M)) :
    outputSquare true (modes M) v=‖includeCLM (modes M) (modes_closed M) v‖^2 := by
  rw [include_norm (modes M) (modes_zero M)]
  have source:=(NativeWindowHistoryCreationGeometry.pairing_mass (modes M) v).symm.trans
    (real_inner_self_eq_norm_sq (coefficients (modes M) v))
  simpa only [NativeWindowHistoryAdjointSpatialHalf.outputSquare,NativeWindowHistoryAdjointSpatialHalf.weight,
    if_true,one_pow,one_mul] using source

def driftBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  transportCap*NativeWindowSobolevVelocity.budget seed 0 horizon*NativeWindowSobolevVelocity.budget seed order horizon

theorem source_drift_jet (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    ‖drift seed M time (includeCLM (modes M) (modes_closed M) (physicalJet seed M order time))‖^2≤
      driftBudget seed order horizon := by
  let u:=physicalJet seed M 0 time
  let v:=physicalJet seed M order time
  have source:=NativeWindowHistoryAdjointSpatialHalf.transport_bound true (modes M) (modes_zero M) (modes_closed M) nu u v
  rw [strong_square] at source
  have uPaid:=(moment_two_le_three (modes M) u).trans
    (NativeWindowHistoryCreationMean.mean_moment seed 0 horizon M time inside)
  have vPaid:=NativeWindowHistoryCreationMean.mean_moment seed order horizon M time inside
  have budget0 : 0≤NativeWindowSobolevVelocity.budget seed 0 horizon := by
    unfold NativeWindowSobolevVelocity.budget
    positivity
  have paid:=mul_le_mul uPaid vPaid (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative _ _ _) budget0
  rw [NativeWindowHistoryMeanDrift.drift_original,restrict_include,← jet_zero_mean]
  exact source.trans (by simpa only [driftBudget,transportCap,NativeWindowHistoryAdjointSpatialHalf.inputOrder,if_true,v,mul_assoc] using mul_le_mul_of_nonneg_left paid transportCap_nonnegative)

def feedbackBudget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  NativeWindowHistoryAdjointSpatialFeedback.budget seed horizon*NativeWindowHistoryMeanJetEnergy.budget seed order horizon

theorem source_feedback_jet (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ)
    (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon) :
    ‖feedback seed M time (includeCLM (modes M) (modes_closed M) (physicalJet seed M order time))‖^2≤
      feedbackBudget seed order horizon :=
  (NativeWindowHistoryAdjointSpatialFeedback.feedback_bound seed horizon M time inside _).trans
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryMeanJetEnergy.source_energy seed order horizon M time inside)
      (NativeWindowHistoryAdjointSpatialFeedback.budget_nonnegative seed horizon))

private theorem three_square {E : Type*} [SeminormedAddCommGroup E] (u v w : E) :
    ‖u-v-w‖^2≤3*(‖u‖^2+‖v‖^2+‖w‖^2) := by
  have t:=(norm_sub_le (u-v) w).trans (add_le_add (norm_sub_le u v) le_rfl)
  have s:=pow_le_pow_left₀ (norm_nonneg _) t 2
  nlinarith only [s,sq_nonneg (‖u‖-‖v‖),sq_nonneg (‖u‖-‖w‖),sq_nonneg (‖v‖-‖w‖)]

private theorem common_principal_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistorySchurCompletion.commonForce seed M time-
      nu.coeff • laplacianFiber nu M (mean (finiteHistory seed time M))=
        mean (finiteHistory seed time M)-drift seed M time (mean (finiteHistory seed time M))-
          feedback seed M time (mean (finiteHistory seed time M)) := by
  have source:=NativeWindowMeanEffectiveGraph.load_split seed M time (mean (finiteHistory seed time M))
  rw [NativeWindowMeanEffectiveGraph.source_load] at source
  rw [source]
  abel


def residualLoad (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : wholePhysical :=
  mean (NativeWindowHistoryOseen.forcingHistory seed M time)+
    NativeWindowHistoryMeanBlocks.annihilation seed M time (finiteHistory seed time M)

private theorem mean_balance_algebra {E : Type*} [AddCommGroup E] (r a c f l d : E)
    (source : r=a+c+f) (principal : a+l=d) : r+l=d+(f+c) := by
  rw [source,← principal]
  abel

theorem source_mean_balance (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    mean (NativeWindowHistoryOseen.rateHistory seed M time)+
      nu.coeff • laplacianFiber nu M (mean (finiteHistory seed time M))=
        drift seed M time (mean (finiteHistory seed time M))+residualLoad seed M time := by
  have actual:=congrArg mean (NativeWindowHistoryOseen.source_equation seed M time)
  rw [map_add,NativeWindowHistoryMeanBlocks.mean_action_split] at actual
  have linear:=NativeWindowMetricGraphMean.drift_read seed M time (mean (finiteHistory seed time M))
  change NativeWindowHistoryMeanAction.meanOperator seed M time (mean (finiteHistory seed time M))+
    nu.coeff • laplacianFiber nu M (mean (finiteHistory seed time M))=_ at linear
  exact mean_balance_algebra _ _ _ _ _ _ actual linear

theorem residual_covariance_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    residualLoad seed M time=mean (NativeWindowHistoryOseen.forcingHistory seed M time)+
      includeCLM (modes M) (modes_closed M)
        (∫lag,NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu
          (NativeWindowHistoryCreationCovariance.centered seed M time (time-lag))
          (NativeWindowHistoryCreationCovariance.centered seed M time (time-lag))
            ∂NativeForwardWindowPairingReadout.averageMeasure) := by
  unfold residualLoad
  congr 1
  rw [← NativeWindowHistorySchurCompletion.annihilation_residual seed M time (finiteHistory seed time M),
    ← NativeWindowHistoryAnnihilationRows.output_include,NativeWindowHistoryAnnihilationRows.output_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryCreationHalf.sample_centered seed M time] with lag actual
  change NativeWindowHistoryAnnihilationRows.input M
    (NativeWindowHistoryMeanProjection.residual (finiteHistory seed time M)) lag=_ at actual
  rw [actual]


theorem common_residual_read (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistorySchurCompletion.commonForce seed M time-residualLoad seed M time=
      mean (finiteHistory seed time M)-mean (NativeWindowHistoryOseen.rateHistory seed M time)-
        feedback seed M time (mean (finiteHistory seed time M)) := by
  have first:=common_principal_read seed M time
  have second:=source_mean_balance seed M time
  let w:=mean (finiteHistory seed time M)
  let r:=mean (NativeWindowHistoryOseen.rateHistory seed M time)
  let d:=drift seed M time w
  let b:=feedback seed M time w
  let l:=nu.coeff • laplacianFiber nu M w
  change NativeWindowHistorySchurCompletion.commonForce seed M time-l=w-d-b at first
  change r+l=d+residualLoad seed M time at second
  have actual : NativeWindowHistorySchurCompletion.commonForce seed M time=(w-d-b)+l := eq_add_of_sub_eq first
  have residual : residualLoad seed M time=(r+l)-d := eq_sub_of_add_eq' second.symm
  change _=w-r-b
  rw [actual,residual]
  abel

theorem source_retained_residual (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M time,time∈Icc 0 horizon →
      ‖NativeWindowHistorySourceResolventSlots.retainedLoad seed M time-residualLoad seed M time‖^2≤C := by
  let B:=3*(NativeForwardWindowJets.budget seed 0^2+NativeForwardWindowJets.budget seed 1^2+feedbackBudget seed 0 horizon)
  let D:=2*(NativeWindowHistorySourceResolventGraph.loadedBudget seed horizon 0+
    (1/4:ℝ)*NativeWindowHistorySourceResolventGraph.loadedBudget seed horizon 1)
  refine ⟨max 0 (2*(B+D)),le_max_left _ _,?_⟩
  intro M time inside
  have reg:=NativeWindowHistorySourceResolventSlots.source_regular_load_bound seed horizon M time inside
  have common : ‖NativeWindowHistorySchurCompletion.commonForce seed M time-residualLoad seed M time‖^2≤B := by
    rw [common_residual_read]
    have mass:=pow_le_pow_left₀ (norm_nonneg _) (NativeWindowHistoryMeanPhysicalJet.physicalJet_norm seed M 0 time) 2
    rw [← include_norm (modes M) (modes_zero M) (modes_closed M),include_zero] at mass
    have rate:=pow_le_pow_left₀ (norm_nonneg _) (NativeWindowHistoryMeanTime.source_rate_bound seed M time) 2
    have feed:=source_feedback_jet seed 0 horizon M time inside
    rw [include_zero] at feed
    exact (three_square _ _ _).trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add mass rate) feed) (by norm_num))
  let f:=NativeWindowHistorySchurCompletion.commonForce seed M time
  let r:=NativeWindowHistorySourceResolventSlots.retainedLoad seed M time
  let q:=residualLoad seed M time
  have split:r-q=(f-q)-(f-r):=by abel
  change ‖f-r‖^2≤D at reg
  change ‖f-q‖^2≤B at common
  change ‖r-q‖^2≤_
  rw [split]
  apply (show ‖(f-q)-(f-r)‖^2≤2*(B+D) from ?_).trans (le_max_right _ _)
  have triangle:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f-q) (f-r)) 2
  nlinarith only [common,reg,triangle,sq_nonneg (‖f-q‖-‖f-r‖)]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem residualLoad_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    residualLoad seed M (step.2.clockAdvance+time)=residualLoad step.1 M time := by
  have acted:=congrArg (fun blocks => blocks.2.2.1)
    (NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative)
  dsimp only at acted
  simp only [residualLoad,acted,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanResidualLoad
