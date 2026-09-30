import H0mework.NavierStokes.VelocityEndpoint.WholeMildReadWrite
import H0mework.NavierStokes.Crossing.TangentCoercivity

/-!
# Complete physical right trace of the generated velocity endpoint

The endpoint mild compiler already writes every Fourier row continuously.
This module retains the exact Euclidean row mass of the same actual Galerkin
events before passing to the whole-state limit.  The resulting pointwise
whole-path ceiling upgrades the local time-zero read to a strong physical
right trace; no cutoff, target path, continuity certificate, or tail bound is
accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace

open scoped BigOperators ENNReal Topology

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointLerayHopfReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity

noncomputable section

/-! ## Exact Euclidean mass retained from the Galerkin producer -/

/-- Any finite inventory of one actual Galerkin velocity state is paid in
the physical Euclidean row norm by the source endpoint kinetic square. -/
theorem generatedVelocityEndpointGalerkinWholeState_amplitude_finset_le_endpoint
    {nu : Viscosity}
    (ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        nu)
    (radius : ℕ)
    (time : Icc (0 : ℝ) 1)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        complexCoordinateAmplitudeSq
          (generatedVelocityEndpointGalerkinWholeState
            ledger radius time wave)) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  let state := (ledger.family.stage radius).trajectory time.1
  let velocityState :=
    generatedVelocityEndpointGalerkinWholeState ledger radius time
  have supported :
      ∀ wave, wave ∉ wholeRestartModes radius → velocityState wave = 0 := by
    intro wave waveNotMem
    simp [velocityState,
      generatedVelocityEndpointGalerkinWholeState_apply, waveNotMem]
  have amplitudeSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq (velocityState wave) := by
    apply summable_of_ne_finset_zero (s := wholeRestartModes radius)
    intro wave waveNotMem
    rw [supported wave waveNotMem]
    simp [complexCoordinateAmplitudeSq]
  have finiteLeFull :
      (∑ wave ∈ waves,
          complexCoordinateAmplitudeSq (velocityState wave)) ≤
        ∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (velocityState wave) :=
    amplitudeSummable.sum_le_tsum waves fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg (velocityState wave)
  have fullEq :
      (∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (velocityState wave)) =
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) velocityState := by
    rw [tsum_eq_sum (s := wholeRestartModes radius)
      (fun wave waveNotMem => by
        rw [supported wave waveNotMem]
        simp [complexCoordinateAmplitudeSq])]
    rfl
  have coefficientEq :
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) velocityState =
        2 * finiteStateVorticityKineticEnergy
          (wholeRestartModes radius) state := by
    rw [← velocityRowAmplitude_sq_sum_eq_two_kineticEnergy
      (wholeRestartModes radius) state]
    unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [velocityRowAmplitude_sq]
    simp [velocityState, state,
      generatedVelocityEndpointGalerkinWholeState_apply, waveMem]
  change
    (∑ wave ∈ waves,
        complexCoordinateAmplitudeSq (velocityState wave)) ≤ _
  calc
    (∑ wave ∈ waves,
        complexCoordinateAmplitudeSq (velocityState wave)) ≤
        ∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (velocityState wave) := finiteLeFull
    _ = finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) velocityState := fullEq
    _ = 2 * finiteStateVorticityKineticEnergy
          (wholeRestartModes radius) state := coefficientEq
    _ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
      nlinarith [ledger.kinetic_energy_le radius time]

/-- Taking the same-lineage Galerkin limit preserves that exact physical
Euclidean payment on every finite inventory of canonical mild rows. -/
theorem velocityEndpointWholeMildCoefficient_amplitude_finset_le_endpoint
    {nu : Viscosity}
    {ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1)
    (waves : Finset IntegerWavevector) :
    (∑ wave ∈ waves,
        complexCoordinateAmplitudeSq
          (velocityEndpointWholeMildCoefficient receipt time wave)) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  have finiteSumTendsto :
      Tendsto
        (fun index =>
          ∑ wave ∈ waves,
            complexCoordinateAmplitudeSq
              (generatedVelocityEndpointGalerkinWholeState ledger
                (receipt.subsequence index) time wave))
        atTop
        (nhds
          (∑ wave ∈ waves,
            complexCoordinateAmplitudeSq
              (velocityEndpointWholeMildCoefficient receipt time wave))) := by
    apply tendsto_finsetSum
    intro wave waveMem
    exact
      (complexCoordinateAmplitudeSq_continuous.tendsto _).comp
        (generatedVelocityEndpointGalerkinWholeState_tendsto_mildCoefficient
          receipt time wave)
  apply le_of_tendsto finiteSumTendsto
  exact Filter.Eventually.of_forall fun index =>
    generatedVelocityEndpointGalerkinWholeState_amplitude_finset_le_endpoint
      ledger (receipt.subsequence index) time waves

theorem velocityEndpointWholeMildCoefficient_amplitude_summable
    {nu : Viscosity}
    {ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    Summable fun wave : IntegerWavevector =>
      complexCoordinateAmplitudeSq
        (velocityEndpointWholeMildCoefficient receipt time wave) := by
  apply summable_of_sum_le
    (fun wave => complexCoordinateAmplitudeSq_nonneg
      (velocityEndpointWholeMildCoefficient receipt time wave))
  intro waves
  exact velocityEndpointWholeMildCoefficient_amplitude_finset_le_endpoint
    receipt time waves

theorem velocityEndpointWholeMildCoefficient_amplitude_tsum_le_endpoint
    {nu : Viscosity}
    {ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    (∑' wave : IntegerWavevector,
        complexCoordinateAmplitudeSq
          (velocityEndpointWholeMildCoefficient receipt time wave)) ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  apply le_of_tendsto
    (velocityEndpointWholeMildCoefficient_amplitude_summable
      receipt time).hasSum
  exact Filter.Eventually.of_forall fun waves =>
    velocityEndpointWholeMildCoefficient_amplitude_finset_le_endpoint
      receipt time waves

/-- The endpoint write therefore has the exact whole physical velocity
ceiling after Euclideanization; the previous factor-three observer loss is
absent. -/
theorem velocityEndpointWholeMildState_physical_norm_sq_le_endpoint
    {nu : Viscosity}
    {ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointLerayHopfCoreReceipt ledger)
    (time : Icc (0 : ℝ) 1) :
    ‖puncturedEuclideanize
        (velocityEndpointWholeMildState receipt time)‖ ^ 2 ≤
      ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 := by
  rw [puncturedEuclideanize_norm_sq]
  exact
    (Summable.tsum_subtype_le
      (fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq
          (velocityEndpointWholeMildCoefficient receipt time wave))
      {wave : IntegerWavevector | wave ≠ 0}
      (fun wave => complexCoordinateAmplitudeSq_nonneg
        (velocityEndpointWholeMildCoefficient receipt time wave))
      (velocityEndpointWholeMildCoefficient_amplitude_summable
        receipt time)).trans
      (velocityEndpointWholeMildCoefficient_amplitude_tsum_le_endpoint
        receipt time)

/-! ## Strong local-zero trace on the complete physical carrier -/

private def endpointPhysicalFiniteProjection
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    WholeRestartVelocityEndpointState :=
  ∑ wave ∈ modes, lp.single 2 wave (state wave)

private def endpointPhysicalFiniteTail
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    WholeRestartVelocityEndpointState :=
  state - endpointPhysicalFiniteProjection modes state

private theorem endpointPhysicalFiniteTail_norm_sq
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    ‖endpointPhysicalFiniteTail modes state‖ ^ 2 =
      ‖state‖ ^ 2 - ‖endpointPhysicalFiniteProjection modes state‖ ^ 2 := by
  classical
  have complementEq :=
    lp.norm_compl_sum_single
      (p := (2 : ENNReal)) (by norm_num) state modes
  have projectionEq :=
    lp.norm_sum_single
      (p := (2 : ENNReal)) (by norm_num)
      (fun wave => state wave) modes
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at complementEq projectionEq
  calc
    ‖endpointPhysicalFiniteTail modes state‖ ^ 2 =
        ‖state‖ ^ 2 - ∑ wave ∈ modes, ‖state wave‖ ^ 2 := by
      simpa only [endpointPhysicalFiniteTail,
        endpointPhysicalFiniteProjection] using complementEq
    _ = ‖state‖ ^ 2 -
        ‖endpointPhysicalFiniteProjection modes state‖ ^ 2 := by
      simpa only [endpointPhysicalFiniteProjection] using
        congrArg (fun value => ‖state‖ ^ 2 - value) projectionEq.symm

private theorem wholeRestartVelocityEndpointState_tendsto_of_coordinatewise_of_norm_sq_le
    {β : Type*}
    {filter : Filter β}
    [NeBot filter]
    (path : β → WholeRestartVelocityEndpointState)
    (endpoint : WholeRestartVelocityEndpointState)
    (coordinateTendsto :
      ∀ wave : NonzeroIntegerWavevector,
        Tendsto (fun index => path index wave) filter (nhds (endpoint wave)))
    (normBound :
      ∀ᶠ index in filter, ‖path index‖ ^ 2 ≤ ‖endpoint‖ ^ 2) :
    Tendsto path filter (nhds endpoint) := by
  classical
  have finiteProjectionTendsto
      (modes : Finset NonzeroIntegerWavevector) :
      Tendsto
        (fun index => endpointPhysicalFiniteProjection modes (path index))
        filter
        (nhds (endpointPhysicalFiniteProjection modes endpoint)) := by
    unfold endpointPhysicalFiniteProjection
    apply tendsto_finsetSum modes
    intro wave _waveMem
    exact
      (lp.singleContinuousLinearMap
        ℂ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean)
        2 wave).continuous.tendsto _ |>.comp
          (coordinateTendsto wave)
  have endpointProjectionTendsto :
      Tendsto
        (fun modes : Finset NonzeroIntegerWavevector =>
          endpointPhysicalFiniteProjection modes endpoint)
        atTop
        (nhds endpoint) := by
    change
      Tendsto
        (fun modes : Finset NonzeroIntegerWavevector =>
          ∑ wave ∈ modes, lp.single 2 wave (endpoint wave))
        atTop
        (nhds endpoint)
    exact
      lp.hasSum_single
        (p := (2 : ENNReal)) (by norm_num) endpoint
  have endpointTailTendsto :
      Tendsto
        (fun modes : Finset NonzeroIntegerWavevector =>
          endpointPhysicalFiniteTail modes endpoint)
        atTop
        (nhds 0) := by
    have constantTendsto :
        Tendsto
          (fun _ : Finset NonzeroIntegerWavevector => endpoint)
          atTop
          (nhds endpoint) :=
      tendsto_const_nhds
    have difference := constantTendsto.sub endpointProjectionTendsto
    simpa only [endpointPhysicalFiniteTail, sub_self] using difference
  rw [Metric.tendsto_nhds]
  intro epsilon epsilonPos
  let quarter := epsilon / 4
  let half := epsilon / 2
  let delta := epsilon ^ 2 / 32
  have quarterPos : 0 < quarter := by
    dsimp only [quarter]
    positivity
  have halfPos : 0 < half := by
    dsimp only [half]
    positivity
  have deltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have endpointTailEventually :
      ∀ᶠ modes : Finset NonzeroIntegerWavevector in atTop,
        ‖endpointPhysicalFiniteTail modes endpoint‖ < quarter := by
    have close :=
      (Metric.tendsto_nhds.mp endpointTailTendsto) quarter quarterPos
    filter_upwards [close] with modes modesClose
    simpa only [dist_zero_right] using modesClose
  obtain ⟨modes, endpointTailSmall⟩ := endpointTailEventually.exists
  have headEventually :
      ∀ᶠ index in filter,
        dist
            (endpointPhysicalFiniteProjection modes (path index))
            (endpointPhysicalFiniteProjection modes endpoint) < quarter :=
    (Metric.tendsto_nhds.mp (finiteProjectionTendsto modes))
      quarter quarterPos
  have projectionSquareTendsto :
      Tendsto
        (fun index =>
          ‖endpointPhysicalFiniteProjection modes (path index)‖ ^ 2)
        filter
        (nhds (‖endpointPhysicalFiniteProjection modes endpoint‖ ^ 2)) :=
    (finiteProjectionTendsto modes).norm.pow 2
  have projectionSquareEventually :
      ∀ᶠ index in filter,
        dist
            (‖endpointPhysicalFiniteProjection modes (path index)‖ ^ 2)
            (‖endpointPhysicalFiniteProjection modes endpoint‖ ^ 2) <
          delta :=
    (Metric.tendsto_nhds.mp projectionSquareTendsto) delta deltaPos
  filter_upwards [headEventually, projectionSquareEventually, normBound] with
      index headSmall projectionSquareClose totalSquareUpper
  have projectionSquareLower :
      ‖endpointPhysicalFiniteProjection modes endpoint‖ ^ 2 - delta <
        ‖endpointPhysicalFiniteProjection modes (path index)‖ ^ 2 := by
    rw [Real.dist_eq, abs_lt] at projectionSquareClose
    linarith [projectionSquareClose.1]
  have endpointTailSquareSmall :
      ‖endpointPhysicalFiniteTail modes endpoint‖ ^ 2 < quarter ^ 2 := by
    nlinarith [norm_nonneg (endpointPhysicalFiniteTail modes endpoint)]
  have pathTailSquareSmall :
      ‖endpointPhysicalFiniteTail modes (path index)‖ ^ 2 < half ^ 2 := by
    have pathTailIdentity :=
      endpointPhysicalFiniteTail_norm_sq modes (path index)
    have endpointTailIdentity :=
      endpointPhysicalFiniteTail_norm_sq modes endpoint
    dsimp only [delta, quarter, half] at projectionSquareLower
    dsimp only [delta, quarter, half] at endpointTailSquareSmall
    dsimp only [delta, quarter, half]
    nlinarith
  have pathTailSmall :
      ‖endpointPhysicalFiniteTail modes (path index)‖ < half := by
    nlinarith [norm_nonneg (endpointPhysicalFiniteTail modes (path index))]
  have decomposition :
      path index - endpoint =
        (endpointPhysicalFiniteProjection modes (path index) -
            endpointPhysicalFiniteProjection modes endpoint) +
          (endpointPhysicalFiniteTail modes (path index) -
            endpointPhysicalFiniteTail modes endpoint) := by
    unfold endpointPhysicalFiniteTail
    abel
  rw [dist_eq_norm, decomposition]
  calc
    ‖(endpointPhysicalFiniteProjection modes (path index) -
          endpointPhysicalFiniteProjection modes endpoint) +
        (endpointPhysicalFiniteTail modes (path index) -
          endpointPhysicalFiniteTail modes endpoint)‖ ≤
        ‖endpointPhysicalFiniteProjection modes (path index) -
          endpointPhysicalFiniteProjection modes endpoint‖ +
        ‖endpointPhysicalFiniteTail modes (path index) -
          endpointPhysicalFiniteTail modes endpoint‖ := norm_add_le _ _
    _ ≤
        ‖endpointPhysicalFiniteProjection modes (path index) -
          endpointPhysicalFiniteProjection modes endpoint‖ +
          (‖endpointPhysicalFiniteTail modes (path index)‖ +
            ‖endpointPhysicalFiniteTail modes endpoint‖) :=
      add_le_add le_rfl (norm_sub_le _ _)
    _ < quarter + (half + quarter) := by
      rw [dist_eq_norm] at headSmall
      exact add_lt_add headSmall
        (add_lt_add pathTailSmall endpointTailSmall)
    _ = epsilon := by
      dsimp only [quarter, half]
      ring

/-- The pointwise mild write is strongly right-continuous at its actual
source-generated initial state on the complete physical velocity carrier.
The conclusion is generated by finite-row continuity plus the exact whole
Euclidean mass ceiling above, not by a supplied tail or continuation law. -/
theorem velocityEndpointWholeMildReadWrite_physical_tendsto_initial
    {nu : Viscosity}
    {ledger :
      GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore
        nu}
    (receipt :
      GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) :
    Tendsto
      (fun time : Icc (0 : ℝ) 1 =>
        puncturedEuclideanize (receipt.wholePath time))
      (nhds (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1))
      (nhds ledger.family.endpointReceipt.velocityEndpoint) := by
  let zeroTime : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  have coordinateTendsto
      (wave : NonzeroIntegerWavevector) :
      Tendsto
        (fun time : Icc (0 : ℝ) 1 =>
          puncturedEuclideanize (receipt.wholePath time) wave)
        (nhds zeroTime)
        (nhds (ledger.family.endpointReceipt.velocityEndpoint wave)) := by
    have rowTendsto :
        Tendsto (fun time => receipt.wholePath time wave.1)
          (nhds zeroTime)
          (nhds (receipt.wholePath zeroTime wave.1)) :=
      (receipt.coordinate_continuous wave.1).continuousAt
    have euclideanTendsto :
        Tendsto
          (fun time =>
            WithLp.toLp 2 (receipt.wholePath time wave.1))
          (nhds zeroTime)
          (nhds
            (WithLp.toLp 2 (receipt.wholePath zeroTime wave.1))) :=
      (PiLp.continuous_toLp
        (p := (2 : ENNReal))
        (β := fun _ : Coordinate => ℂ)).tendsto _ |>.comp rowTendsto
    have initialRow :
        euclideanCoordinateRow (receipt.wholePath zeroTime wave.1) =
          ledger.family.endpointReceipt.velocityEndpoint wave := by
      rw [receipt.initial_row wave.1]
      rw [wholeRestartVelocityEndpointCoefficient_of_ne
        ledger.family.endpointReceipt.velocityEndpoint wave.1 wave.2]
      rfl
    rw [← initialRow]
    simpa only [puncturedEuclideanize_apply, euclideanCoordinateRow] using
      euclideanTendsto
  have normBound :
      ∀ᶠ time : Icc (0 : ℝ) 1 in nhds zeroTime,
        ‖puncturedEuclideanize (receipt.wholePath time)‖ ^ 2 ≤
          ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 :=
    Filter.Eventually.of_forall fun time => by
      rw [receipt.wholePath_apply]
      exact
        velocityEndpointWholeMildState_physical_norm_sq_le_endpoint
          receipt.core time
  exact
    wholeRestartVelocityEndpointState_tendsto_of_coordinatewise_of_norm_sq_le
      (fun time => puncturedEuclideanize (receipt.wholePath time))
      ledger.family.endpointReceipt.velocityEndpoint
      coordinateTendsto normBound

/-- The original root's true-cofinal whole write has a strong physical
right trace at the endpoint carried by that exact source occurrence. -/
theorem
    sourceGeneratedNativeTemporalWholeMildReadWrite_physical_tendsto_initial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto
      (fun time : Icc (0 : ℝ) 1 =>
        puncturedEuclideanize
          ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
            initial).wholePath time))
      (nhds (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1))
      (nhds
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt
          initial).velocityEndpoint) := by
  exact
    velocityEndpointWholeMildReadWrite_physical_tendsto_initial
      (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
end NavierStokes
end SaturationMonoid
