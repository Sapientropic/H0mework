import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.CompactC1
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction OriginalKCoefficientBFiniteAction
open OriginalKSourceResolventReconstruction OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open scoped Topology InnerProductSpace
open private forward_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource
local notation "T" => burnolTateReciprocalL2
local notation "F" => fourierL2
local notation "D" => burnolMultiplicativeDilation
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension

private theorem poisson_dilation (h : ℝ) (value : BurnolL2) :
    poissonPair (D h value) = D h (poissonPair value) := by
  change T (F (D h value)) = D h (T (F value))
  rw [fourierL2_burnolMultiplicativeDilation, burnolTateReciprocalL2_dilation_inverse]

/-- The actual Poisson pair commutes with the full original resolvent integral. -/
theorem actual_poisson_source_resolvent (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    poissonPair (sourceResolvent coordinate value) = sourceResolvent coordinate (poissonPair value) := by
  have right : 1 / 4 < (star coordinate.value / 2).re := by
    rw [Complex.div_re]
    simp only [Complex.star_def, Complex.conj_re]
    norm_num
    linarith [coordinate.rightHalf]
  have domain := burnolDirectRightResolventIntegrand_integrableOn (star coordinate.value / 2) right value
  change poissonPair (burnolDirectRightResolvent (star coordinate.value / 2) value) =
    burnolDirectRightResolvent (star coordinate.value / 2) (poissonPair value)
  rw [burnolDirectRightResolvent, map_neg, ← poissonPair.integral_comp_comm domain]
  congr 1
  apply integral_congr_ae
  filter_upwards with h
  simp only [burnolDirectRightResolventIntegrand, map_smul, poisson_dilation]

private theorem poisson_unit_source (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    poissonPair (unitResolventSource coordinate value) = unitResolventSource coordinate (poissonPair value) := by
  simp only [unitResolventSource, map_smul, map_sub, actual_poisson_source_resolvent]

/-- The two return values are identified by their actual compact source graphs, before the whole K is assembled. -/
theorem actual_return_paired_value (coordinate : BurnolCompletedMellinCoordinate) :
    ReturnCounting.value coordinate = poissonPair (ReturnCounting.forwardValue coordinate) := by
  let raw := burnolRieszReturnRaw coordinate
  have even (x : ℝ) (_inside : x ∈ symmetricInterval q) : raw |x| = raw x := by
    by_cases positive : 0 ≤ x
    · rw [abs_of_nonneg positive]
    · rw [abs_of_neg (lt_of_not_ge positive)]
      exact return_raw_even coordinate x
  have inputs := actual_compact_c1_inputs (Constructor.returnState coordinate : Hq) raw
    (burnolRieszReturnRawDerivative coordinate) (Constructor.returnState_read coordinate) even
    (burnolRieszReturnRaw_continuous coordinate).measurable
    (burnolRieszReturnRaw_continuous coordinate).continuousOn
    (burnolRieszReturnRawDerivative_continuous coordinate).continuousOn
    (fun x _ _ => burnolRieszReturnRaw_hasDerivAt coordinate x)
  obtain ⟨weightDerivative, slopeContinuous, measured, domain, head⟩ := inputs
  have forward := actual_compact_forward (Constructor.returnState coordinate : Hq) raw
    (Constructor.returnState_read coordinate) even weightDerivative slopeContinuous measured domain head
  have reverse := actual_compact_reverse (Constructor.returnState coordinate : Hq) raw
    (Constructor.returnState_read coordinate) even weightDerivative slopeContinuous domain head
  have forwardValue := tendsto_nhds_unique (ReturnCounting.forward_tendsto coordinate) forward
  have reverseValue := tendsto_nhds_unique (ReturnCounting.finite_tendsto coordinate) reverse
  rw [← forwardValue] at reverseValue
  exact reverseValue

private theorem actual_counted_K_source (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    KCountingGram.value coordinate = unitResolventSource coordinate ConstantForward.value -
      F (CountingDual.value coordinate) + ReturnCounting.forwardValue coordinate := by
  have total := ((WholeGramSource.elementary_forward_tendsto coordinate).sub
    ((fourierL2.continuous.tendsto _).comp (CountingDual.original_dual_tendsto coordinate))).add
      (ReturnCounting.forward_tendsto coordinate)
  have actual : Tendsto (fun N : ℕ => FiniteForcing.source N (sourceKernel coordinate)) atTop
      (𝓝 (unitResolventSource coordinate ConstantForward.value -
        F (CountingDual.value coordinate) + ReturnCounting.forwardValue coordinate)) := by
    apply total.congr'
    filter_upwards with N
    change _ = CountingDual.sourceCLM N (sourceKernel coordinate)
    rw [sourceKernel, map_sub, map_add]
    simp only [CountingDual.sourceCLM_apply, forward_fourier]
    change FiniteForcing.source N (elementarySource coordinate) -
      F (DualSource.source N (E (sourceB coordinate : Hq))) +
      FiniteForcing.source N (E (sourceSB coordinate : Hq)) =
      FiniteForcing.source N (elementarySource coordinate) +
        FiniteForcing.source N (E (sourceSB coordinate : Hq)) -
        F (DualSource.source N (E (sourceB coordinate : Hq)))
    module
  rw [sourceKernel_original] at actual
  exact tendsto_nhds_unique (KCountingGram.forward_tendsto coordinate zero) actual

/-- This is the equality of the complete independently generated K values, including both Unit directions. -/
theorem actual_original_K_paired_value (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    -PositionCounting.value coordinate zero - T (CountingDual.value coordinate) =
      poissonPair (KCountingGram.value coordinate) := by
  have constant : poissonPair ConstantForward.value = ConstantDual.value := by
    change T (F ConstantForward.value) = ConstantDual.value
    rw [ConstantFourier.original_square, burnolTateReciprocalL2_involutive]
  have even : reflectL2 (CountingDual.value coordinate) = CountingDual.value coordinate :=
    burnolReflectL2_eq_of_even_raw _ _ (DualLanding.original_coeFn coordinate) (fun x => by
      simp only [DualSourceRaw.eventRaw, DualSourceRaw.channels, abs_neg])
  have pairedFourier : poissonPair (F (CountingDual.value coordinate)) = T (CountingDual.value coordinate) := by
    change T (F (F (CountingDual.value coordinate))) = T (CountingDual.value coordinate)
    rw [fourierL2_fourierL2, even]
  rw [actual_counted_K_source coordinate zero, map_add, map_sub, poisson_unit_source, constant,
    pairedFourier, ← actual_return_paired_value]
  have elementary := elementary_reverse_unit_resolvent coordinate zero
  unfold elementaryReverseSource at elementary
  linear_combination (norm := module) elementary

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
