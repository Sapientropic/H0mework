import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip

open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology

open private forward_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeGramSource

local notation "F" => fourierL2
local notation "T" => burnolTateReciprocalL2
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "K" => burnolCompletedMellinRieszVector
local notation "lead" => ForcingPrimitive.leadingCoefficient

private theorem forward_source_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N => FiniteForcing.source N (K c : BurnolL2)) atTop
      (𝓝 (unitResolventSource c ConstantForward.value - F (CountingDual.value c) +
        ReturnCounting.forwardValue c)) := by
  have fourier := (fourierL2.continuous.tendsto _).comp (CountingDual.original_dual_tendsto c)
  have total := ((WholeGramSource.elementary_forward_tendsto c).sub fourier).add
    (ReturnCounting.forward_tendsto c)
  rw [← sourceKernel_original]
  apply total.congr'
  filter_upwards with N
  change _ = CountingDual.sourceCLM N (sourceKernel c)
  rw [sourceKernel, map_sub, map_add]
  simp only [CountingDual.sourceCLM_apply, forward_fourier]
  change FiniteForcing.source N (elementarySource c) -
    F (DualSource.source N (E (sourceB c : Hq))) +
      FiniteForcing.source N (E (sourceSB c : Hq)) =
    FiniteForcing.source N (elementarySource c) +
      FiniteForcing.source N (E (sourceSB c : Hq)) -
      F (DualSource.source N (E (sourceB c : Hq)))
  module

theorem actual_original_K_forward (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N => FiniteForcing.source N (K c : BurnolL2)) atTop
      (𝓝 (KCountingGram.value c)) := by
  rw [show KCountingGram.value c = _ from (forward_source_limit c).limUnder_eq]
  exact forward_source_limit c

private theorem unit_pair (c : BurnolCompletedMellinCoordinate) :
    poissonPair (unitResolventSource c ConstantForward.value) =
      freeUnit (star c.value) ConstantDual.value := by
  have seed : poissonPair ConstantForward.value = ConstantDual.value := by
    change T (F ConstantForward.value) = ConstantDual.value
    rw [ConstantFourier.original_square, burnolTateReciprocalL2_involutive]
  rw [← actual_free_unit c ConstantDual.value]
  simp only [unitResolventSource, map_smul, map_sub, actual_poisson_source_resolvent, seed]

private theorem dual_pair (c : BurnolCompletedMellinCoordinate) :
    poissonPair (F (CountingDual.value c)) = T (CountingDual.value c) := by
  have even : reflectL2 (CountingDual.value c) = CountingDual.value c :=
    burnolReflectL2_eq_of_even_raw _ _ (DualLanding.original_coeFn c) (fun x => by
      simp only [DualSourceRaw.eventRaw, DualSourceRaw.channels, abs_neg])
  change T (F (F (CountingDual.value c))) = T (CountingDual.value c)
  rw [fourierL2_fourierL2, even]

/-- The two actual K counting directions share the full base at every coordinate. -/
theorem actual_K_paired_base (c : BurnolCompletedMellinCoordinate) :
    poissonPair (KCountingGram.value c) = baseLimit c - T (CountingDual.value c) := by
  rw [show KCountingGram.value c = _ from (forward_source_limit c).limUnder_eq]
  rw [map_add, map_sub, unit_pair, dual_pair, ← actual_return_paired_value, baseLimit]
  module

theorem actual_original_K_reverse (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N => DualSource.source N (K c : BurnolL2)) atTop
      (𝓝 (poissonPair (KCountingGram.value c))) := by
  have forward := (fourierL2.continuous.tendsto (AmbientCounting.value c)).comp (AmbientCounting.original_ambient_limit c)
  have actual := (actual_base_tendsto c).sub forward
  have dual : F (AmbientCounting.value c) = T (CountingDual.value c) := by
    rw [DualLanding.original_tate_fourier, burnolTateReciprocalL2_involutive]
  rw [dual, ← actual_K_paired_base] at actual
  exact actual.congr' (Eventually.of_forall (fun N => (KCounting.original_finite c N).symm))

/-- The original K consumer uses the complete floor on the whole right strip. -/
theorem actual_original_K_counted_response_all (c : BurnolCompletedMellinCoordinate) :
    F (KCountingGram.value c) = -T (floorFromResponses c) +
      lead c • F (logProgramme c) - CountingDual.value c := by
  have actual := congrArg T (actual_K_paired_base c)
  change T (T (F (KCountingGram.value c))) = T (baseLimit c - T (CountingDual.value c)) at actual
  rw [burnolTateReciprocalL2_involutive, map_sub, burnolTateReciprocalL2_involutive] at actual
  have logRead : T (poissonPair (logProgramme c)) = F (logProgramme c) :=
    burnolTateReciprocalL2_involutive _
  rw [actual_floor_base, map_sub, map_smul, logRead, actual]
  module

/-- The actual K field keeps the source coefficient in its exterior read. -/
theorem actual_original_K_exterior (c : BurnolCompletedMellinCoordinate) :
    let paired := T (F (KCountingGram.value c) - lead c • F (logProgramme c) + CountingDual.value c)
    ∀ᵐ x ∂volume, (1/4 : ℝ) < |x| →
      paired x = (1/2 : ℂ)*(((|x| : ℝ) : ℂ)^(-star c.value))*riemannZeta (star c.value) := by
  have strip := actual_original_K_counted_response_all c
  have complete : F (KCountingGram.value c) - lead c • F (logProgramme c) + CountingDual.value c =
      -T (floorFromResponses c) := by
    rw [strip]
    module
  dsimp only
  rw [complete, map_neg, burnolTateReciprocalL2_involutive]
  filter_upwards [Lp.coeFn_neg (floorFromResponses c), actual_floor_exterior c]
    with x negative exterior outside
  rw [negative, Pi.neg_apply, exterior outside]
  change - (-(1/2 : ℂ)*(((|x| : ℝ) : ℂ)^(-star c.value))*riemannZeta (star c.value)) = _
  ring

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
