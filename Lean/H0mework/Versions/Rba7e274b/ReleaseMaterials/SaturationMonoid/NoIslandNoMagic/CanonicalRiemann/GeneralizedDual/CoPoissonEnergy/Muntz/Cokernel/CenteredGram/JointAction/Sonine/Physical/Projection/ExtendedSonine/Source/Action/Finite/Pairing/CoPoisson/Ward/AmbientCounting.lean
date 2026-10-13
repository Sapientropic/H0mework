import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalSeed
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InfiniteWeightedProgram
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteSourceContinuity
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SeedCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.AmbientCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- The full source is the original infinite weighted programme on the original counting primitive. -/
def value (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  InfiniteWeightedProgram.program (deriv (ReciprocalTail.weight coordinate)) burnolUnitCountingPrimitiveL2

private theorem finite_source_eq (coordinate : BurnolCompletedMellinCoordinate)
    (N : ℕ) (upper : ℝ) (after : 4 ≤ upper) :
    FiniteForcing.source N (burnolWeightedReciprocalStepSource 4 upper
      (ReciprocalTail.weight coordinate) (deriv (ReciprocalTail.weight coordinate))) =
      WeightedProgram.program 4 upper (ReciprocalTail.weight coordinate)
        (deriv (ReciprocalTail.weight coordinate)) (Prefix.primitiveL2 N) := by
  exact (weighted_prefix_eq_finite_sub_continuous _ _ _ _ N (by norm_num) after
    (fun u inside => (ReciprocalTail.weight_hasDerivAt coordinate u
      ((by norm_num : (0 : ℝ) < 4).trans_le inside.1)).differentiableAt.hasDerivAt)
    ((ReciprocalTail.weight_deriv_continuousOn coordinate).mono
      (fun _ inside => (by norm_num : (0 : ℝ) < 4).trans_le inside.1))
    (ReciprocalTail.weight_deriv_measurable coordinate) (ReciprocalTail.weight_measurable coordinate)).symm

/-- Each finite counting operator consumes the actual seed limit before the primitive limit is taken. -/
theorem original_finite_source (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) =
      InfiniteWeightedProgram.program (deriv (ReciprocalTail.weight coordinate)) (Prefix.primitiveL2 N) := by
  have sourceLimit := ((FiniteSourceContinuity.source_continuous N).tendsto
    (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))).comp
      (ReciprocalSeed.seed_tendsto coordinate)
  have programmeLimit := InfiniteWeightedProgram.finite_program_tendsto
    (ReciprocalTail.weight coordinate) (deriv (ReciprocalTail.weight coordinate))
    (ReciprocalTail.weight_deriv_measurable coordinate)
    (ReciprocalTail.derivative_weight_integrable coordinate)
    (ReciprocalTail.head_tendsto_zero coordinate) (Prefix.primitiveL2 N)
  have sameLimit := sourceLimit.congr' (show _ =ᶠ[atTop]
      (fun upper : ℝ => WeightedProgram.program 4 upper (ReciprocalTail.weight coordinate)
        (deriv (ReciprocalTail.weight coordinate)) (Prefix.primitiveL2 N)) from by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with upper after
    exact finite_source_eq coordinate N upper after)
  exact tendsto_nhds_unique sameLimit programmeLimit

/-- The original b generates an actual ambient strong L² counting limit, with its whole normalization. -/
theorem original_ambient_limit (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) atTop (𝓝 (value coordinate)) := by
  have programmeLimit := InfiniteWeightedProgram.program_tendsto
    (deriv (ReciprocalTail.weight coordinate)) (ReciprocalTail.weight_deriv_measurable coordinate)
    (ReciprocalTail.derivative_weight_integrable coordinate)
    Prefix.primitiveL2 burnolUnitCountingPrimitiveL2 Prefix.primitive_tendsto
  apply programmeLimit.congr'
  exact Eventually.of_forall (fun N => (original_finite_source coordinate N).symm)

/-- The original Pa consumer now reads the actual ambient source against its genuinely moved Fourier test. -/
theorem original_cutoff_pair_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    let extension := burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
    let test := fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    Tendsto (fun N : ℕ => inner ℂ (FiniteForcing.source N
        (originalPhysicalCutoff q (burnolMultiplicativeDilation (-shift) extension))) test)
      atTop (𝓝 (inner ℂ (value coordinate) (burnolMultiplicativeDilation shift test))) := by
  dsimp only
  have regular : Continuous (fun source : BurnolL2 => inner ℂ source
      (burnolMultiplicativeDilation shift (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)))) := by
    fun_prop
  have movedLimit := (regular.tendsto (value coordinate)).comp (original_ambient_limit coordinate)
  have sourceZero := SeedCounting.original_fourier_seed_limit coordinate zero shift nonnegative bounded
  have combined := sourceZero.add movedLimit
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using combined

end
end OriginalRieszFinitePairing.CoPoisson.Ward.AmbientCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
