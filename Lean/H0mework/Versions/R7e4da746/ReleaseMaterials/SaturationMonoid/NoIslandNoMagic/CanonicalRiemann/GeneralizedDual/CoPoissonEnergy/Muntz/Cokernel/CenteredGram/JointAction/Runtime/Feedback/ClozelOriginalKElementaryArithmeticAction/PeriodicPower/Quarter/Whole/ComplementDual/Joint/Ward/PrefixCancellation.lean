import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.FixedPrefix
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TopUnit

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TopUnit
open scoped Topology InnerProductSpace

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "U" => OriginalKFiniteOrderRelease.UnitPowerSource.unitPower observation half
local notation "e" => burnolAnalyticComplementExpectedPhysicalFourierRead ActualAnalyticOwner observation
local notation "q" => (1 / 4 : ℝ)
local notation "r₀" => q / stageZeroSonineQ
local notation "h₀" => Real.log stageZeroSonineQ
include nontrivial

/-- The original Fourier top fee and the conjugate C top jet are the same generated coefficient. -/
theorem actual_original_fixed_top_fee :
    star e = (2 : ℂ) ^ (m - 1) *
      generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (star (c).value) (star (c).value) := by
  have positive := generatedRiemannXiZeroOrder_pos observation nontrivial
  have power : (2 : ℂ) ^ m = (2 : ℂ) ^ (m - 1) * 2 := by
    calc
      _ = (2 : ℂ) ^ ((m - 1) + 1) := congrArg (fun n : Nat => (2 : ℂ) ^ n) (by omega)
      _ = _ := pow_succ _ _
  rw [burnolAnalyticComplementExpectedPhysicalFourierRead_eq observation nontrivial,
    star_mul, star_div₀, star_pow, star_ofNat]
  change star (generatedRiemannBareZeroLocalizedSpectrum ActualAnalyticOwner (c).value (c).value) *
    ((2 : ℂ) ^ m / 2) = _
  rw [← actual_bare_conjugate c, power]
  ring

/-- The complete fixed positive Unit contact is the actual smaller-radius C prefix. -/
theorem actual_native_unit_plus_fixed_prefix :
    inner ℂ (U (m - 1)) (burnolMultiplicativeDilation h₀ (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native.nativeReturn c)) =
      -fullMellinTranslationCharacter (star (c).value) (-h₀) *
        ((2 : ℂ) ^ m / ((m - 1).factorial : ℂ)) *
          (∫ x : ℝ in (0 : ℝ)..r₀, (x : ℂ) ^ (star (c).value - 1) *
            (Real.log (x / r₀) : ℂ) ^ (m - 1) * fullFloorRaw c x) := by
  rw [actual_native_unit_plus_fixed_prefix_top observation nontrivial half,
    actual_original_fixed_top_fee observation nontrivial half]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
