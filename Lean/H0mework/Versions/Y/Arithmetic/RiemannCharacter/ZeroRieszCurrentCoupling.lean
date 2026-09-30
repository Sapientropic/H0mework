import H0mework.Versions.Y.Arithmetic.RiemannCharacter.ZeroGlobalCoPoissonCurrent
import H0mework.Versions.Y.Arithmetic.MuntzAction.CoPoissonMuntzRieszDilation
import H0mework.Versions.Y.Arithmetic.MuntzAction.ZeroMuntzRieszRelationTrace

/-!
# Same-zero Riesz-current constitutive residual

The canonical Riesz pair carried by the zero-owned Müntz occurrence is
evaluated after the actual positive dilation.  Removing only the generated
quarter-density weight recovers the existing selected/reversal Mellin
readbacks.  Their norm difference is therefore exactly the integral
group-ring radial current.

This closes the missing kinematic coupling.  It deliberately retains the
resulting flux residual instead of asserting stationarity or RH.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace Character
namespace GlobalCoPoissonCurrent

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open IntegralCharacterGroupRing
open ClozelGeneralizedDual
open scoped InnerProductSpace

noncomputable section

def selectedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (scale : ℝ) (positive : 0 < scale) : ℂ :=
  selectedRieszTrace observation nontrivial source
    (quarterDilationTestAction
      (selectedCoPoissonMuntzParameter observation) scale positive
      (normalizedCoPoissonMuntzQuarterShellTest
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)))

def reversalDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (scale : ℝ) (positive : 0 < scale) : ℂ :=
  reversalRieszTrace observation nontrivial source
    (quarterDilationTestAction
      (reversalCoPoissonMuntzParameter observation) scale positive
      (normalizedCoPoissonMuntzQuarterShellTest
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)))

theorem occurrence_selectedDilationTrace_eq_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    selectedDilationTrace observation nontrivial
        (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale positive =
      (scale : ℂ) ^
        ((1 / 4 : ℂ) -
          ClozelGeneralizedDual.selectedCoPoissonMuntzParameter observation) := by
  unfold selectedDilationTrace
  rw [ClozelGeneralizedDual.occurrence_selectedRieszTrace_eq_functional]
  have eigen := LinearMap.congr_fun
    (quarterDilationFunctional_eigenlaw
      (selectedCoPoissonMuntzParameter observation) scale positive)
    (normalizedCoPoissonMuntzQuarterShellTest
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
  simpa using eigen

theorem occurrence_reversalDilationTrace_eq_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    reversalDilationTrace observation nontrivial
        (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale positive =
      (scale : ℂ) ^
        ((1 / 4 : ℂ) -
          ClozelGeneralizedDual.reversalCoPoissonMuntzParameter observation) := by
  unfold reversalDilationTrace
  rw [ClozelGeneralizedDual.occurrence_reversalRieszTrace_eq_functional]
  have eigen := LinearMap.congr_fun
    (quarterDilationFunctional_eigenlaw
      (reversalCoPoissonMuntzParameter observation) scale positive)
    (normalizedCoPoissonMuntzQuarterShellTest
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial))
  simpa using eigen

/-- Remove the source-generated half-density normalization, not an arbitrary
character-dependent scalar. -/
def selectedNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (scale : ℝ) (positive : 0 < scale) : ℂ :=
  (positiveMellinQuarterDilationWeight scale)⁻¹ *
    selectedDilationTrace observation nontrivial source scale positive

def reversalNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (scale : ℝ) (positive : 0 < scale) : ℂ :=
  (positiveMellinQuarterDilationWeight scale)⁻¹ *
    reversalDilationTrace observation nontrivial source scale positive

theorem occurrence_selectedNormalizedDilationTrace_eq_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    selectedNormalizedDilationTrace observation nontrivial
        (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale positive =
      (scale : ℂ) ^
        (-(ClozelGeneralizedDual.selectedCoPoissonMuntzParameter
          observation)) := by
  rw [selectedNormalizedDilationTrace,
    occurrence_selectedDilationTrace_eq_character,
    ← quarterDilationCharacter_factor
      (selectedCoPoissonMuntzParameter observation) scale positive]
  exact inv_mul_cancel_left₀
    (positiveMellinQuarterDilationWeight_ne_zero scale) _

theorem occurrence_reversalNormalizedDilationTrace_eq_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : ℝ) (positive : 0 < scale) :
    reversalNormalizedDilationTrace observation nontrivial
        (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root scale positive =
      (scale : ℂ) ^
        (-(ClozelGeneralizedDual.reversalCoPoissonMuntzParameter
          observation)) := by
  rw [reversalNormalizedDilationTrace,
    occurrence_reversalDilationTrace_eq_character,
    ← quarterDilationCharacter_factor
      (reversalCoPoissonMuntzParameter observation) scale positive]
  exact inv_mul_cancel_left₀
    (positiveMellinQuarterDilationWeight_ne_zero scale) _

def qRichStageScale (stage : Nat) : ℝ :=
  QRich.blockQRichSuccessorScale stage

theorem qRichStageScale_pos (stage : Nat) :
    0 < qRichStageScale stage := by
  unfold qRichStageScale
  rw [QRich.blockQRichSuccessorScale_eq_stage_add_three]
  positivity

def sourceSelectedStageNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (stage : Nat) : ℂ :=
  selectedNormalizedDilationTrace observation nontrivial
    source
    (qRichStageScale stage) (qRichStageScale_pos stage)

def sourceReversalStageNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ClozelGeneralizedDual.ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (stage : Nat) : ℂ :=
  reversalNormalizedDilationTrace observation nontrivial
    source
    (qRichStageScale stage) (qRichStageScale_pos stage)

def selectedStageNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℂ :=
  sourceSelectedStageNormalizedDilationTrace observation nontrivial
    (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
      observation nontrivial).root stage

def reversalStageNormalizedDilationTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℂ :=
  sourceReversalStageNormalizedDilationTrace observation nontrivial
    (ClozelGeneralizedDual.zeroOwnedCharacterMuntzCokernelOccurrence
      observation nontrivial).root stage

theorem selectedStageNormalizedDilationTrace_eq_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    selectedStageNormalizedDilationTrace observation nontrivial stage =
      QRich.selectedPositiveMellinDilationReadback
        observation nontrivial stage := by
  unfold selectedStageNormalizedDilationTrace
    sourceSelectedStageNormalizedDilationTrace
  rw [occurrence_selectedNormalizedDilationTrace_eq_character,
    QRich.selectedPositiveMellinDilationReadback_eq_character]
  unfold qRichStageScale ClozelGeneralizedDual.selectedCoPoissonMuntzParameter
  rfl

theorem reversalStageNormalizedDilationTrace_eq_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    reversalStageNormalizedDilationTrace observation nontrivial stage =
      QRich.reversalPositiveMellinDilationReadback
        observation nontrivial stage := by
  unfold reversalStageNormalizedDilationTrace
    sourceReversalStageNormalizedDilationTrace
  rw [occurrence_reversalNormalizedDilationTrace_eq_character,
    QRich.reversalPositiveMellinDilationReadback_eq_character]
  unfold qRichStageScale ClozelGeneralizedDual.reversalCoPoissonMuntzParameter
  rfl

/-- Exact retained radial residual generated by the Riesz pair and the
actual scale action. -/
def radialRieszFluxResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℝ :=
  ‖selectedStageNormalizedDilationTrace observation nontrivial stage‖ -
    ‖reversalStageNormalizedDilationTrace observation nontrivial stage‖

/-- The former character current is now exactly a source.2 Riesz-current
coupling residual. -/
theorem groupRingRadialCurrent_eq_radialRieszFluxResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    groupRingRadialCurrent observation stage =
      radialRieszFluxResidual observation nontrivial stage := by
  unfold groupRingRadialCurrent radialRieszFluxResidual stageSqrtScaleUnit
  rw [selected_sqrt_basis_readback observation nontrivial stage,
    reversal_sqrt_basis_readback observation nontrivial stage,
    ← selectedStageNormalizedDilationTrace_eq_readback,
    ← reversalStageNormalizedDilationTrace_eq_readback]

theorem radialRieszFluxResidual_eq_zero_iff_groupRingRadialCurrent_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    radialRieszFluxResidual observation nontrivial stage = 0 ↔
      groupRingRadialCurrent observation stage = 0 := by
  rw [groupRingRadialCurrent_eq_radialRieszFluxResidual]

end

end GlobalCoPoissonCurrent
end Character
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
