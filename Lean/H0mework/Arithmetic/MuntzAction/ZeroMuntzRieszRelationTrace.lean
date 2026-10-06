import H0mework.Arithmetic.MuntzAction.CoPoissonMuntzZeroGraphCokernel
import H0mework.Arithmetic.CoPoisson.RoleRepresentation

/-!
# Same-zero Müntz relation trace on the canonical Riesz pair

The actual quarter-Mellin relation is identified pointwise with the global
integral remainder role.  The canonical Riesz vectors carried by the same
zero occurrence pair to zero with every such relation class.  This is the
source relation no-flux law; it does not say that a free dilation mode or its
integral current vanishes.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open CanonicalUnitArithmeticCoordinateProjectionObstruction
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedPositiveRealCharacter
open GlobalCoPoissonRoleRepresentation
open scoped InnerProductSpace SchwartzMap

noncomputable section

def mellinScaleUnit (scale : PositiveMellinReal) : Units NNReal :=
  positiveRealUnit (Real.sqrt scale.1) (Real.sqrt_pos.2 scale.2)

@[simp] theorem mellinScaleUnit_value (scale : PositiveMellinReal) :
    ThetaJRoleRepresentation.scaleValue (mellinScaleUnit scale) =
      Real.sqrt scale.1 := by
  unfold mellinScaleUnit ThetaJRoleRepresentation.scaleValue
  exact positiveRealUnit_val _ _

/-- Every value of the actual quarter-Mellin relation is the evaluation of
the global remainder role on the corresponding square-root scale basis. -/
theorem muntzRelation_value_eq_remainderRole
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) (scale : PositiveMellinReal) :
    (coPoissonQuarterMellinConvergentMap
        z positive belowHalf test).1 scale =
      remainderRole (delta (mellinScaleUnit scale)) test := by
  rw [coPoissonQuarterMellinConvergentMap_value,
    remainderRole_delta_apply, mellinScaleUnit_value]
  unfold coPoissonQuarterMellinMap coPoissonMuntzScaleRemainder
  rw [dif_pos (Real.sqrt_pos.2 scale.2)]
  rfl

/-- Selected Riesz pairing read directly from an arbitrary payload of the
same type.  Its authoritative use below is always at the occurrence root. -/
def selectedRieszTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (value : QuarterMellinL2Test
      (selectedCoPoissonMuntzParameter observation)) : ℂ :=
  inner ℂ source.2.1
    (coPoissonMuntzGraphSourceMap
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      value)

def reversalRieszTrace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (source : ZeroOwnedCharacterMuntzCokernelPayload
      observation nontrivial)
    (value : QuarterMellinL2Test
      (reversalCoPoissonMuntzParameter observation)) : ℂ :=
  inner ℂ source.2.2
    (coPoissonMuntzGraphSourceMap
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
      (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
      value)

theorem occurrence_selectedRieszTrace_eq_functional
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (selectedCoPoissonMuntzParameter observation)) :
    selectedRieszTrace observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root value =
      quarterMellinL2Functional
        (selectedCoPoissonMuntzParameter observation) value := by
  change inner ℂ
      (selectedCoPoissonMuntzRieszVector observation nontrivial)
      (coPoissonMuntzGraphSourceMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        value) = _
  exact selectedCoPoissonMuntzRieszVector_source_readback
    observation nontrivial value

theorem occurrence_reversalRieszTrace_eq_functional
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (value : QuarterMellinL2Test
      (reversalCoPoissonMuntzParameter observation)) :
    reversalRieszTrace observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root value =
      quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation) value := by
  change inner ℂ
      (reversalCoPoissonMuntzRieszVector observation nontrivial)
      (coPoissonMuntzGraphSourceMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        value) = _
  exact reversalCoPoissonMuntzRieszVector_source_readback
    observation nontrivial value

/-- The selected Riesz vector has zero flux through every actual Müntz
relation class. -/
theorem occurrence_selectedMuntzRelationTrace_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (test : SchwartzMap ℝ ℂ) :
    selectedRieszTrace observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root
        (coPoissonQuarterMellinConvergentMap
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          test) = 0 := by
  rw [occurrence_selectedRieszTrace_eq_functional]
  have annihilation := LinearMap.congr_fun
    (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial) test
  change quarterMellinL2Functional (observation.coordinate / 2)
      (coPoissonQuarterMellinConvergentMap
        (observation.coordinate / 2) _ _ test) = 0
  exact annihilation

/-- The reversal Riesz vector obeys the same actual relation no-flux law. -/
theorem occurrence_reversalMuntzRelationTrace_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (test : SchwartzMap ℝ ℂ) :
    reversalRieszTrace observation nontrivial
        (zeroOwnedCharacterMuntzCokernelOccurrence
          observation nontrivial).root
        (coPoissonQuarterMellinConvergentMap
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
          (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          test) = 0 := by
  rw [occurrence_reversalRieszTrace_eq_functional]
  have annihilation := LinearMap.congr_fun
    (reversalZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial) test
  change quarterMellinL2Functional
      (coordinateReversal observation.coordinate / 2)
      (coPoissonQuarterMellinConvergentMap
        (coordinateReversal observation.coordinate / 2) _ _ test) = 0
  exact annihilation

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
