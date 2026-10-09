import H0mework.Versions.V2.Arithmetic.MobiusSource.Replay
import H0mework.Arithmetic.MellinTateSource.FourierRead

/-!
# The complete co-Poisson range has a concrete Möbius source realization

Tate supplies the second generator from the same actual source. The
continuous replay identity therefore extends to the existing closed range,
without assuming that a shifted projection remains in that range.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction BigOperators InnerProductSpace ENNReal
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius
local notation "Window" => BurnolRadiusIntervalL2 4

theorem burnolCoPoissonWindowReplay_Pa (radius : ℝ)
    (value : Ambient) (inPa : value ∈ burnolCompactCoPoissonClosedRange) :
    burnolCoPoissonWindowReplay radius value =
      burnolRadiusRestriction radius (value : BurnolL2) := by
  let original : Ambient →L[ℂ] BurnolRadiusIntervalL2 radius :=
    (burnolRadiusRestriction radius).comp
      (Submodule.subtypeL (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule)
  let equation := (burnolCoPoissonWindowReplay radius - original).ker
  have generatorEq (index : BurnolCompactCoPoissonGeneratorIndex) :
      burnolCoPoissonWindowReplay radius (burnolCompactCoPoissonGenerator index) =
        original (burnolCompactCoPoissonGenerator index) := by
    rcases index with ⟨source, parity⟩
    fin_cases parity
    · exact burnolCoPoissonWindowReplay_compact_eq radius source
    · have sameSource : burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) =
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      calc
        _ = burnolCoPoissonWindowReplay radius
            (burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source)) :=
          congrArg (burnolCoPoissonWindowReplay radius) sameSource
        _ = original (burnolCompactAdditivePhysicalState
            (burnolCompactTateReciprocalSource source)) :=
          burnolCoPoissonWindowReplay_compact_eq radius (burnolCompactTateReciprocalSource source)
        _ = _ := congrArg original sameSource.symm
  have sourceEq (input : BurnolCompactCoPoissonLinearSource) :
      burnolCoPoissonWindowReplay radius (burnolCompactCoPoissonLanding input) =
        original (burnolCompactCoPoissonLanding input) := by
    induction input using Finsupp.induction_linear with
    | zero => simp
    | add left right leftEq rightEq => simp only [map_add, leftEq, rightEq]
    | single index coefficient =>
        rw [burnolCompactCoPoissonLanding_single, map_smul, map_smul, generatorEq]
  have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤ equation := by
    rintro _ ⟨input, rfl⟩
    change burnolCoPoissonWindowReplay radius (burnolCompactCoPoissonLanding input) -
      original (burnolCompactCoPoissonLanding input) = 0
    rw [sourceEq, sub_self]
  have closed : IsClosed (equation : Set Ambient) := by
    change IsClosed {input : Ambient | burnolCoPoissonWindowReplay radius input -
      original input = 0}
    exact isClosed_eq ((burnolCoPoissonWindowReplay radius).continuous.sub original.continuous)
      continuous_const
  have closedLe := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    rangeLe closed
  have actual := closedLe inPa
  change burnolCoPoissonWindowReplay radius value - original value = 0 at actual
  exact sub_eq_zero.mp actual

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
