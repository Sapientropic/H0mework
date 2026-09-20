import H0mework.Physics.CartanReduction.ActionIncrement

/-! The source's reduced P286 step changes the complete action on one
Cartan-qualified actual. Opposite two-step differences prohibit a nontrivial
payload two-cycle without introducing a time/depth potential. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Reduction

open MeasureTheory
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineFormNativeMotherAction
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineP286SourceNativeReducedEntropyDescent
open StageNineP286SourceNativeReducedCompactVariation
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineP286SourceNativeCenteredReducedEntropyIteration

noncomputable section

def p286CartanStateNext {source : SmoothUnifiedSource} (center : BasePoint)
    (state : P286CenteredReducedEntropyStateAt source) :
    P286CenteredReducedEntropyStateAt source where
  current := p286CartanNext source state.current state.smooth state.nondegenerate center
  smooth := p286CartanNext_smooth source state.current state.smooth state.nondegenerate center
  nondegenerate := p286CartanNext_nondegenerate source state.current state.smooth state.nondegenerate center
  auxiliaryEquation :=
    p286CartanNext_auxiliaryPointwiseEquation source state.current state.smooth state.nondegenerate center

/-- Difference of the active Dirac-dual mother densities on the two actuals. -/
def actualRelativeAction (source : SmoothUnifiedSource)
    (before after : StageNineHolonomicConfiguration) : ℝ :=
  ∫ point : BasePoint,
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField after point) -
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
        (toContinuumPointField before point)

theorem actualRelativeAction_reverse (source : SmoothUnifiedSource)
    (before after : StageNineHolonomicConfiguration) :
    actualRelativeAction source after before = -actualRelativeAction source before after := by
  unfold actualRelativeAction
  rw [← integral_neg]
  simp only [neg_sub]

theorem p286CartanStateNext_actualRelativeAction
    {source : SmoothUnifiedSource} (center : BasePoint)
    (state : P286CenteredReducedEntropyStateAt source)
    (cartanFixed : sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      state.current = state.current) :
    actualRelativeAction source state.current (p286CartanStateNext center state).current =
      p286CenteredReducedRelativeAction source state.current state.smooth state.nondegenerate center := by
  change actualRelativeAction source state.current
    (p286CartanNext source state.current state.smooth state.nondegenerate center) = _
  rw [p286CartanNext_eq_reducedNext_of_cartan_fixed source state.current
    state.smooth state.nondegenerate center cartanFixed]
  unfold actualRelativeAction
  have materialIncrement : ∀ point : BasePoint,
      sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField
            (p286CenteredReducedNext source state.current state.smooth state.nondegenerate center) point) -
        sourceGeneratedDiracDualFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField state.current point) =
      sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField
            (p286CenteredReducedNext source state.current state.smooth state.nondegenerate center) point) -
        sourceGeneratedFormNativeUnifiedLocalDensity source 0 point
          (toContinuumPointField state.current point) := by
    intro point
    exact diracDual_densityIncrement_eq_of_material source 0 point _ _ rfl rfl rfl rfl
  simp_rw [materialIncrement]
  unfold p286CenteredReducedNext p286CenteredReducedRelativeAction p286ReducedCompactRelativeAction
  rw [state.reducedBase_eq]

theorem p286CartanStateNext_cartan_fixed
    {source : SmoothUnifiedSource} (center : BasePoint)
    (state : P286CenteredReducedEntropyStateAt source) :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
        (p286CartanStateNext center state).current =
      (p286CartanStateNext center state).current :=
  p286CartanNext_cartan_fixed source state.current state.smooth state.nondegenerate center

theorem p286CartanStateNext_action_nonpositive
    {source : SmoothUnifiedSource} (center : BasePoint)
    (state : P286CenteredReducedEntropyStateAt source)
    (cartanFixed : sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      state.current = state.current) :
    actualRelativeAction source state.current (p286CartanStateNext center state).current ≤ 0 := by
  rw [p286CartanStateNext_actualRelativeAction center state cartanFixed]
  exact p286CenteredReducedRelativeAction_nonpositive source state.current
    state.smooth state.nondegenerate center

/-- A return after two physical writes already forces a one-write fixed
actual. The argument uses the full action change, never occurrence depth. -/
theorem p286CartanStateNext_no_nontrivial_twoCycle
    {source : SmoothUnifiedSource} (center : BasePoint)
    (state : P286CenteredReducedEntropyStateAt source)
    (cartanFixed : sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
      state.current = state.current)
    (returns : (p286CartanStateNext center (p286CartanStateNext center state)).current =
      state.current) :
    (p286CartanStateNext center state).current = state.current := by
  have secondNonpositive := p286CartanStateNext_action_nonpositive center
    (p286CartanStateNext center state) (p286CartanStateNext_cartan_fixed center state)
  rw [returns, actualRelativeAction_reverse,
    p286CartanStateNext_actualRelativeAction center state cartanFixed] at secondNonpositive
  have defectZero : p286CenteredReducedDefect source state.current center = 0 := by
    by_contra nonzero
    have positive := lt_of_le_of_ne
      (p286CenteredReducedDefect_nonnegative source state.current center) (Ne.symm nonzero)
    have strict := p286CenteredReducedRelativeAction_strict source state.current
      state.smooth state.nondegenerate center positive
    linarith
  change p286CartanNext source state.current state.smooth state.nondegenerate center = _
  rw [p286CartanNext_eq_reducedNext_of_cartan_fixed source state.current
    state.smooth state.nondegenerate center cartanFixed,
    p286CenteredReducedNext_eq_base_of_defect_zero source state.current
      state.smooth state.nondegenerate center defectZero,
    state.reducedBase_eq]

end
end SaturationMonoid.PhysicsCore.Stage9C.Reduction
