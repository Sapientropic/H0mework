import H0mework.NavierStokes.EndpointWork.HighFrequencyGlobalExhaustion

/-!
# Source-generated reduced-core scale lineage

The cofinal reduced-core branch is converted from a nested `∀ ∃` statement
into one actual scale path.  Each response is selected from the source-owned
tail, its absolute occurrence lies strictly after the preceding one, and its
requested radius grows strictly.  Every selected crossing retains the exact
reciprocal-component whole nonlinear forcing law.

No path, index, radius growth, crossing, or forcing witness is supplied by
the endpoint theorem's caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade

noncomputable section

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- One generated response of the cofinal reduced-core producer, still
expressed in the coordinates of its exact actual tail. -/
private structure WholeRestartReducedCoreTailResponse
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start radius : ℕ) where
  index : ℕ
  crossed :
    wholeRestartHalfCriticalCrossed (run initial start) index
  coreEscapes :
    radius <
      wholeRestartCrossingFiniteCoreRadius
        (run initial start) index crossed
  gluingZero :
    wholeRestartCrossingCompleteSourceGluingNegativeOneState
      (run initial start) index crossed = 0
  reducedForcing :
    wholeStateVorticityNonlinearNegativeOneState
          (run (run initial start) index).contact.physicalState
          (run (run initial start) index).contact.transverse
          (run (run initial start) index).contact.gradient_summable =
        ((canonicalHalfCriticalComponentCount ν
            (wholeRestartCrossingFiniteCoreState
              (run initial start) index crossed) : ℝ)⁻¹ : ℂ) •
          wholeRestartCrossingFiniteCoreNegativeOneState
            (run initial start) index crossed

private noncomputable def wholeRestartReducedCoreTailResponse
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial)
    (start radius : ℕ) :
    WholeRestartReducedCoreTailResponse initial start radius := by
  let index := Classical.choose (responsibility start radius)
  let indexSpec := Classical.choose_spec (responsibility start radius)
  let crossed := Classical.choose indexSpec
  let response := Classical.choose_spec indexSpec
  rcases response with ⟨coreEscapes, gluingZero, reducedForcing⟩
  exact
    { index := index
      crossed := crossed
      coreEscapes := coreEscapes
      gluingZero := gluingZero
      reducedForcing := reducedForcing }

private structure WholeRestartReducedCoreCursor where
  start : ℕ
  radius : ℕ

private noncomputable def WholeRestartReducedCoreCursor.next
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial)
    (cursor : WholeRestartReducedCoreCursor) :
    WholeRestartReducedCoreCursor :=
  let response :=
    wholeRestartReducedCoreTailResponse
      responsibility cursor.start cursor.radius
  { start := cursor.start + response.index + 1
    radius :=
      wholeRestartCrossingFiniteCoreRadius
        (run initial cursor.start) response.index response.crossed }

private noncomputable def wholeRestartReducedCoreCursor
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial) :
    ℕ → WholeRestartReducedCoreCursor
  | 0 => ⟨0, 0⟩
  | step + 1 =>
      (wholeRestartReducedCoreCursor responsibility step).next
        responsibility

private noncomputable def wholeRestartReducedCoreResponseAt
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial)
    (step : ℕ) :
    WholeRestartReducedCoreTailResponse initial
      (wholeRestartReducedCoreCursor responsibility step).start
      (wholeRestartReducedCoreCursor responsibility step).radius :=
  wholeRestartReducedCoreTailResponse responsibility _ _

private noncomputable def wholeRestartReducedCoreOccurrence
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial)
    (step : ℕ) : ℕ :=
  (wholeRestartReducedCoreCursor responsibility step).start +
    (wholeRestartReducedCoreResponseAt responsibility step).index

private theorem wholeRestartReducedCoreOccurrence_lt_nextStart
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial)
    (step : ℕ) :
    wholeRestartReducedCoreOccurrence responsibility step <
      (wholeRestartReducedCoreCursor responsibility (step + 1)).start := by
  simp only [wholeRestartReducedCoreOccurrence,
    wholeRestartReducedCoreResponseAt, wholeRestartReducedCoreCursor,
    WholeRestartReducedCoreCursor.next]
  omega

private theorem wholeRestartReducedCoreOccurrence_strictMono
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial) :
    StrictMono (wholeRestartReducedCoreOccurrence responsibility) := by
  apply strictMono_nat_of_lt_succ
  intro step
  exact
    (wholeRestartReducedCoreOccurrence_lt_nextStart
      responsibility step).trans_le
        (Nat.le_add_right
          (wholeRestartReducedCoreCursor responsibility (step + 1)).start
          (wholeRestartReducedCoreResponseAt
            responsibility (step + 1)).index)

private theorem wholeRestartReducedCoreRadius_strictMono
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial) :
    StrictMono
      (fun step =>
        (wholeRestartReducedCoreCursor responsibility step).radius) := by
  apply strictMono_nat_of_lt_succ
  intro step
  simpa only [wholeRestartReducedCoreResponseAt,
    wholeRestartReducedCoreCursor,
    WholeRestartReducedCoreCursor.next] using
      (wholeRestartReducedCoreResponseAt
        responsibility step).coreEscapes

/-- The actual strict scale lineage generated by the cofinal reduced-core
branch.  Its occurrence and radius paths are both source-owned and strictly
increasing, and every node carries the exact faithful-zero forcing identity. -/
structure WholeRestartReducedCoreScaleLineage
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) where
  start : ℕ → ℕ
  relativeIndex : ℕ → ℕ
  requestedRadius : ℕ → ℕ
  crossed :
    ∀ step : ℕ,
      wholeRestartHalfCriticalCrossed
        (run initial (start step)) (relativeIndex step)
  occurrence_strict :
    StrictMono (fun step => start step + relativeIndex step)
  requestedRadius_strict : StrictMono requestedRadius
  requestedRadius_succ_eq_coreRadius :
    ∀ step : ℕ,
      requestedRadius (step + 1) =
        wholeRestartCrossingFiniteCoreRadius
          (run initial (start step)) (relativeIndex step) (crossed step)
  actualCurrent :
    ∀ step : ℕ,
      run (run initial (start step)) (relativeIndex step) =
        run initial (start step + relativeIndex step)
  coreEscapes :
    ∀ step : ℕ,
      requestedRadius step <
        wholeRestartCrossingFiniteCoreRadius
          (run initial (start step)) (relativeIndex step) (crossed step)
  gluingZero :
    ∀ step : ℕ,
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        (run initial (start step)) (relativeIndex step) (crossed step) = 0
  reducedForcing :
    ∀ step : ℕ,
      wholeStateVorticityNonlinearNegativeOneState
            (run
              (run initial (start step))
              (relativeIndex step)).contact.physicalState
            (run
              (run initial (start step))
              (relativeIndex step)).contact.transverse
            (run
              (run initial (start step))
              (relativeIndex step)).contact.gradient_summable =
          ((canonicalHalfCriticalComponentCount ν
              (wholeRestartCrossingFiniteCoreState
                (run initial (start step))
                (relativeIndex step) (crossed step)) : ℝ)⁻¹ : ℂ) •
            wholeRestartCrossingFiniteCoreNegativeOneState
              (run initial (start step))
              (relativeIndex step) (crossed step)

/-- The nested tail response generates one strict whole-run scale lineage;
no path or monotonicity certificate is accepted from the caller. -/
noncomputable def wholeRestartCofinalReducedCoreResponsibility_scaleLineage
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (responsibility :
      wholeRestartCofinalReducedCoreResponsibility initial) :
    WholeRestartReducedCoreScaleLineage initial where
  start :=
    fun step =>
      (wholeRestartReducedCoreCursor responsibility step).start
  relativeIndex :=
    fun step =>
      (wholeRestartReducedCoreResponseAt responsibility step).index
  requestedRadius :=
    fun step =>
      (wholeRestartReducedCoreCursor responsibility step).radius
  crossed :=
    fun step =>
      (wholeRestartReducedCoreResponseAt responsibility step).crossed
  occurrence_strict :=
    wholeRestartReducedCoreOccurrence_strictMono responsibility
  requestedRadius_strict :=
    wholeRestartReducedCoreRadius_strictMono responsibility
  requestedRadius_succ_eq_coreRadius :=
    fun _ => rfl
  actualCurrent :=
    fun step =>
      run_run initial
        (wholeRestartReducedCoreCursor responsibility step).start
        (wholeRestartReducedCoreResponseAt responsibility step).index
  coreEscapes :=
    fun step =>
      (wholeRestartReducedCoreResponseAt responsibility step).coreEscapes
  gluingZero :=
    fun step =>
      (wholeRestartReducedCoreResponseAt responsibility step).gluingZero
  reducedForcing :=
    fun step =>
      (wholeRestartReducedCoreResponseAt responsibility step).reducedForcing

/-- The endpoint source now returns a strict reduced-core scale lineage,
a native gluing redirect, or the every-scale atom aggregate lineage. -/
theorem
    stageDefect_generates_zero_or_reducedCoreScaleLineage_or_nativeGluing_or_atomScaleAggregateLineage
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (stage : ℕ) :
    infiniteEndpointMacroStageKineticDefect lineage stage = 0 ∨
      (0 < infiniteEndpointMacroStageKineticDefect lineage stage ∧
        (Nonempty
            (WholeRestartReducedCoreScaleLineage
              (lineage.current stage)) ∨
          wholeRestartNativeGluingResponsibility
              (lineage.current stage) ∨
          wholeRestartAtomScaleAggregateResponsibility
            (lineage.current stage)
            (infiniteEndpointMacroStageKineticDefect lineage stage / 2))) := by
  rcases
      lineage.stageDefect_generates_zero_or_cofinalReducedCore_or_nativeGluing_or_atomScaleAggregateLineage
        stage with
    defectZero | ⟨defectPositive, reduced | gluingOrAggregate⟩
  · exact Or.inl defectZero
  · exact Or.inr
      ⟨defectPositive,
        Or.inl
          ⟨wholeRestartCofinalReducedCoreResponsibility_scaleLineage
            reduced⟩⟩
  · exact Or.inr ⟨defectPositive, Or.inr gluingOrAggregate⟩

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
