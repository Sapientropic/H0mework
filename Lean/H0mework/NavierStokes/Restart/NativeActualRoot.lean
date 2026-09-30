import H0mework.Realization.Process.NativeResponseDisposition
import H0mework.NavierStokes.Restart.NativeRecursion

/-!
# Actual single-step root for the generated whole-restart process

The authoritative temporal process is the already existing native update

```text
current -> current.next
```

and its recursive readout `GeneratedWholeRestartCurrent.run`.  This module gives that update the
dependent responder shape used by the shared source-generated reachability kernel.  Every finite
occurrence is produced by one call to the responder at the current state.  No proposition about a
future terminal, an infinite lineage, a future crossing, or a completed tail occurs in the source
mouth.

The later endpoint-macro and accumulation constructions may consume properties of the generated
finite history.  They are not allowed to replace this root by first deciding a global fact about
the whole future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent

noncomputable section

/-- One actual source-owned whole-restart edge.  Its target is fixed by the current's native
`next`; callers cannot provide another target. -/
inductive GeneratedWholeRestartNativeActualStep
    (nu : Viscosity) :
    GeneratedWholeRestartCurrent nu ->
      GeneratedWholeRestartCurrent nu -> Type
  | advance (current : GeneratedWholeRestartCurrent nu) :
      GeneratedWholeRestartNativeActualStep nu current current.next

namespace GeneratedWholeRestartNativeActualStep

/-- The dependent target of an actual root edge is the existing native write. -/
theorem target_eq_next
    {nu : Viscosity}
    {current next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartNativeActualStep nu current next) :
    next = current.next := by
  cases step
  rfl

end GeneratedWholeRestartNativeActualStep

/-- The source-owned responder at one current.  It emits exactly one native write and never reads
a terminal/infinite verdict about later occurrences. -/
def generatedWholeRestartNativeActualRespond
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    Option
      (Response (GeneratedWholeRestartNativeActualStep nu) current) :=
  some <| Sigma.mk current.next (.advance current)

@[simp] theorem generatedWholeRestartNativeActualRespond_eq_some
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    generatedWholeRestartNativeActualRespond current =
      some (Sigma.mk current.next (.advance current)) :=
  rfl

/-- The original root has no source-level `none` branch.  A later domain terminal must therefore
be emitted by an additional actual occurrence; it cannot be manufactured by a global verdict over
this run. -/
theorem generatedWholeRestartNativeActualRespond_ne_none
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    generatedWholeRestartNativeActualRespond current ≠ none := by
  simp

/-- Proof-relevant reachability of the `index`-th current is generated recursively from the exact
previous response.  This is the authority direction behind the existing function `run`. -/
def generatedWholeRestartNativeReachableAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    (index : Nat) ->
      NativeReachable initial generatedWholeRestartNativeActualRespond
        (run initial index)
  | 0 => .initial
  | index + 1 =>
      .step (generatedWholeRestartNativeReachableAt initial index)
        (generatedWholeRestartNativeActualRespond_eq_some (run initial index))

/-- The reachability proof contains exactly the number of native events requested by the finite
prefix; no completed future is stored in the current. -/
@[simp] theorem generatedWholeRestartNativeReachableAt_occurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) (index : Nat) :
    (generatedWholeRestartNativeReachableAt initial index).occurrence = index := by
  induction index with
  | zero =>
      change 0 = 0
      rfl
  | succ index inductionHypothesis =>
      change
        (generatedWholeRestartNativeReachableAt initial index).occurrence + 1 =
          index + 1
      rw [inductionHypothesis]

/-- One exact finite occurrence generated at `run initial index`.  The dependent response and its
producer equality stay in the same Type-valued package. -/
structure GeneratedWholeRestartNativeActualOccurrenceAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : Type where
  response : Response
    (GeneratedWholeRestartNativeActualStep nu) (run initial index)
  generated :
    generatedWholeRestartNativeActualRespond (run initial index) = some response

/-- Canonical source-owned occurrence at one finite index. -/
def generatedWholeRestartNativeActualOccurrence
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    GeneratedWholeRestartNativeActualOccurrenceAt initial index where
  response := Sigma.mk (run initial index).next (.advance (run initial index))
  generated := generatedWholeRestartNativeActualRespond_eq_some (run initial index)

/-- Reading the target of the generated occurrence recovers the next recursively generated state,
not a caller-supplied future current. -/
@[simp] theorem generatedWholeRestartNativeActualOccurrence_target
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    (generatedWholeRestartNativeActualOccurrence initial index).response.1 =
      run initial (index + 1) :=
  rfl

/-- One finite source occurrence simultaneously exposes its exact current, native target, actual
step, and proof-relevant arrival chain.  This is the thin root mouth to be recognized by later
whole-carrier and living-law compilers. -/
theorem generatedWholeRestartNativeActualRootAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    generatedWholeRestartNativeActualRespond (run initial index) =
        some (generatedWholeRestartNativeActualOccurrence initial index).response ∧
      (generatedWholeRestartNativeActualOccurrence initial index).response.1 =
        run initial (index + 1) ∧
      (generatedWholeRestartNativeReachableAt initial index).occurrence = index := by
  exact
    ⟨(generatedWholeRestartNativeActualOccurrence initial index).generated,
      generatedWholeRestartNativeActualOccurrence_target initial index,
      generatedWholeRestartNativeReachableAt_occurrence initial index⟩

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeActualRoot
end NavierStokes
end SaturationMonoid
