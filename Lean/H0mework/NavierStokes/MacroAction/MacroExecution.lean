import H0mework.Realization.Process.NativeOccurrenceFold
import H0mework.NavierStokes.MacroRuntime.Runtime

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeMacroFiniteExecution

open SourceGeneratedNativeResponseDisposition SourceGeneratedNativeBoundedRun
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

noncomputable section

variable {nu : Viscosity}

def execute (seed : GeneratedWholeRestartCurrent nu) (fuel : ℕ) :
    BoundedRun generatedWholeRestartEndpointMacroRespond seed fuel :=
  generatedBoundedRun generatedWholeRestartEndpointMacroRespond seed fuel

theorem terminal_or_exact_arrival (seed : GeneratedWholeRestartCurrent nu) (fuel : ℕ) :
    (∃ terminal : GeneratedWholeRestartEndpointMacroTerminalRun seed, terminal.arrival.occurrence ≤ fuel) ∨
      ∃ current : GeneratedWholeRestartCurrent nu,
        ∃ arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current,
          arrival.occurrence = fuel ∧
            ∃ response : Response (GeneratedWholeRestartEndpointMacroStep nu) current,
              generatedWholeRestartEndpointMacroRespond current = some response := by
  let run := execute seed fuel
  cases run.endDisposition with
  | terminal stopped depthLe =>
    left
    refine ⟨{ terminal := run.endState, arrival := run.endNativeReachable, stopped := stopped }, ?_⟩
    exact run.endNativeReachable_occurrence.trans_le depthLe
  | @continued next transition depthEq =>
    right
    exact ⟨run.endState, run.endNativeReachable, run.endNativeReachable_occurrence.trans depthEq,
      ⟨next, transition.edge⟩, transition.generated⟩

theorem terminal_or_depth (seed : GeneratedWholeRestartCurrent nu) (fuel : ℕ) :
    Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed) ∨
      ∃ current : GeneratedWholeRestartCurrent nu,
        ∃ arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current,
          arrival.occurrence = fuel := by
  rcases terminal_or_exact_arrival seed fuel with ⟨terminal, _⟩ | ⟨current, arrival, depth, _⟩
  · exact .inl ⟨terminal⟩
  · exact .inr ⟨current, arrival, depth⟩

theorem executed_occurrences (seed : GeneratedWholeRestartCurrent nu) (fuel : ℕ) :
    (execute seed fuel).endNativeReachable.actualOccurrenceTable = (execute seed fuel).actualOccurrenceTable ∧
      (execute seed fuel).endNativeReachable.occurrence = (execute seed fuel).depth ∧
      (execute seed fuel).depth ≤ fuel :=
  ⟨(execute seed fuel).endNativeReachable_actualOccurrenceTable,
    (execute seed fuel).endNativeReachable_occurrence, (execute seed fuel).depth_le_fuel⟩

theorem arrival_invariant (seed : GeneratedWholeRestartCurrent nu)
    (predicate : ℕ → GeneratedWholeRestartCurrent nu → Prop)
    (initial : predicate 0 seed)
    (advance : ∀ (current : GeneratedWholeRestartCurrent nu)
      (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current),
      generatedWholeRestartEndpointMacroRespond current = some response →
      ∀ depth : ℕ, predicate depth current → predicate (depth + 1) response.1)
    {current : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    predicate arrival.occurrence current := by
  induction arrival with
  | initial => exact initial
  | step arrival generated previous => exact advance _ _ generated _ previous

theorem terminal_of_invariant_stops (seed : GeneratedWholeRestartCurrent nu) (fuel : ℕ)
    (predicate : ℕ → GeneratedWholeRestartCurrent nu → Prop)
    (initial : predicate 0 seed)
    (advance : ∀ (current : GeneratedWholeRestartCurrent nu)
      (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current),
      generatedWholeRestartEndpointMacroRespond current = some response →
      ∀ depth : ℕ, predicate depth current → predicate (depth + 1) response.1)
    (stops : ∀ current, predicate fuel current → generatedWholeRestartEndpointMacroRespond current = none) :
    ∃ terminal : GeneratedWholeRestartEndpointMacroTerminalRun seed, terminal.arrival.occurrence ≤ fuel := by
  rcases terminal_or_exact_arrival seed fuel with terminal | ⟨current, arrival, depthEq, response, generated⟩
  · exact terminal
  · have paid := arrival_invariant seed predicate initial advance arrival
    rw [depthEq] at paid
    have stopped := stops current paid
    rw [stopped] at generated
    contradiction

end
end SaturationMonoid.NavierStokes.NativeMacroFiniteExecution
