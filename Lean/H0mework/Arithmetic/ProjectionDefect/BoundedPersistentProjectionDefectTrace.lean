import H0mework.Arithmetic.ProjectionDefect.StableArithmeticProjectionDefectInstability

/-!
# Bounded persistent projection-defect traces

This file names the persistence object that the hard gates rule out.

The object is intentionally thin:

```text
for every shell k <= target, there is a projection defect at k
```

It carries no endpoint candidates and no atom-pair successor realization.  It
is only the explicit "stable gap over a bounded interval" witness consumed by
finite descent, source holonomy, or terminal-discharge laws.

The companion file `BoundedPersistentTraceExtraction.lean` proves that bounded
source-side defect descent extracts this object from a claimed target-shell
defect.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- A bounded persistent ordinary atom-projection defect trace. -/
structure BoundedPersistentAtomProjectionDefectTrace
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n target : Nat) where
  defect_at :
    ∀ k : Nat, k ≤ target ->
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k)

namespace BoundedPersistentAtomProjectionDefectTrace

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n target : Nat}

/-- Instability laws rule out bounded persistent ordinary defect traces. -/
theorem false_of_instability_law
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target)
    (law :
      ArithmeticProjectionDefectInstabilityLaw
        Atomic SourceEvidence Residual n) :
    False :=
  law.no_persistent_arithmetic_projection_defect_trace
    trace.defect_at

/-- Bounded source-side descent laws rule out bounded persistent ordinary
defect traces at their target. -/
theorem false_of_bounded_descent
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target)
    (descent :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target) :
    False :=
  descent.no_persistent_arithmetic_projection_defect_trace
    trace.defect_at

end BoundedPersistentAtomProjectionDefectTrace

/-- A bounded persistent traced feasible atom-projection defect trace. -/
structure BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  defect_at :
    ∀ k : Nat, k ≤ target ->
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k)

namespace BoundedPersistentTracedFeasibleAtomProjectionDefectTrace

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced instability laws rule out bounded persistent traced feasible defect
traces. -/
theorem false_of_instability_law
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (law :
      TracedFeasibleArithmeticProjectionDefectInstabilityLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    False :=
  law.no_persistent_traced_feasible_arithmetic_projection_defect_trace
    trace.defect_at

/-- Bounded traced source-side descent laws rule out bounded persistent traced
feasible defect traces at their target. -/
theorem false_of_bounded_descent
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (descent :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  descent.no_persistent_traced_feasible_arithmetic_projection_defect_trace
    trace.defect_at

end BoundedPersistentTracedFeasibleAtomProjectionDefectTrace


end RepresentationArithmeticAtomProjectionDefect
