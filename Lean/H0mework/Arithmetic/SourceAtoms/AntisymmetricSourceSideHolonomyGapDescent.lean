import H0mework.Arithmetic.SourceAtoms.SourceSideHolonomyGapDescent
import H0mework.Arithmetic.SourceAtoms.SourceAntisymmetricHolonomy

/-!
# Antisymmetric source-side holonomy gap descent

This file lowers the source-holonomy hard gate from a closed source loop to a
more source-native preloop:

```text
upper projection defect at k+1
+ lower atom-pair realization at k
-> source -> target path
+ target -> source path
+ strict residual drop
+ source path antisymmetry
-> closed strict source residual holonomy
-> contradiction
-> lower projection defect at k
```

No theorem here assumes atom-pair successor realization.  The only arithmetic
input is the hypothetical lower realization whose coexistence with the upper
defect is forbidden by source-side holonomy.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Bounded non-traced antisymmetric source-side holonomy gap descent.

The hard source-side field returns a preclosed strict residual holonomy.  The
closed equality is not a field: it is derived from `path_antisymmetry`. -/
structure BoundedAntisymmetricSourceSideHolonomyGapDescent
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  path_antisymmetry :
    SourcePathAntisymmetry SourceEvidence Source
  lower_realization_to_source_preloop :
    ∀ {k : Nat},
      k < target ->
        (defect :
          AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourcePreClosedStrictResidualHolonomyAt
              SourceEvidence Residual Source
              (source := defect.demand.evidence)

namespace BoundedAntisymmetricSourceSideHolonomyGapDescent

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Convert the antisymmetric preloop socket to the closed-holonomy gap
descent socket. -/
def toSourceSideHolonomyGapDescent
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    BoundedSourceSideHolonomyGapDescent
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  lower_realization_to_source_loop := by
    intro k hk defect hLowerRealization
    exact
      sourceClosedStrictResidualHolonomyAtOfAntisymmetricPreLoop
        D.path_antisymmetry
        (D.lower_realization_to_source_preloop
          hk defect hLowerRealization)

/-- Antisymmetric source-side preholonomy gives one-step defect descent. -/
theorem descend_below
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  D.toSourceSideHolonomyGapDescent.descend_below hk

/-- Convert the antisymmetric preholonomy socket all the way to bounded
defect-instability descent. -/
def toBoundedSourceSideDefectDescent
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    BoundedSourceSideAtomProjectionDefectDescent
      Atomic SourceEvidence Residual n target :=
  D.toSourceSideHolonomyGapDescent.toBoundedSourceSideDefectDescent

/-- Antisymmetric source-side preholonomy excludes the target projection
defect. -/
theorem terminal_defect_of_target_defect
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) :=
  D.toSourceSideHolonomyGapDescent
    |>.terminal_defect_of_target_defect

/-- Antisymmetric source-side preholonomy excludes the target projection
defect. -/
theorem no_target_arithmetic_projection_defect
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toSourceSideHolonomyGapDescent.no_target_arithmetic_projection_defect

/-- A bounded persistent defect trace is impossible under antisymmetric
source-side preholonomy. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  D.toSourceSideHolonomyGapDescent
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace by
antisymmetric source-side preholonomy descent. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  D.toSourceSideHolonomyGapDescent
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible under
antisymmetric source-side preholonomy. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  D.toSourceSideHolonomyGapDescent
    |>.no_bounded_persistent_arithmetic_projection_defect_trace trace

/-- Antisymmetric source-side preholonomy excludes a target defect through the
explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  D.toSourceSideHolonomyGapDescent
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level readout from antisymmetric source-side preholonomy.

The conclusion is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_demand
    (D :
      BoundedAntisymmetricSourceSideHolonomyGapDescent
        Atomic SourceEvidence Residual Source n target)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toSourceSideHolonomyGapDescent
    |>.not_not_atom_realization_of_target_demand demand

end BoundedAntisymmetricSourceSideHolonomyGapDescent

/-- Bounded traced antisymmetric source-side holonomy gap descent.

This is the preferred trace-preserving preholonomy socket: source path /
phase trace / sigma tag / producer trace descend, while the coexistence of an
upper defect and lower atom realization would create an antisymmetric
source-preloop with strict residual drop. -/
structure BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  path_antisymmetry :
    SourcePathAntisymmetry SourceEvidence Source
  lower_realization_to_source_preloop :
    ∀ {k : Nat},
      k < target ->
        (defect :
          TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n (k + 1)) ->
          (∃ p : ArithmeticAtomPair Atomic n,
            ArithmeticAtomPair.energy p = k) ->
            SourcePreClosedStrictResidualHolonomyAt
              SourceEvidence Residual Source
              (source := defect.demand.demand.demand.evidence)

namespace BoundedTracedAntisymmetricSourceSideHolonomyGapDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Convert the traced antisymmetric preloop socket to the traced
closed-holonomy gap descent socket. -/
def toTracedSourceSideHolonomyGapDescent
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedSourceSideHolonomyGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_descent := D.source_descent
  step_path := D.step_path
  trace_descent := D.trace_descent
  lower_realization_to_source_loop := by
    intro k hk defect hLowerRealization
    exact
      sourceClosedStrictResidualHolonomyAtOfAntisymmetricPreLoop
        D.path_antisymmetry
        (D.lower_realization_to_source_preloop
          hk defect hLowerRealization)

/-- Traced antisymmetric source-side preholonomy gives one-step traced defect
descent. -/
theorem descend_below
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    {k : Nat}
    (hk : k < target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n (k + 1)) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) :=
  D.toTracedSourceSideHolonomyGapDescent.descend_below hk

/-- Convert the traced antisymmetric preholonomy socket all the way to
bounded traced defect-instability descent. -/
def toBoundedTracedSourceSideDefectDescent
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    BoundedTracedSourceSideAtomProjectionDefectDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.toBoundedTracedSourceSideDefectDescent

/-- Traced antisymmetric source-side preholonomy excludes the target traced
feasible projection defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.terminal_traced_feasible_defect_of_target_defect

/-- Traced antisymmetric source-side preholonomy excludes the target traced
feasible projection defect. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- A bounded traced persistent defect trace is impossible under traced
antisymmetric source-side preholonomy. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace by antisymmetric source-side preholonomy descent.
-/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is impossible
under traced antisymmetric source-side preholonomy. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- Traced antisymmetric source-side preholonomy excludes a target traced
feasible defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Traced demand-level readout from antisymmetric source-side preholonomy.

The conclusion is double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedAntisymmetricSourceSideHolonomyGapDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  D.toTracedSourceSideHolonomyGapDescent
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

end BoundedTracedAntisymmetricSourceSideHolonomyGapDescent


end RepresentationArithmeticAtomProjectionDefect
