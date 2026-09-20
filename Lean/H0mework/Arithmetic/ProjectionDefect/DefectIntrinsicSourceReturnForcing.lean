import H0mework.Arithmetic.SourceAtoms.UniformSourceReturnForcingInstability

/-!
# Defect-intrinsic source return forcing

This file isolates the stronger hard-door source obligation:

```text
upper traced projection defect at k+1
-> source return from lowered evidence to upper evidence
```

Unlike the older coexistence socket, this does not take a lower atom-pair
realization as an input.  It is therefore a sharper source-side target for
GT/crystal/branching dynamics: prove that a claimed stable projection defect
itself forces the forbidden return path, then residual no-return excludes the
stable defect branch.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Uniform traced source return forcing intrinsic to the projection defect.

The return path is read from the defect / trace itself.  No lower atom-pair
realization or endpoint candidate is supplied to this field. -/
structure UniformTracedDefectIntrinsicSourceReturnForcing
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  step_path :
    ResidualStepSourcePathCompatibility SourceEvidence Residual Source
  trace_descent :
    SourceRepairTraceDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n
  defect_returns :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1)) ->
        Source.path
          (source_descent.lowerEvidence defect.demand.demand.demand)
          defect.demand.demand.demand.evidence

namespace UniformTracedDefectIntrinsicSourceReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- A defect-intrinsic return law is stronger than the old coexistence-state
return-forcing socket: the lower realization input is ignored. -/
def toUniformTracedDefectRealizationSourceReturnForcing
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    UniformTracedDefectRealizationSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  source_descent := U.source_descent
  step_path := U.step_path
  trace_descent := U.trace_descent
  lower_realization_returns := by
    intro _k defect _realization
    exact U.defect_returns defect

/-- Intrinsic return forcing plus residual no-return and terminal no-third-sink
gives the traced finite-descent instability law. -/
def toTracedArithmeticProjectionDefectInstabilityLaw
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    TracedFeasibleArithmeticProjectionDefectInstabilityLaw
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  U.toUniformTracedDefectRealizationSourceReturnForcing
    |>.toTracedArithmeticProjectionDefectInstabilityLaw
      terminal_no_third_sink path_residual_nonincreasing

/-- Defect-intrinsic source return forcing excludes stable traced feasible
projection defects. -/
theorem no_stable_traced_feasible_arithmetic_projection_defect
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  (U.toTracedArithmeticProjectionDefectInstabilityLaw
    terminal_no_third_sink path_residual_nonincreasing)
    |>.no_stable_traced_feasible_arithmetic_projection_defect

/-- A target-shell defect extracts a first-class bounded persistent traced
defect trace under defect-intrinsic source return forcing. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat}
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  U.toUniformTracedDefectRealizationSourceReturnForcing
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      terminal_no_third_sink path_residual_nonincreasing target_defect

/-- Bounded persistent traced defect traces are impossible under
defect-intrinsic source return forcing. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat}
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  U.toUniformTracedDefectRealizationSourceReturnForcing
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      terminal_no_third_sink path_residual_nonincreasing trace

/-- Target traced feasible projection defects are impossible through the
explicit bounded-persistent-trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat} :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  U.toUniformTracedDefectRealizationSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
      terminal_no_third_sink path_residual_nonincreasing

/-- Demand-level double-negated atom-pair readout from defect-intrinsic source
return forcing.  No endpoint witness is extracted. -/
theorem not_not_atom_realization_of_traced_feasible_demand
    (U :
      UniformTracedDefectIntrinsicSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      TracedFeasibleAtomProjectionTerminalNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {k : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  (U.toTracedArithmeticProjectionDefectInstabilityLaw
    terminal_no_third_sink path_residual_nonincreasing)
    |>.not_not_atom_realization_of_traced_feasible_demand demand

end UniformTracedDefectIntrinsicSourceReturnForcing


end RepresentationArithmeticAtomProjectionDefect
