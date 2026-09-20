import H0mework.Arithmetic.SourceAtoms.TerminalDischargedSourceReturnForcing

/-!
# Uniform source-return forcing instability

This file upgrades the bounded return-forcing socket to a uniform all-shell
hard gate:

```text
uniform source return forcing
+ residual no-return
+ terminal no-third-sink
-> arithmetic projection defects cannot stably exist at any finite shell
```

The uniform law is still not a producer theorem.  It does not ask a source
grammar to generate prime endpoints; it only says that stable missing
atom-projection branches are impossible once source dynamics force the
forbidden lower-to-upper return in every shell.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Uniform coexistence-state source return forcing.

This is the all-shell version of
`BoundedDefectRealizationSourceReturnForcing`: for every upper defect at
`k+1`, a lower atom-pair realization at `k` forces a source path from the
lowered source evidence back to the upper evidence. -/
structure UniformDefectRealizationSourceReturnForcing
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  lower_realization_returns :
    ∀ {k : Nat},
      (defect :
        AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          Source.path
            (source_descent.lowerEvidence defect.demand)
            defect.demand.evidence

namespace UniformDefectRealizationSourceReturnForcing

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- Restrict a uniform return-forcing law to any bounded target. -/
def toBounded
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (target : Nat) :
    BoundedDefectRealizationSourceReturnForcing
      Atomic SourceEvidence Residual Source n target where
  source_descent := U.source_descent
  lower_realization_returns := by
    intro k _ defect realization
    exact U.lower_realization_returns defect realization

/-- Uniform return forcing plus residual no-return and terminal no-third-sink
gives the global finite-descent instability law. -/
def toArithmeticProjectionDefectInstabilityLaw
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ArithmeticProjectionDefectInstabilityLaw
      Atomic SourceEvidence Residual n where
  terminal_no_third_sink := terminal_no_third_sink
  descend := by
    intro k hDefect
    rcases hDefect with ⟨defect⟩
    exact ⟨{
      demand := lowerDemandOfSourceStep U.source_descent defect.demand
      noAtomRealization := by
        intro realization
        exact
          SourceResidualPathNonincreasing.no_return_after_source_descent
            path_residual_nonincreasing
            U.source_descent
            defect.demand
            (U.lower_realization_returns defect realization)
    }⟩

/-- Materializing terminal discharge fills the uniform instability law. -/
def toArithmeticProjectionDefectInstabilityLawOfMaterializingTerminal
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ArithmeticProjectionDefectInstabilityLaw
      Atomic SourceEvidence Residual n :=
  U.toArithmeticProjectionDefectInstabilityLaw
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    path_residual_nonincreasing

/-- Nonabsorbed terminal discharge fills the uniform instability law through
faithful projection definedness. -/
def toArithmeticProjectionDefectInstabilityLawOfNonabsorbedTerminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ArithmeticProjectionDefectInstabilityLaw
      Atomic SourceEvidence Residual n :=
  U.toArithmeticProjectionDefectInstabilityLawOfMaterializingTerminal
    (atomProjectionTerminalMaterializingNoThirdSinkOfNonabsorbed terminal)
    path_residual_nonincreasing

/-- Uniform return forcing excludes stable arithmetic projection defects at
every finite shell. -/
theorem no_stable_arithmetic_projection_defect
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  (U.toArithmeticProjectionDefectInstabilityLaw
    terminal_no_third_sink path_residual_nonincreasing)
    |>.no_stable_arithmetic_projection_defect

/-- A target-shell defect extracts a first-class bounded persistent defect
trace under uniform source-return forcing. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat}
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  (U.toBounded target
    |>.toSourceNoReturnGapDescent
      terminal_no_third_sink path_residual_nonincreasing)
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible under uniform
source-return forcing. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat}
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  (U.toBounded target
    |>.toSourceNoReturnGapDescent
      terminal_no_third_sink path_residual_nonincreasing)
    |>.no_bounded_persistent_arithmetic_projection_defect_trace trace

/-- Uniform source-return forcing excludes a target defect through the
explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat} :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (U.toBounded target
    |>.toSourceNoReturnGapDescent
      terminal_no_third_sink path_residual_nonincreasing)
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Uniform return forcing plus materializing terminal discharge excludes
stable arithmetic projection defects at every finite shell. -/
theorem no_stable_arithmetic_projection_defect_of_materializing_terminal
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  (U.toArithmeticProjectionDefectInstabilityLawOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_stable_arithmetic_projection_defect

/-- Uniform return forcing plus nonabsorbed terminal discharge excludes stable
arithmetic projection defects at every finite shell. -/
theorem no_stable_arithmetic_projection_defect_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  (U.toArithmeticProjectionDefectInstabilityLawOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_stable_arithmetic_projection_defect

/-- Demand-level double-negated readout from uniform return forcing. -/
theorem not_not_atom_realization_of_demand
    (U :
      UniformDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  (U.toArithmeticProjectionDefectInstabilityLaw
    terminal_no_third_sink path_residual_nonincreasing)
    |>.not_not_atom_realization_of_demand demand

end UniformDefectRealizationSourceReturnForcing

/-- Uniform anchored source return forcing.

This is the preferred extraction shape for native source dynamics: construct
a defect-conditioned anchor and two source paths in every shell, then compose
them to the uniform lower-to-upper return. -/
structure UniformDefectConditionedSourceAnchorReturnForcing
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) where
  source_descent :
    SourceDemandOneStepDescent SourceEvidence Residual n
  path_transitivity :
    SourcePathTransitivity SourceEvidence Source
  sourceAnchor :
    ∀ {k : Nat},
      (defect :
        AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (defect :
        AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (source_descent.lowerEvidence defect.demand)
          (sourceAnchor defect realization)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (defect :
        AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (sourceAnchor defect realization)
          defect.demand.evidence

namespace UniformDefectConditionedSourceAnchorReturnForcing

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- Uniform anchored return forcing composes to uniform direct return forcing.
-/
def toUniformSourceReturnForcing
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n) :
    UniformDefectRealizationSourceReturnForcing
      Atomic SourceEvidence Residual Source n where
  source_descent := A.source_descent
  lower_realization_returns := by
    intro k defect realization
    exact
      A.path_transitivity.trans
        (A.lower_to_anchor defect realization)
        (A.anchor_returns_to_upper defect realization)

/-- Uniform anchored return forcing excludes stable arithmetic projection
defects at every finite shell. -/
theorem no_stable_arithmetic_projection_defect
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  A.toUniformSourceReturnForcing.no_stable_arithmetic_projection_defect
    terminal_no_third_sink path_residual_nonincreasing

/-- A target-shell defect extracts a first-class bounded persistent defect
trace under uniform anchored source-return forcing. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat}
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  A.toUniformSourceReturnForcing
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      terminal_no_third_sink path_residual_nonincreasing target_defect

/-- A first-class bounded persistent defect trace is impossible under uniform
anchored source-return forcing. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat}
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  A.toUniformSourceReturnForcing
    |>.no_bounded_persistent_arithmetic_projection_defect_trace
      terminal_no_third_sink path_residual_nonincreasing trace

/-- Uniform anchored source-return forcing excludes a target defect through
the explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal_no_third_sink :
      AtomProjectionTerminalNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    {target : Nat} :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  A.toUniformSourceReturnForcing
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace
      terminal_no_third_sink path_residual_nonincreasing

/-- Uniform anchored return forcing plus materializing terminal discharge
excludes stable arithmetic projection defects at every finite shell. -/
theorem no_stable_arithmetic_projection_defect_of_materializing_terminal
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  A.toUniformSourceReturnForcing
    |>.no_stable_arithmetic_projection_defect_of_materializing_terminal
      terminal path_residual_nonincreasing

/-- Uniform anchored return forcing plus nonabsorbed terminal discharge
excludes stable arithmetic projection defects at every finite shell. -/
theorem no_stable_arithmetic_projection_defect_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      UniformDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  A.toUniformSourceReturnForcing
    |>.no_stable_arithmetic_projection_defect_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing

end UniformDefectConditionedSourceAnchorReturnForcing

/-- Uniform traced coexistence-state source return forcing. -/
structure UniformTracedDefectRealizationSourceReturnForcing
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
  lower_realization_returns :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          Source.path
            (source_descent.lowerEvidence defect.demand.demand.demand)
            defect.demand.demand.demand.evidence

namespace UniformTracedDefectRealizationSourceReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- Restrict a uniform traced return-forcing law to any bounded target. -/
def toBounded
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (target : Nat) :
    BoundedTracedDefectRealizationSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target where
  source_descent := U.source_descent
  step_path := U.step_path
  trace_descent := U.trace_descent
  lower_realization_returns := by
    intro k _ defect realization
    exact U.lower_realization_returns defect realization

/-- Uniform traced return forcing plus residual no-return and terminal
no-third-sink gives the global traced finite-descent instability law. -/
def toTracedArithmeticProjectionDefectInstabilityLaw
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
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
      Atomic SourceEvidence Residual Source n where
  terminal_no_third_sink := terminal_no_third_sink
  descend := by
    intro k hDefect
    rcases hDefect with ⟨defect⟩
    exact ⟨{
      demand :=
        lowerTracedFeasibleDemandOfSourceStep
          U.source_descent U.step_path U.trace_descent defect.demand
      noAtomRealization := by
        intro realization
        exact
          SourceResidualPathNonincreasing.no_return_after_source_descent
            path_residual_nonincreasing
            U.source_descent
            defect.demand.demand.demand
            (U.lower_realization_returns defect realization)
    }⟩

/-- Materializing traced terminal discharge fills the uniform traced
instability law. -/
def toTracedArithmeticProjectionDefectInstabilityLawOfMaterializingTerminal
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    TracedFeasibleArithmeticProjectionDefectInstabilityLaw
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  U.toTracedArithmeticProjectionDefectInstabilityLaw
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    path_residual_nonincreasing

/-- Raw-code nonabsorbed terminal discharge fills the uniform traced
instability law. -/
def toTracedArithmeticProjectionDefectInstabilityLawOfCodeNonabsorbedTerminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    TracedFeasibleArithmeticProjectionDefectInstabilityLaw
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n :=
  U.toTracedArithmeticProjectionDefectInstabilityLaw
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeNonabsorbed
      terminal)
    path_residual_nonincreasing

/-- Uniform traced return forcing excludes stable traced feasible projection
defects at every finite shell. -/
theorem no_stable_traced_feasible_arithmetic_projection_defect
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
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

/-- A target-shell traced feasible defect extracts a first-class bounded
persistent traced feasible defect trace under uniform traced source-return
forcing. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
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
  (U.toBounded target
    |>.toTracedSourceNoReturnGapDescent
      terminal_no_third_sink path_residual_nonincreasing)
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible under uniform traced source-return forcing. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
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
  (U.toBounded target
    |>.toTracedSourceNoReturnGapDescent
      terminal_no_third_sink path_residual_nonincreasing)
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- Uniform traced source-return forcing excludes a target traced feasible
defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
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
  (U.toBounded target
    |>.toTracedSourceNoReturnGapDescent
      terminal_no_third_sink path_residual_nonincreasing)
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Uniform traced return forcing plus raw-code nonabsorbed terminal discharge
excludes stable traced feasible projection defects at every finite shell. -/
theorem no_stable_traced_feasible_arithmetic_projection_defect_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (U :
      UniformTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  (U.toTracedArithmeticProjectionDefectInstabilityLawOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_stable_traced_feasible_arithmetic_projection_defect

end UniformTracedDefectRealizationSourceReturnForcing

/-- Uniform traced anchored source return forcing. -/
structure UniformTracedDefectConditionedSourceAnchorReturnForcing
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
  path_transitivity :
    SourcePathTransitivity SourceEvidence Source
  sourceAnchor :
    ∀ {k : Nat},
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1)) ->
        (∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k) ->
          SourceEvidence
  lower_to_anchor :
    ∀ {k : Nat}
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (source_descent.lowerEvidence defect.demand.demand.demand)
          (sourceAnchor defect realization)
  anchor_returns_to_upper :
    ∀ {k : Nat}
      (defect :
        TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n (k + 1))
      (realization :
        ∃ p : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy p = k),
        Source.path
          (sourceAnchor defect realization)
          defect.demand.demand.demand.evidence

namespace UniformTracedDefectConditionedSourceAnchorReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- Uniform traced anchored return forcing composes to uniform traced direct
return forcing. -/
def toUniformTracedSourceReturnForcing
    (A :
      UniformTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    UniformTracedDefectRealizationSourceReturnForcing
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n where
  source_descent := A.source_descent
  step_path := A.step_path
  trace_descent := A.trace_descent
  lower_realization_returns := by
    intro k defect realization
    exact
      A.path_transitivity.trans
        (A.lower_to_anchor defect realization)
        (A.anchor_returns_to_upper defect realization)

/-- Uniform traced anchored return forcing excludes stable traced feasible
projection defects at every finite shell. -/
theorem no_stable_traced_feasible_arithmetic_projection_defect
    (A :
      UniformTracedDefectConditionedSourceAnchorReturnForcing
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
  A.toUniformTracedSourceReturnForcing
    |>.no_stable_traced_feasible_arithmetic_projection_defect
      terminal_no_third_sink path_residual_nonincreasing

/-- A target-shell traced feasible defect extracts a first-class bounded
persistent traced feasible defect trace under uniform traced anchored
source-return forcing. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
    (A :
      UniformTracedDefectConditionedSourceAnchorReturnForcing
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
  A.toUniformTracedSourceReturnForcing
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      terminal_no_third_sink path_residual_nonincreasing target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible under uniform traced anchored source-return forcing. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
    (A :
      UniformTracedDefectConditionedSourceAnchorReturnForcing
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
  A.toUniformTracedSourceReturnForcing
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      terminal_no_third_sink path_residual_nonincreasing trace

/-- Uniform traced anchored source-return forcing excludes a target traced
feasible defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
    (A :
      UniformTracedDefectConditionedSourceAnchorReturnForcing
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
  A.toUniformTracedSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace
      terminal_no_third_sink path_residual_nonincreasing

/-- Uniform traced anchored return forcing plus raw-code nonabsorbed terminal
discharge excludes stable traced feasible projection defects at every finite
shell. -/
theorem no_stable_traced_feasible_arithmetic_projection_defect_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      UniformTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  A.toUniformTracedSourceReturnForcing
    |>.no_stable_traced_feasible_arithmetic_projection_defect_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing

end UniformTracedDefectConditionedSourceAnchorReturnForcing


end RepresentationArithmeticAtomProjectionDefect
