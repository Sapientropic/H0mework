import H0mework.Arithmetic.ProjectionDefect.DefectConditionedSourceReturnForcing
import H0mework.Arithmetic.SourceAtoms.TracedTerminalCodeNoThirdSink

/-!
# Terminal-discharged source return forcing

This file connects the thinner source-return socket to terminal discharge:

```text
source return forcing
+ residual no-return
+ materializing / nonabsorbed terminal no-third-sink
-> no stable arithmetic projection defect
```

This is not a producer theorem.  It does not ask the source grammar to generate
prime endpoints.  It says that a stable arithmetic projection defect cannot
coexist with a source-dynamic return-forcing law and terminal discharge.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

namespace BoundedDefectRealizationSourceReturnForcing

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Materializing terminal discharge fills the return-forcing hard gate. -/
def toSourceNoReturnGapDescentOfMaterializingTerminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target :=
  F.toSourceNoReturnGapDescent
    (atomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    path_residual_nonincreasing

/-- Nonabsorbed terminal discharge fills the return-forcing hard gate through
faithful projection definedness. -/
def toSourceNoReturnGapDescentOfNonabsorbedTerminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target :=
  F.toSourceNoReturnGapDescentOfMaterializingTerminal
    (atomProjectionTerminalMaterializingNoThirdSinkOfNonabsorbed terminal)
    path_residual_nonincreasing

/-- Return forcing excludes target defects with a materializing terminal
discharge and residual no-return. -/
theorem no_target_arithmetic_projection_defect_of_materializing_terminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (F.toSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_arithmetic_projection_defect

/-- Return forcing excludes bounded persistent defect traces with a
materializing terminal discharge and residual no-return. -/
theorem no_persistent_arithmetic_projection_defect_trace_of_materializing_terminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  (F.toSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace
with a materializing terminal discharge and residual no-return. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect_of_materializing_terminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  (F.toSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible with a
materializing terminal discharge and residual no-return. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace_of_materializing_terminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  (F.toSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_bounded_persistent_arithmetic_projection_defect_trace trace

/-- A materializing terminal discharge excludes a target defect through the
explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace_of_materializing_terminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (F.toSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level double-negated readout with a materializing terminal
discharge. -/
theorem not_not_atom_realization_of_target_demand_of_materializing_terminal
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (F.toSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.not_not_atom_realization_of_target_demand demand

/-- Return forcing excludes target defects with a nonabsorbed terminal
discharge and residual no-return. -/
theorem no_target_arithmetic_projection_defect_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (F.toSourceNoReturnGapDescentOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_arithmetic_projection_defect

/-- Return forcing excludes bounded persistent defect traces with a
nonabsorbed terminal discharge and residual no-return. -/
theorem no_persistent_arithmetic_projection_defect_trace_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  (F.toSourceNoReturnGapDescentOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_persistent_arithmetic_projection_defect_trace trace

/-- A target defect extracts a first-class bounded persistent defect trace
with a nonabsorbed terminal discharge and residual no-return. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  (F.toSourceNoReturnGapDescentOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent defect trace is impossible with a
nonabsorbed terminal discharge and residual no-return. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  (F.toSourceNoReturnGapDescentOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_bounded_persistent_arithmetic_projection_defect_trace trace

/-- A nonabsorbed terminal discharge excludes a target defect through the
explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  (F.toSourceNoReturnGapDescentOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level double-negated readout with a nonabsorbed terminal
discharge. -/
theorem not_not_atom_realization_of_target_demand_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (F :
      BoundedDefectRealizationSourceReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (F.toSourceNoReturnGapDescentOfNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.not_not_atom_realization_of_target_demand demand

end BoundedDefectRealizationSourceReturnForcing

namespace BoundedDefectConditionedSourceAnchorReturnForcing

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Anchored return forcing plus materializing terminal discharge fills the
source no-return gap-descent socket. -/
def toSourceNoReturnGapDescentOfMaterializingTerminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target :=
  A.toSourceReturnForcing
    |>.toSourceNoReturnGapDescentOfMaterializingTerminal
      terminal path_residual_nonincreasing

/-- Anchored return forcing plus nonabsorbed terminal discharge fills the
source no-return gap-descent socket. -/
def toSourceNoReturnGapDescentOfNonabsorbedTerminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedSourceNoReturnGapDescent
      Atomic SourceEvidence Residual Source n target :=
  A.toSourceReturnForcing
    |>.toSourceNoReturnGapDescentOfNonabsorbedTerminal
      terminal path_residual_nonincreasing

/-- Anchored return forcing excludes target defects with a materializing
terminal discharge and residual no-return. -/
theorem no_target_arithmetic_projection_defect_of_materializing_terminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  A.toSourceReturnForcing
    |>.no_target_arithmetic_projection_defect_of_materializing_terminal
      terminal path_residual_nonincreasing

/-- Anchored return forcing excludes bounded persistent defect traces with a
materializing terminal discharge and residual no-return. -/
theorem no_persistent_arithmetic_projection_defect_trace_of_materializing_terminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  A.toSourceReturnForcing
    |>.no_persistent_arithmetic_projection_defect_trace_of_materializing_terminal
      terminal path_residual_nonincreasing trace

/-- A target defect extracts a first-class bounded persistent defect trace
from anchored return forcing with a materializing terminal discharge. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect_of_materializing_terminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  A.toSourceReturnForcing
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect_of_materializing_terminal
      terminal path_residual_nonincreasing target_defect

/-- A first-class bounded persistent defect trace is impossible from anchored
return forcing with a materializing terminal discharge. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace_of_materializing_terminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  A.toSourceReturnForcing
    |>.no_bounded_persistent_arithmetic_projection_defect_trace_of_materializing_terminal
      terminal path_residual_nonincreasing trace

/-- Anchored materializing terminal discharge excludes a target defect through
the explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace_of_materializing_terminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  A.toSourceReturnForcing
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace_of_materializing_terminal
      terminal path_residual_nonincreasing

/-- Demand-level double-negated readout from anchored return forcing with a
materializing terminal discharge. -/
theorem not_not_atom_realization_of_target_demand_of_materializing_terminal
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalMaterializingNoThirdSink
        Atomic SourceEvidence Residual n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  A.toSourceReturnForcing
    |>.not_not_atom_realization_of_target_demand_of_materializing_terminal
      terminal path_residual_nonincreasing demand

/-- Anchored return forcing excludes target defects with a nonabsorbed
terminal discharge and residual no-return. -/
theorem no_target_arithmetic_projection_defect_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  A.toSourceReturnForcing
    |>.no_target_arithmetic_projection_defect_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing

/-- Anchored return forcing excludes bounded persistent defect traces with a
nonabsorbed terminal discharge and residual no-return. -/
theorem no_persistent_arithmetic_projection_defect_trace_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  A.toSourceReturnForcing
    |>.no_persistent_arithmetic_projection_defect_trace_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing trace

/-- A target defect extracts a first-class bounded persistent defect trace
from anchored return forcing with a nonabsorbed terminal discharge. -/
theorem boundedPersistentAtomProjectionDefectTraceOfTargetDefect_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target :=
  A.toSourceReturnForcing
    |>.boundedPersistentAtomProjectionDefectTraceOfTargetDefect_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing target_defect

/-- A first-class bounded persistent defect trace is impossible from anchored
return forcing with a nonabsorbed terminal discharge. -/
theorem no_bounded_persistent_arithmetic_projection_defect_trace_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentAtomProjectionDefectTrace
        Atomic SourceEvidence Residual n target) :
    False :=
  A.toSourceReturnForcing
    |>.no_bounded_persistent_arithmetic_projection_defect_trace_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing trace

/-- Anchored nonabsorbed terminal discharge excludes a target defect through
the explicit bounded persistent trace midpoint. -/
theorem no_target_arithmetic_projection_defect_via_extracted_persistent_trace_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) :=
  A.toSourceReturnForcing
    |>.no_target_arithmetic_projection_defect_via_extracted_persistent_trace_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing

/-- Demand-level double-negated readout from anchored return forcing with a
nonabsorbed terminal discharge. -/
theorem not_not_atom_realization_of_target_demand_of_nonabsorbed_terminal
    {Projection :
      FaithfulAtomProjectionFunctor Atomic SourceEvidence n Residual}
    (A :
      BoundedDefectConditionedSourceAnchorReturnForcing
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      AtomProjectionTerminalNonabsorbedNoThirdSink
        Atomic SourceEvidence Residual n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  A.toSourceReturnForcing
    |>.not_not_atom_realization_of_target_demand_of_nonabsorbed_terminal
      terminal path_residual_nonincreasing demand

end BoundedDefectConditionedSourceAnchorReturnForcing

namespace BoundedTracedDefectRealizationSourceReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Materializing traced terminal discharge fills the traced return-forcing
hard gate. -/
def toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  F.toTracedSourceNoReturnGapDescent
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfMaterializing terminal)
    path_residual_nonincreasing

/-- Raw-code nonabsorbed terminal discharge fills the traced return-forcing
hard gate. -/
def toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  F.toTracedSourceNoReturnGapDescent
    (tracedFeasibleAtomProjectionTerminalNoThirdSinkOfCodeNonabsorbed
      terminal)
    path_residual_nonincreasing

/-- Traced return forcing excludes target defects with a materializing terminal
discharge and residual no-return. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_of_materializing_terminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (F.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- Traced return forcing excludes bounded persistent traces with a
materializing terminal discharge and residual no-return. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace_of_materializing_terminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  (F.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace with a materializing terminal discharge. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect_of_materializing_terminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  (F.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible with a materializing terminal discharge. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace_of_materializing_terminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  (F.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- A traced materializing terminal discharge excludes a target defect through
the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace_of_materializing_terminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (F.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level traced double-negated readout with a materializing terminal
discharge. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand_of_materializing_terminal
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (F.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    terminal path_residual_nonincreasing)
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

/-- Traced return forcing excludes target defects with a raw-code
nonabsorbed terminal discharge and residual no-return. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (F.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_traced_feasible_arithmetic_projection_defect

/-- Traced return forcing excludes bounded persistent traces with a raw-code
nonabsorbed terminal discharge and residual no-return. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  (F.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace with a raw-code nonabsorbed terminal discharge.
-/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  (F.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect
      target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible with a raw-code nonabsorbed terminal discharge. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  (F.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace
      trace

/-- A raw-code nonabsorbed terminal discharge excludes a target traced feasible
defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  (F.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace

/-- Demand-level traced double-negated readout with a raw-code nonabsorbed
terminal discharge. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (F :
      BoundedTracedDefectRealizationSourceReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  (F.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    terminal path_residual_nonincreasing)
    |>.not_not_atom_realization_of_target_traced_feasible_demand demand

end BoundedTracedDefectRealizationSourceReturnForcing

namespace BoundedTracedDefectConditionedSourceAnchorReturnForcing

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Traced anchored return forcing plus materializing terminal discharge fills
the traced source no-return gap-descent socket. -/
def toTracedSourceNoReturnGapDescentOfMaterializingTerminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  A.toTracedSourceReturnForcing
    |>.toTracedSourceNoReturnGapDescentOfMaterializingTerminal
      terminal path_residual_nonincreasing

/-- Traced anchored return forcing plus raw-code nonabsorbed terminal discharge
fills the traced source no-return gap-descent socket. -/
def toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    BoundedTracedSourceNoReturnGapDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  A.toTracedSourceReturnForcing
    |>.toTracedSourceNoReturnGapDescentOfCodeNonabsorbedTerminal
      terminal path_residual_nonincreasing

/-- Traced anchored return forcing excludes target defects with a materializing
terminal discharge and residual no-return. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_of_materializing_terminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  A.toTracedSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect_of_materializing_terminal
      terminal path_residual_nonincreasing

/-- Traced anchored return forcing excludes bounded persistent traces with a
materializing terminal discharge and residual no-return. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace_of_materializing_terminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  A.toTracedSourceReturnForcing
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace_of_materializing_terminal
      terminal path_residual_nonincreasing trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace from anchored return forcing with a materializing
terminal discharge. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect_of_materializing_terminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  A.toTracedSourceReturnForcing
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect_of_materializing_terminal
      terminal path_residual_nonincreasing target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible from anchored return forcing with a materializing terminal
discharge. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace_of_materializing_terminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  A.toTracedSourceReturnForcing
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace_of_materializing_terminal
      terminal path_residual_nonincreasing trace

/-- Anchored traced materializing terminal discharge excludes a target defect
through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace_of_materializing_terminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  A.toTracedSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace_of_materializing_terminal
      terminal path_residual_nonincreasing

/-- Demand-level traced double-negated readout from anchored return forcing
with a materializing terminal discharge. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand_of_materializing_terminal
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalMaterializingNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  A.toTracedSourceReturnForcing
    |>.not_not_atom_realization_of_target_traced_feasible_demand_of_materializing_terminal
      terminal path_residual_nonincreasing demand

/-- Traced anchored return forcing excludes target defects with a raw-code
nonabsorbed terminal discharge and residual no-return. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  A.toTracedSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing

/-- Traced anchored return forcing excludes bounded persistent traces with a
raw-code nonabsorbed terminal discharge and residual no-return. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  A.toTracedSourceReturnForcing
    |>.no_persistent_traced_feasible_arithmetic_projection_defect_trace_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing trace

/-- A target traced feasible defect extracts a first-class bounded persistent
traced feasible defect trace from anchored return forcing with a raw-code
nonabsorbed terminal discharge. -/
theorem boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target :=
  A.toTracedSourceReturnForcing
    |>.boundedPersistentTracedFeasibleAtomProjectionDefectTraceOfTargetDefect_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing target_defect

/-- A first-class bounded persistent traced feasible defect trace is
impossible from anchored return forcing with a raw-code nonabsorbed terminal
discharge. -/
theorem no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (trace :
      BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    False :=
  A.toTracedSourceReturnForcing
    |>.no_bounded_persistent_traced_feasible_arithmetic_projection_defect_trace_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing trace

/-- Anchored raw-code nonabsorbed terminal discharge excludes a target traced
feasible defect through the explicit bounded persistent trace midpoint. -/
theorem no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :=
  A.toTracedSourceReturnForcing
    |>.no_target_traced_feasible_arithmetic_projection_defect_via_extracted_persistent_trace_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing

/-- Demand-level traced double-negated readout from anchored return forcing
with a raw-code nonabsorbed terminal discharge. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand_of_code_nonabsorbed_terminal
    {Projection :
      AtomicEndpointCodeProjection Atomic SourceEvidence n Residual}
    (A :
      BoundedTracedDefectConditionedSourceAnchorReturnForcing
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (terminal :
      TracedFeasibleAtomProjectionTerminalCodeNonabsorbedNoThirdSink
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n Projection)
    (path_residual_nonincreasing :
      SourceResidualPathNonincreasing SourceEvidence Residual Source)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target :=
  A.toTracedSourceReturnForcing
    |>.not_not_atom_realization_of_target_traced_feasible_demand_of_code_nonabsorbed_terminal
      terminal path_residual_nonincreasing demand

end BoundedTracedDefectConditionedSourceAnchorReturnForcing


end RepresentationArithmeticAtomProjectionDefect
