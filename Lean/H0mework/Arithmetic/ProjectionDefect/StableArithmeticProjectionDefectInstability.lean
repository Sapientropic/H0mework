import H0mework.Arithmetic.ProjectionDefect.AtomProjectionDefectCore

/-!
# Stable arithmetic projection-defect instability

This file gives the current hard gate a deliberately non-producer name.

The goal is not:

```text
SU7/source dynamics generates prime endpoint pairs
```

The goal is:

```text
source-side path/holonomy structure makes arithmetic projection defects
descend to a terminal no-third-sink contradiction
```

No theorem in this file assumes atom-pair successor realization.  The bounded
socket below asks directly for source-side defect descent
`defect at k+1 -> defect at k`.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

/-- Non-traced arithmetic projection-defect instability law.

This is a naming front door for `AtomProjectionDefectDescentDomain`: terminal
no-third-sink plus one-step defect descent.  It carries no endpoint candidate
and no prime-pair witness. -/
abbrev ArithmeticProjectionDefectInstabilityLaw
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n : Nat) :=
  AtomProjectionDefectDescentDomain
    Atomic SourceEvidence Residual n

namespace ArithmeticProjectionDefectInstabilityLaw

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n : Nat}

/-- A defect-instability law excludes arithmetic projection defects at every
finite shell.

This is the exact hard-door formulation: the proof proceeds by finite descent
to the terminal no-third-sink contradiction, not by constructing endpoint
atoms. -/
theorem no_stable_arithmetic_projection_defect
    (L :
      ArithmeticProjectionDefectInstabilityLaw
        Atomic SourceEvidence Residual n) :
    ∀ k : Nat,
      ¬ Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
  no_atom_projection_defect_by_finite_descent L

/-- A separately asserted persistent defect trace is impossible under the
instability law.  The useful operational theorem is
`no_stable_arithmetic_projection_defect`; this trace form records the intended
reading of "stable defect". -/
theorem no_persistent_arithmetic_projection_defect_trace
    (L :
      ArithmeticProjectionDefectInstabilityLaw
        Atomic SourceEvidence Residual n)
    {target : Nat}
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  (L.no_stable_arithmetic_projection_defect 0)
    (trace 0 (Nat.zero_le target))

/-- Demand-level readout from defect instability.

The conclusion is intentionally double-negated: this theorem says that the
missing-realization branch cannot persist as a stable projection defect.  It
does not return a prime pair. -/
theorem not_not_atom_realization_of_demand
    (L :
      ArithmeticProjectionDefectInstabilityLaw
        Atomic SourceEvidence Residual n)
    {k : Nat}
    (demand : RepRepairDemand SourceEvidence Residual n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_demand_by_finite_descent
    L demand

end ArithmeticProjectionDefectInstabilityLaw

/-- Bounded source-side descent certificate for one target shell.

This is the hard gate in its local form.  It does not ask for atom-pair
successor realization.  Instead, a future source/GT/crystal/holonomy theorem
must prove that a projection defect at shell `k+1` descends to one at shell
`k` throughout the bounded path down from `target`. -/
structure BoundedSourceSideAtomProjectionDefectDescent
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    AtomProjectionTerminalNoThirdSink
      Atomic SourceEvidence Residual n
  source_path_or_holonomy_structure : Prop
  source_path_or_holonomy_witness : source_path_or_holonomy_structure
  descend_below :
    ∀ {k : Nat},
      k < target ->
        source_path_or_holonomy_structure ->
          Nonempty
            (AtomProjectionDefect Atomic SourceEvidence Residual n (k + 1)) ->
          Nonempty
            (AtomProjectionDefect Atomic SourceEvidence Residual n k)

namespace BoundedSourceSideAtomProjectionDefectDescent

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n target : Nat}

/-- Restrict a bounded source-side descent certificate to a smaller target. -/
def restrict
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target)
    {target' : Nat}
    (hsub : target' ≤ target) :
    BoundedSourceSideAtomProjectionDefectDescent
      Atomic SourceEvidence Residual n target' where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_path_or_holonomy_structure := D.source_path_or_holonomy_structure
  source_path_or_holonomy_witness := D.source_path_or_holonomy_witness
  descend_below := by
    intro k hk hStructure hDefect
    exact D.descend_below (Nat.lt_of_lt_of_le hk hsub)
      hStructure hDefect

/-- Bounded source-side descent to terminal no-third-sink excludes the target
projection defect.

The induction uses only the supplied defect descent field.  It never invokes
an atom-pair successor-realization operator. -/
theorem terminal_defect_of_target_defect
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) ->
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n 0) := by
  induction target with
  | zero =>
      intro hDefect
      exact hDefect
  | succ k ih =>
      intro hDefect
      have hPrev :
          Nonempty
            (AtomProjectionDefect Atomic SourceEvidence Residual n k) :=
        D.descend_below (Nat.lt_succ_self k)
          D.source_path_or_holonomy_witness hDefect
      exact
        (ih (D.restrict (Nat.le_succ k))) hPrev

/-- Bounded source-side descent to terminal no-third-sink excludes the target
projection defect.

The target defect first descends to a terminal defect; the terminal
no-third-sink principle then rules that terminal defect out. -/
theorem no_target_arithmetic_projection_defect
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) := by
  intro hDefect
  exact
    no_terminal_atom_projection_defect_of_no_third_sink
      D.terminal_no_third_sink
      (D.terminal_defect_of_target_defect hDefect)

/-- A bounded persistent defect trace cannot exist under source-side descent.

This is only a stability exclusion: it uses the target member of the trace and
does not extract endpoint atoms. -/
theorem no_persistent_arithmetic_projection_defect_trace
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (AtomProjectionDefect Atomic SourceEvidence Residual n k)) :
    False :=
  D.no_target_arithmetic_projection_defect
    (trace target (Nat.le_refl target))

/-- Demand-level bounded source-side descent readout.  The result remains
double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_demand
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target)
    (demand : RepRepairDemand SourceEvidence Residual n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target := by
  intro hMissing
  exact D.no_target_arithmetic_projection_defect
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

end BoundedSourceSideAtomProjectionDefectDescent

/-- Traced feasible arithmetic projection-defect instability law.

This is the source/repair-trace preserving version of the same hard gate:
terminal no-third-sink plus traced defect descent. -/
abbrev TracedFeasibleArithmeticProjectionDefectInstabilityLaw
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n : Nat) :=
  TracedFeasibleAtomProjectionDefectDescentDomain
    SourcePath PhaseTrace SigmaTag ProducerTrace
    Atomic SourceEvidence Residual Source n

namespace TracedFeasibleArithmeticProjectionDefectInstabilityLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n : Nat}

/-- Traced defect instability excludes traced feasible arithmetic projection
defects at every finite shell, preserving sourcePath / phaseTrace / sigmaTag /
producerTrace in the descent. -/
theorem no_stable_traced_feasible_arithmetic_projection_defect
    (L :
      TracedFeasibleArithmeticProjectionDefectInstabilityLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n) :
    ∀ k : Nat,
      ¬ Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n k) :=
  no_traced_feasible_atom_projection_defect_by_finite_descent L

/-- A traced persistent defect trace is impossible under the traced instability
law. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (L :
      TracedFeasibleArithmeticProjectionDefectInstabilityLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    {target : Nat}
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  (L.no_stable_traced_feasible_arithmetic_projection_defect 0)
    (trace 0 (Nat.zero_le target))

/-- Traced demand-level readout from defect instability.

This keeps the output at `¬¬` and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_traced_feasible_demand
    (L :
      TracedFeasibleArithmeticProjectionDefectInstabilityLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n)
    {k : Nat}
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n k) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k :=
  not_not_atom_realization_of_traced_feasible_demand_by_finite_descent
    L demand

end TracedFeasibleArithmeticProjectionDefectInstabilityLaw

/-- Bounded traced source-side descent certificate for one target shell.

This is the trace-preserving local hard gate.  It asks source/holonomy
dynamics to descend traced feasible defects directly, with no atom-pair
successor-realization premise. -/
structure BoundedTracedSourceSideAtomProjectionDefectDescent
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop) (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (n target : Nat) where
  terminal_no_third_sink :
    TracedFeasibleAtomProjectionTerminalNoThirdSink
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n
  source_path_or_holonomy_structure : Prop
  source_path_or_holonomy_witness : source_path_or_holonomy_structure
  descend_below :
    ∀ {k : Nat},
      k < target ->
        source_path_or_holonomy_structure ->
          Nonempty
            (TracedFeasibleAtomProjectionDefect
              SourcePath PhaseTrace SigmaTag ProducerTrace
              Atomic SourceEvidence Residual Source n (k + 1)) ->
          Nonempty
            (TracedFeasibleAtomProjectionDefect
              SourcePath PhaseTrace SigmaTag ProducerTrace
              Atomic SourceEvidence Residual Source n k)

namespace BoundedTracedSourceSideAtomProjectionDefectDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- Restrict a bounded traced source-side descent certificate to a smaller
target. -/
def restrict
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    {target' : Nat}
    (hsub : target' ≤ target) :
    BoundedTracedSourceSideAtomProjectionDefectDescent
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target' where
  terminal_no_third_sink := D.terminal_no_third_sink
  source_path_or_holonomy_structure := D.source_path_or_holonomy_structure
  source_path_or_holonomy_witness := D.source_path_or_holonomy_witness
  descend_below := by
    intro k hk hStructure hDefect
    exact D.descend_below (Nat.lt_of_lt_of_le hk hsub)
      hStructure hDefect

/-- Bounded traced source-side descent to terminal no-third-sink excludes the
target traced feasible projection defect. -/
theorem terminal_traced_feasible_defect_of_target_defect
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) ->
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n 0) := by
  induction target with
  | zero =>
      intro hDefect
      exact hDefect
  | succ k ih =>
      intro hDefect
      have hPrev :
          Nonempty
            (TracedFeasibleAtomProjectionDefect
              SourcePath PhaseTrace SigmaTag ProducerTrace
              Atomic SourceEvidence Residual Source n k) :=
        D.descend_below (Nat.lt_succ_self k)
          D.source_path_or_holonomy_witness hDefect
      exact
        (ih (D.restrict (Nat.le_succ k))) hPrev

/-- Bounded traced source-side descent to terminal no-third-sink excludes the
target traced feasible projection defect. -/
theorem no_target_traced_feasible_arithmetic_projection_defect
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) := by
  intro hDefect
  exact
    no_terminal_traced_feasible_atom_projection_defect_of_no_third_sink
      D.terminal_no_third_sink
      (D.terminal_traced_feasible_defect_of_target_defect hDefect)

/-- A bounded traced persistent defect trace cannot exist under traced
source-side descent. -/
theorem no_persistent_traced_feasible_arithmetic_projection_defect_trace
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (trace :
      ∀ k : Nat, k ≤ target ->
        Nonempty
          (TracedFeasibleAtomProjectionDefect
            SourcePath PhaseTrace SigmaTag ProducerTrace
            Atomic SourceEvidence Residual Source n k)) :
    False :=
  D.no_target_traced_feasible_arithmetic_projection_defect
    (trace target (Nat.le_refl target))

/-- Traced demand-level bounded source-side descent readout.  The result
remains double-negated and does not extract endpoint atoms. -/
theorem not_not_atom_realization_of_target_traced_feasible_demand
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (demand :
      TracedFeasibleRepRepairDemand
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source n target) :
    ¬¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = target := by
  intro hMissing
  exact D.no_target_traced_feasible_arithmetic_projection_defect
    ⟨{ demand := demand, noAtomRealization := hMissing }⟩

end BoundedTracedSourceSideAtomProjectionDefectDescent


end RepresentationArithmeticAtomProjectionDefect
