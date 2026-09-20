import H0mework.Arithmetic.ProjectionDefect.BoundedPersistentProjectionDefectTrace

/-!
# Bounded persistent trace extraction

This file turns a claimed target-shell projection defect plus source-side
descent into the first-class bounded persistence witness.

The direction is:

```text
target defect
+ source-side defect descent below target
-> defect at every shell k <= target
-> bounded persistent projection-defect trace
```

This is extraction of the stable-gap object, not endpoint production.
-/

namespace RepresentationArithmeticAtomProjectionDefect

universe u

namespace BoundedSourceSideAtomProjectionDefectDescent

variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {n target : Nat}

/-- A target-shell defect descends to every lower shell below the same bound.
-/
theorem defect_at_of_target_defect
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target))
    {k : Nat}
    (hk : k ≤ target) :
    Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n k) := by
  induction target generalizing k with
  | zero =>
      have hk_zero : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact target_defect
  | succ target' ih =>
      by_cases htop : k = target' + 1
      · subst k
        exact target_defect
      · have hk_lt_top : k < target' + 1 :=
          Nat.lt_of_le_of_ne hk htop
        have hk_le_prev : k ≤ target' :=
          Nat.le_of_lt_succ hk_lt_top
        have prev_defect :
            Nonempty
              (AtomProjectionDefect
                Atomic SourceEvidence Residual n target') :=
          D.descend_below (Nat.lt_succ_self target')
            D.source_path_or_holonomy_witness target_defect
        exact
          ih (D.restrict (Nat.le_succ target'))
            prev_defect hk_le_prev

/-- A target-shell defect plus bounded source-side descent extracts a
first-class bounded persistent defect trace. -/
theorem persistentTraceOfTargetDefect
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target)
    (target_defect :
      Nonempty
        (AtomProjectionDefect Atomic SourceEvidence Residual n target)) :
    BoundedPersistentAtomProjectionDefectTrace
      Atomic SourceEvidence Residual n target := by
  exact {
    defect_at := by
      intro k hk
      exact D.defect_at_of_target_defect target_defect hk
  }

/-- Source-side descent turns a target defect into a persistent trace, and the
same descent law rules that trace out. -/
theorem no_target_defect_via_extracted_persistent_trace
    (D :
      BoundedSourceSideAtomProjectionDefectDescent
        Atomic SourceEvidence Residual n target) :
    ¬ Nonempty
      (AtomProjectionDefect Atomic SourceEvidence Residual n target) := by
  intro target_defect
  exact
    (D.persistentTraceOfTargetDefect target_defect)
      |>.false_of_bounded_descent D

end BoundedSourceSideAtomProjectionDefectDescent

namespace BoundedTracedSourceSideAtomProjectionDefectDescent

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {n target : Nat}

/-- A target-shell traced feasible defect descends to every lower shell below
the same bound. -/
theorem defect_at_of_target_defect
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target))
    {k : Nat}
    (hk : k ≤ target) :
    Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n k) := by
  induction target generalizing k with
  | zero =>
      have hk_zero : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact target_defect
  | succ target' ih =>
      by_cases htop : k = target' + 1
      · subst k
        exact target_defect
      · have hk_lt_top : k < target' + 1 :=
          Nat.lt_of_le_of_ne hk htop
        have hk_le_prev : k ≤ target' :=
          Nat.le_of_lt_succ hk_lt_top
        have prev_defect :
            Nonempty
              (TracedFeasibleAtomProjectionDefect
                SourcePath PhaseTrace SigmaTag ProducerTrace
                Atomic SourceEvidence Residual Source n target') :=
          D.descend_below (Nat.lt_succ_self target')
            D.source_path_or_holonomy_witness target_defect
        exact
          ih (D.restrict (Nat.le_succ target'))
            prev_defect hk_le_prev

/-- A target-shell traced feasible defect plus bounded traced source-side
descent extracts a first-class bounded persistent traced feasible defect trace.
-/
theorem persistentTraceOfTargetDefect
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target)
    (target_defect :
      Nonempty
        (TracedFeasibleAtomProjectionDefect
          SourcePath PhaseTrace SigmaTag ProducerTrace
          Atomic SourceEvidence Residual Source n target)) :
    BoundedPersistentTracedFeasibleAtomProjectionDefectTrace
      SourcePath PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence Residual Source n target := by
  exact {
    defect_at := by
      intro k hk
      exact D.defect_at_of_target_defect target_defect hk
  }

/-- Traced source-side descent turns a target defect into a persistent trace,
and the same descent law rules that trace out. -/
theorem no_target_defect_via_extracted_persistent_trace
    (D :
      BoundedTracedSourceSideAtomProjectionDefectDescent
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) :
    ¬ Nonempty
      (TracedFeasibleAtomProjectionDefect
        SourcePath PhaseTrace SigmaTag ProducerTrace
        Atomic SourceEvidence Residual Source n target) := by
  intro target_defect
  exact
    (D.persistentTraceOfTargetDefect target_defect)
      |>.false_of_bounded_descent D

end BoundedTracedSourceSideAtomProjectionDefectDescent


end RepresentationArithmeticAtomProjectionDefect
