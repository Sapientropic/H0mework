import H0mework.Arithmetic.ProjectionDefect.NativeTraceDefectIntrinsicForcing

/-!
# Generated observed defect closed domain

Gate classification:

* This file proves the closed-domain elimination half:
  `ClosedGeneratedObservedDefect -> False`.
* It does **not** grant a bare arithmetic missing shell admission to this
  domain.
* It does **not** prove a selected-family coherence gate.

The point is to freeze the honest codomain for the pointwise admission theorem. A
closed generated observed defect is not an arbitrary defect later enriched by
an adapter: its trace source-path type is fixed by the native hard-door
geometry at construction time, so the return obstruction is read from the
observed trace itself.  Downstream,
`ReturnCarryingGeneratedObservedMissingShell` names the admitted object that packages this
closed source/trace jurisdiction together with its bare arithmetic shadow.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace NativeTraceHardDoor

universe u

/-- Closed observed defect domain for the generated native trace hard door.

This is a source of defects, not a post-hoc enrichment of bare missing shells.
The `defect` field lives in `geometry.SourcePath`, so native return geometry is
part of the observed trace domain at construction time. -/
structure ClosedGeneratedObservedDefect
    (PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (n k : Nat) where
  geometry :
    NativeTraceReturnHardDoorGeometry
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n
  defect :
    TracedFeasibleAtomProjectionDefect
      geometry.SourcePath
      PhaseTrace SigmaTag ProducerTrace
      Atomic SourceEvidence geometry.residual_transport
      geometry.lowering_dynamics.sourceCategory n k

namespace ClosedGeneratedObservedDefect

variable {PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n k : Nat}

/-- Closed-domain elimination gate.

This is the already-available RAAPD hard door repackaged around the closed
observed domain.  It does not say that every bare arithmetic missing shell must
enter this domain. -/
theorem impossible
    (closed :
      ClosedGeneratedObservedDefect
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    False :=
  (closed.geometry.no_stable_traced_feasible_defect_via_defect_intrinsic_forcing
    k) ⟨closed.defect⟩

/-- Nonempty form of the closed-domain elimination gate. -/
theorem no_nonempty :
    ¬ Nonempty
      (ClosedGeneratedObservedDefect
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) := by
  intro h
  rcases h with ⟨closed⟩
  exact closed.impossible

end ClosedGeneratedObservedDefect

/-- Named theorem matching the closed-domain judgment split:
`ClosedGeneratedObservedDefect -> False`.

Gate classification: closed-domain elimination.  Source/trace admissibility
must already be present; bare arithmetic shadows are outside this judgment. -/
theorem closedGeneratedObservedDefect_impossible
    {PhaseTrace SigmaTag ProducerTrace : Type u}
    {Atomic : Nat -> Prop}
    {SourceEvidence : Type u}
    {n k : Nat}
    (closed :
      ClosedGeneratedObservedDefect
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    False :=
  closed.impossible


end NativeTraceHardDoor

end RepresentationArithmeticAtomProjectionDefect
