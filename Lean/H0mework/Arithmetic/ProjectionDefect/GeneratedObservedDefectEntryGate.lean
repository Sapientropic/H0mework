import H0mework.Arithmetic.ProjectionDefect.GeneratedObservedDefectClosedDomain

/-!
# Generated observed missing-shell admission gate

Gate classification:

* `MissingGeneratedShell` is only the arithmetic shadow of a missing shell.
* `GeneratedObservedMissingShell` is the honest physical-source admission
  candidate: generated sector, physical credential, traced demand, and
  arithmetic shadow are tied to the same source evidence.
* `GeneratedObservedMissingShellTruthFormula` is the external hard-door
  judgment; the candidate does not contain its own contradiction.
* `ReturnCarryingGeneratedObservedMissingShell` is the former closed record.
  It is retained for compatibility, but its native return path makes every
  positive instance contradictory before the missing field is inspected.
* `GeneratedObservedMissingShellEntryLaw` is retained as a stronger, universal
  legacy mouth into that return-carrying closed record.

The jurisdiction boundary is pointwise.  A Truth Formula judges only a
`GeneratedObservedMissingShell` already carrying an independent physical
admission credential.  It does not eliminate arbitrary inhabitants of the
bare arithmetic projection type.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace NativeTraceHardDoor

universe u

/-- Bare arithmetic missing-shell shadow.

Despite the historical name, this type says only that the even fiber `2 * n`
has no `Atomic` pair of energy `k`.  It carries no source path, sigma tag,
producer trace, source evidence, generated-sector witness, physical
admissibility, or residual-transport responsibility.  It is therefore a
projection boundary, not by itself a physical obstruction. -/
structure MissingGeneratedShell
    (Atomic : Nat -> Prop)
    (n k : Nat) where
  noAtomRealization :
    ¬ ∃ p : ArithmeticAtomPair Atomic n,
      ArithmeticAtomPair.energy p = k

/-- Semantically precise compatibility name for `MissingGeneratedShell`.

New theorem statements may use this alias when the arithmetic-shadow role
needs to be explicit; the historical structure name remains available. -/
abbrev ArithmeticMissingShellShadow
    (Atomic : Nat -> Prop)
    (n k : Nat) :=
  MissingGeneratedShell Atomic n k

/-! ## Honest physical-source admission candidate -/

/-- Owner of the generated-sector and physical-admission evidence spaces.

Both witness types have a readout into `SourceEvidence`.  A candidate below
must prove that both readouts are the exact evidence carried by its observed
demand.  This prevents a physical credential for one source object from being
attached to an unrelated arithmetic shell demand.

The structure does not assert that either witness type is inhabited.  Their
real producer remains the responsibility of the concrete SU7/sigma/source
geometry. -/
structure GeneratedSourceAdmissionJurisdiction
    (SourcePath SourceEvidence : Type u) where
  GeneratedSector : Type u
  PhysicalAdmission : Type u
  pathEvidence : SourcePath -> SourceEvidence
  generatedEvidence : GeneratedSector -> SourceEvidence
  admittedEvidence : PhysicalAdmission -> SourceEvidence

/-- Source-generated and physically admitted observation before any arithmetic
missing shadow is attached.

This is the positive producer output.  Jurisdiction is carried by:

* a traced feasible demand, retaining source path, phase, sigma, producer
  trace, feasibility, and residual responsibility;
* a generated-sector witness;
* a physical-admission credential;
* equality of every witness readout with that exact demand evidence.

Because this type has no `Atomic` parameter and no negative realization field,
a downstream materializer consuming it cannot inspect or exploit
`MissingGeneratedShell.noAtomRealization`. -/
structure GeneratedObservedSourceAdmission
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (jurisdiction :
      GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence)
    (n k : Nat) where
  observedDemand :
    TracedFeasibleRepRepairDemand
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source n k
  generatedSector : jurisdiction.GeneratedSector
  physicalAdmission : jurisdiction.PhysicalAdmission
  sourcePathEvidence_eq :
    jurisdiction.pathEvidence observedDemand.trace.sourcePath =
      observedDemand.demand.demand.evidence
  generatedEvidence_eq :
    jurisdiction.generatedEvidence generatedSector =
      observedDemand.demand.demand.evidence
  admittedEvidence_eq :
    jurisdiction.admittedEvidence physicalAdmission =
      observedDemand.demand.demand.evidence

namespace GeneratedObservedSourceAdmission

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {jurisdiction :
  GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence}
variable {n k : Nat}

/-- Exact evidence jointly named by the source path, generated sector,
physical credential, feasibility proof, and residual responsibility. -/
def sourceEvidence
    (admission :
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k) :
    SourceEvidence :=
  admission.observedDemand.demand.demand.evidence

theorem sourcePathEvidence_eq_sourceEvidence
    (admission :
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k) :
    jurisdiction.pathEvidence admission.observedDemand.trace.sourcePath =
      admission.sourceEvidence :=
  admission.sourcePathEvidence_eq

theorem generatedEvidence_eq_sourceEvidence
    (admission :
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k) :
    jurisdiction.generatedEvidence admission.generatedSector =
      admission.sourceEvidence :=
  admission.generatedEvidence_eq

theorem admittedEvidence_eq_sourceEvidence
    (admission :
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k) :
    jurisdiction.admittedEvidence admission.physicalAdmission =
      admission.sourceEvidence :=
  admission.admittedEvidence_eq

/-- The positive admission already owns the exact arithmetic-shell residual;
no missing-shadow proof is needed to read it. -/
theorem sourceEvidence_residual_eq
    (admission :
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k) :
    Residual.residualEnergy admission.sourceEvidence = k :=
  admission.observedDemand.demand.demand.residual_eq

/-- Feasibility likewise belongs to the positive admission. -/
theorem sourceEvidence_feasible
    (admission :
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k) :
    Source.feasible admission.sourceEvidence :=
  admission.observedDemand.demand.feasible

end GeneratedObservedSourceAdmission

/-- A source-generated, observed, physically admitted missing-shell candidate.

The arithmetic absence is attached only after the independent positive
`GeneratedObservedSourceAdmission` exists.

No native return path or no-third-sink contradiction is stored in this object.
Whether such a candidate can persist is the separate Truth-Formula judgment
defined below. -/
structure GeneratedObservedMissingShell
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (jurisdiction :
      GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence)
    (n k : Nat)
    extends
      GeneratedObservedSourceAdmission
        SourcePath PhaseTrace SigmaTag ProducerTrace
        SourceEvidence Residual Source jurisdiction n k where
  missing : ArithmeticMissingShellShadow Atomic n k

namespace GeneratedObservedMissingShell

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {jurisdiction :
  GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence}
variable {n k : Nat}

/-- Exact source evidence shared by the demand, generated sector, and physical
admission credential. -/
def sourceEvidence
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    SourceEvidence :=
  candidate.toGeneratedObservedSourceAdmission.sourceEvidence

theorem sourcePathEvidence_eq_sourceEvidence
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    jurisdiction.pathEvidence candidate.observedDemand.trace.sourcePath =
      candidate.sourceEvidence :=
  candidate.toGeneratedObservedSourceAdmission.sourcePathEvidence_eq_sourceEvidence

theorem generatedEvidence_eq_sourceEvidence
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    jurisdiction.generatedEvidence candidate.generatedSector =
      candidate.sourceEvidence :=
  candidate.toGeneratedObservedSourceAdmission.generatedEvidence_eq_sourceEvidence

theorem admittedEvidence_eq_sourceEvidence
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    jurisdiction.admittedEvidence candidate.physicalAdmission =
      candidate.sourceEvidence :=
  candidate.toGeneratedObservedSourceAdmission.admittedEvidence_eq_sourceEvidence

/-- Residual responsibility is read from the same source evidence and equals
the arithmetic shadow index `k`. -/
theorem sourceEvidence_residual_eq
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    Residual.residualEnergy candidate.sourceEvidence = k :=
  candidate.toGeneratedObservedSourceAdmission.sourceEvidence_residual_eq

/-- Physical/source feasibility is retained by the same observed evidence. -/
theorem sourceEvidence_feasible
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    Source.feasible candidate.sourceEvidence :=
  candidate.toGeneratedObservedSourceAdmission.sourceEvidence_feasible

end GeneratedObservedMissingShell

/-- Independent generated-repair materialization law.

This is the honest consumer/hard-gate premise: it receives only the positive
source admission and must materialize an arithmetic atom pair at the admitted
shell.  It cannot read a missing-shadow proof because that proof is absent from
its input type. -/
structure GeneratedObservedRepairMaterializationLaw
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (jurisdiction :
      GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence)
    (n k : Nat) : Prop where
  materialize :
    GeneratedObservedSourceAdmission
      SourcePath PhaseTrace SigmaTag ProducerTrace
      SourceEvidence Residual Source jurisdiction n k ->
        ∃ pair : ArithmeticAtomPair Atomic n,
          ArithmeticAtomPair.energy pair = k

/-- External Truth-Formula jurisdiction judgment.

The hard door eliminates candidates that have already earned physical/source
admission.  Crucially, this law has no quantifier over bare
`MissingGeneratedShell` witnesses and is not a producer of admission data. -/
structure GeneratedObservedMissingShellTruthFormula
    (SourcePath PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (Residual : AdditiveResidualTransportCategory SourceEvidence)
    (Source : RepresentationFeasibleCategory SourceEvidence)
    (jurisdiction :
      GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence)
    (n k : Nat) : Prop where
  eliminate :
    GeneratedObservedMissingShell
      SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
      SourceEvidence Residual Source jurisdiction n k -> False

namespace GeneratedObservedMissingShellTruthFormula

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {jurisdiction :
  GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence}
variable {n k : Nat}

/-- The Truth Formula excludes the admitted obstruction, not its naked
arithmetic shadow. -/
theorem no_admitted_obstruction
    (truth :
      GeneratedObservedMissingShellTruthFormula
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    ¬ Nonempty
      (GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) := by
  rintro ⟨candidate⟩
  exact truth.eliminate candidate

end GeneratedObservedMissingShellTruthFormula

namespace GeneratedObservedRepairMaterializationLaw

variable {SourcePath PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {Residual : AdditiveResidualTransportCategory SourceEvidence}
variable {Source : RepresentationFeasibleCategory SourceEvidence}
variable {jurisdiction :
  GeneratedSourceAdmissionJurisdiction SourcePath SourceEvidence}
variable {n k : Nat}

/-- Independent repair materialization induces the calibrated Truth Formula.

The contradiction uses `missing.noAtomRealization` only after the atom pair has
been generated from the positive admission alone. -/
theorem toTruthFormula
    (law :
      GeneratedObservedRepairMaterializationLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    GeneratedObservedMissingShellTruthFormula
      SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
      SourceEvidence Residual Source jurisdiction n k where
  eliminate := by
    intro candidate
    exact candidate.missing.noAtomRealization
      (law.materialize candidate.toGeneratedObservedSourceAdmission)

/-- Direct theorem form of the same non-circular jurisdiction judgment. -/
theorem admittedMissing_impossible
    (law :
      GeneratedObservedRepairMaterializationLaw
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k)
    (candidate :
      GeneratedObservedMissingShell
        SourcePath PhaseTrace SigmaTag ProducerTrace Atomic
        SourceEvidence Residual Source jurisdiction n k) :
    False :=
  law.toTruthFormula.eliminate candidate

end GeneratedObservedRepairMaterializationLaw

/-! ## Legacy return-carrying closed object -/

/-- Former generated-observed record, retained for downstream compatibility.

Its trace source-path type is `NativeTraceReturnSourcePath`.  At positive
residual it already conflicts with the geometry's strict lowering law, even
without reading `missing`.  It is therefore a diagnostic closed-elimination
object, not the physical admission candidate above. -/
structure ReturnCarryingGeneratedObservedMissingShell
    (PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (n k : Nat) where
  geometry :
    NativeTraceReturnHardDoorGeometry
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n
  observedDemand :
    TracedFeasibleRepRepairDemand
      geometry.SourcePath
      PhaseTrace SigmaTag ProducerTrace
      SourceEvidence geometry.residual_transport
      geometry.lowering_dynamics.sourceCategory n k
  missing :
    ArithmeticMissingShellShadow Atomic n k

namespace ReturnCarryingGeneratedObservedMissingShell

variable {PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n k : Nat}

/-- Arithmetic projection shadow retained inside the admitted obstruction. -/
theorem arithmeticShadow
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    ArithmeticMissingShellShadow Atomic n k :=
  admitted.missing

/-- Read the native source-path witness from the admitted obstruction itself.
-/
def nativeSourcePath
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    admitted.geometry.SourcePath :=
  admitted.observedDemand.trace.sourcePath

/-- Phase trace retained by the admitted source observation. -/
def phaseTrace
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    PhaseTrace :=
  admitted.observedDemand.trace.phaseTrace

/-- Sigma tag retained by the admitted source observation. -/
def sigmaTag
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    SigmaTag :=
  admitted.observedDemand.trace.sigmaTag

/-- Producer trace retained by the admitted source observation. -/
def producerTrace
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    ProducerTrace :=
  admitted.observedDemand.trace.producerTrace

/-- Source evidence whose generated-sector payload is fixed by the concrete
`SourceEvidence` instantiation. -/
def sourceEvidence
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    SourceEvidence :=
  admitted.observedDemand.demand.demand.evidence

/-- Physical/source feasibility is retained on the same source evidence. -/
theorem sourceEvidence_feasible
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    admitted.geometry.lowering_dynamics.sourceCategory.feasible
      admitted.sourceEvidence :=
  admitted.observedDemand.demand.feasible

/-- Residual-transport responsibility is tied to the admitted arithmetic shell
`k`, rather than stored as an unrelated self-reported key. -/
theorem sourceEvidence_residual_eq
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    admitted.geometry.residual_transport.residualEnergy
      admitted.sourceEvidence = k :=
  admitted.observedDemand.demand.demand.residual_eq

/-- Package an admitted obstruction into the already-closed hard-door domain.
-/
def toClosedGeneratedObservedDefect
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    ClosedGeneratedObservedDefect
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k where
  geometry := admitted.geometry
  defect := {
    demand := admitted.observedDemand
    noAtomRealization := admitted.missing.noAtomRealization
  }

/-- Legacy closed-domain elimination.  At successor shells the stronger
`positive_impossible_without_missing_field` boundary shows that this record is
already contradictory before the arithmetic shadow is used. -/
theorem impossible
    (admitted :
      ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    False :=
  admitted.toClosedGeneratedObservedDefect.impossible

/-- There is no admitted generated-observed obstruction at a closed hard-door
shell.  This theorem deliberately says nothing about the inhabitance of bare
  `MissingGeneratedShell Atomic n k`.  It must not be confused with the honest
physical admission candidate of the same file. -/
theorem no_nonempty :
    ¬ Nonempty
      (ReturnCarryingGeneratedObservedMissingShell
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) := by
  rintro ⟨admitted⟩
  exact admitted.impossible

end ReturnCarryingGeneratedObservedMissingShell

/-- Universal admission law from every bare arithmetic missing witness at the
fixed shell into the generated-observed native trace domain.

This legacy socket is strictly stronger than a pointwise physical admission:
its `observedDemand` function gives every bare witness jurisdiction.  It is
useful as a diagnostic/global mouth, but merely inhabiting it must not be
counted as source-generation progress.  Its codomain is the legacy
return-carrying record, not `GeneratedObservedMissingShell`. -/
structure GeneratedObservedMissingShellEntryLaw
    (PhaseTrace SigmaTag ProducerTrace : Type u)
    (Atomic : Nat -> Prop)
    (SourceEvidence : Type u)
    (n k : Nat) where
  geometry :
    NativeTraceReturnHardDoorGeometry
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n
  observedDemand :
    MissingGeneratedShell Atomic n k ->
      TracedFeasibleRepRepairDemand
        geometry.SourcePath
        PhaseTrace SigmaTag ProducerTrace
        SourceEvidence geometry.residual_transport
        geometry.lowering_dynamics.sourceCategory n k

namespace GeneratedObservedMissingShellEntryLaw

variable {PhaseTrace SigmaTag ProducerTrace : Type u}
variable {Atomic : Nat -> Prop}
variable {SourceEvidence : Type u}
variable {n k : Nat}

/-- Apply the universal mouth to one bare arithmetic witness, producing the
pointwise admitted obstruction that the hard door is allowed to judge. -/
def admitArithmeticShadow
    (E :
      GeneratedObservedMissingShellEntryLaw
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k)
    (missing : MissingGeneratedShell Atomic n k) :
    ReturnCarryingGeneratedObservedMissingShell
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k where
  geometry := E.geometry
  observedDemand := E.observedDemand missing
  missing := missing

/-- The formal missing-shell entry theorem.

Gate classification: universal-admission compatibility map.  The result is
obtained by first forming the pointwise admitted obstruction; this theorem is
not evidence that every bare arithmetic shadow should be admitted. -/
def toClosedGeneratedObservedDefect
    (E :
      GeneratedObservedMissingShellEntryLaw
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k)
    (missing : MissingGeneratedShell Atomic n k) :
    ClosedGeneratedObservedDefect
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k :=
  (E.admitArithmeticShadow missing).toClosedGeneratedObservedDefect

/-- Named entry map matching the judgment split:
`missing shell -> ClosedGeneratedObservedDefect`, conditional on the legacy
universal admission law.

This is a `def`, not a `theorem`, because the codomain is a data-bearing closed
defect object rather than a proposition. -/
def missingShell_to_closedGeneratedObservedDefect
    (E :
      GeneratedObservedMissingShellEntryLaw
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k)
    (missing : MissingGeneratedShell Atomic n k) :
    ClosedGeneratedObservedDefect
      PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k :=
  E.toClosedGeneratedObservedDefect missing

/-- Propositional / theorem form of the entry map. -/
theorem missingShell_to_closedGeneratedObservedDefect_nonempty
    (E :
      GeneratedObservedMissingShellEntryLaw
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k)
    (missing : MissingGeneratedShell Atomic n k) :
    Nonempty
      (ClosedGeneratedObservedDefect
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :=
  ⟨E.missingShell_to_closedGeneratedObservedDefect missing⟩

/-- Once the universal admission law is supplied, a bare missing witness is
impossible because that law admits it to the closed-domain hard door. -/
theorem missingShell_impossible
    (E :
      GeneratedObservedMissingShellEntryLaw
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k)
    (missing : MissingGeneratedShell Atomic n k) :
    False :=
  (E.admitArithmeticShadow missing).impossible

/-- A universal admission law excludes bare arithmetic missing shells.

This conclusion is intentionally attached to the strong law: it must not be
read as saying that the hard door independently excludes all arithmetic
shadows. -/
theorem no_missing_generated_shell
    (E :
      GeneratedObservedMissingShellEntryLaw
        PhaseTrace SigmaTag ProducerTrace Atomic SourceEvidence n k) :
    ¬ Nonempty (MissingGeneratedShell Atomic n k) := by
  intro h
  rcases h with ⟨missing⟩
  exact E.missingShell_impossible missing

end GeneratedObservedMissingShellEntryLaw


end NativeTraceHardDoor

end RepresentationArithmeticAtomProjectionDefect
