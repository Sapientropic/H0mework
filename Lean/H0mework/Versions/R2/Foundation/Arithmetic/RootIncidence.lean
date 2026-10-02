import H0mework.Foundation.Arithmetic.Generation
import H0mework.Versions.R2.Foundation.Arithmetic.ProductiveContinuation
import H0mework.Versions.R2.Foundation.Authority.Representation

/-!
# Root-generated arithmetic incidence step

One installed root face generates the actual whole/part unit histories at an
exact occurrence.  The kernel normalizes both parallel and joint incidence;
failure is a typed mismatch residual, not `False`.  The same step exposes the
root compiler's whole-ledger write-back and generated next current.

No public producer accepts a numeral result, cardinality equality, `Equiv`,
residual value, branch selector, or completed future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootArithmeticIncidence

open ArithmeticGeneration
open RootArithmeticTerminalAuthority

universe u v

/-- Actual arithmetic material carried by one root occurrence. -/
structure RootArithmeticMaterialAt : Type where
  whole : UnitHistory
  left : UnitHistory
  right : UnitHistory

/-- Exact parallel mismatch.  Actual and expected histories remain in the
material index; no caller supplies a residual number. -/
structure IncidenceProvenanceAt
    {Provenance : Sort v} (provenance : Provenance) : Prop where
  private mk ::
  rooted : provenance = provenance

structure GeneratedParallelResidualAt
    {Provenance : Sort v} (provenance : Provenance)
    (material : RootArithmeticMaterialAt) : Type where
  private mk ::
  rooted : IncidenceProvenanceAt provenance
  mismatch : material.whole ≠ material.left.parallel material.right

/-- Exact joint mismatch. -/
structure GeneratedJointResidualAt
    {Provenance : Sort v} (provenance : Provenance)
    (material : RootArithmeticMaterialAt) : Type where
  private mk ::
  rooted : IncidenceProvenanceAt provenance
  mismatch : material.whole ≠ material.left.joint material.right

inductive ParallelIncidenceNormalFormAt
    {Provenance : Sort v} (provenance : Provenance)
    (material : RootArithmeticMaterialAt) : Type
  | exact
      (rooted : IncidenceProvenanceAt provenance)
      (commutes : material.whole = material.left.parallel material.right)
  | generatedResidual
      (residual : GeneratedParallelResidualAt provenance material)

inductive JointIncidenceNormalFormAt
    {Provenance : Sort v} (provenance : Provenance)
    (material : RootArithmeticMaterialAt) : Type
  | exact
      (rooted : IncidenceProvenanceAt provenance)
      (commutes : material.whole = material.left.joint material.right)
  | generatedResidual
      (residual : GeneratedJointResidualAt provenance material)

/-- Deterministic parallel normalization. -/
def normalizeParallel
    {Provenance : Sort v} (provenance : Provenance)
    (material : RootArithmeticMaterialAt) :
    ParallelIncidenceNormalFormAt provenance material :=
  if commutes : material.whole = material.left.parallel material.right then
    .exact ⟨rfl⟩ commutes
  else
    .generatedResidual ⟨⟨rfl⟩, commutes⟩

/-- Deterministic joint normalization. -/
def normalizeJoint
    {Provenance : Sort v} (provenance : Provenance)
    (material : RootArithmeticMaterialAt) :
    JointIncidenceNormalFormAt provenance material :=
  if commutes : material.whole = material.left.joint material.right then
    .exact ⟨rfl⟩ commutes
  else
    .generatedResidual ⟨⟨rfl⟩, commutes⟩

/-- Source law generating arithmetic material from the exact lower-root
occurrence.  It is installed before the living emitter through
`toProjectionLaw`; a theorem caller never supplies its output. -/
structure SourceNativeRootArithmeticMaterialLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V) : Type (u + 1) where
  private mk ::
  materialAt : {current : V.Current} →
    source.source.toRootSource.actual.OccurrenceAt current →
      RootArithmeticMaterialAt

def SourceNativeRootArithmeticMaterialLaw.create
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (materialAt : {current : V.Current} →
      source.source.toRootSource.actual.OccurrenceAt current →
        RootArithmeticMaterialAt) :
    SourceNativeRootArithmeticMaterialLaw source :=
  ⟨materialAt⟩

def SourceNativeRootArithmeticMaterialLaw.toProjectionLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    (law : SourceNativeRootArithmeticMaterialLaw source) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} _occurrence _active =>
    ULift.{u, 0} RootArithmeticMaterialAt
  project := fun _projection {_current} occurrence _active =>
    ULift.up (law.materialAt occurrence)

/-- Recognition that the material generator is already an installed face of
the same living root source. -/
structure SourceNativeRootArithmeticIncidenceRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V) : Type (u + 2) where
  materialLaw : SourceNativeRootArithmeticMaterialLaw
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

/-- Zero-field authority token for one exact root arithmetic step. -/
structure RootArithmeticIncidenceStepAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type where
  private mk ::

def SourceNativeRootArithmeticIncidenceRecognitionAt.generateStepAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootArithmeticIncidenceStepAt recognition visit :=
  ⟨⟩

namespace RootArithmeticIncidenceStepAt

def generated
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (_step : RootArithmeticIncidenceStepAt recognition visit) :
    SourceNativeTemporalVisitGeneratedEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot visit :=
  root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit

def material
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :
    RootArithmeticMaterialAt :=
  recognition.materialLaw.materialAt step.generated.occurrence

def parallelNormalForm
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :
    ParallelIncidenceNormalFormAt step step.material :=
  normalizeParallel step step.material

def jointNormalForm
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :
    JointIncidenceNormalFormAt step step.material :=
  normalizeJoint step step.material

/-- The exact occurrence's complete ledger write-back. -/
def wholeLedgerWriteBack
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :=
  step.generated.wholeLedgerWriteBack

/-- The next authoritative current generated by the same living root
compiler.  Incidence success or residual cannot select it. -/
def nextCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (_step : RootArithmeticIncidenceStepAt recognition visit) :
    SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

@[simp] theorem nextCurrent_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  rfl

/-- The arithmetic material is the installed projection outcome at the same
exact root occurrence. -/
theorem installedMaterial_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit)
        step.generated.occurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.generated.occurrence) :=
  recognition.installation.outcome_heq step.generated.occurrence PUnit.unit

@[simp] theorem componentOutcome_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootArithmeticIncidenceStepAt recognition visit) :
    recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.generated.occurrence =
      .inl ⟨PUnit.unit, ULift.up step.material⟩ :=
  rfl

theorem unique
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (left right : RootArithmeticIncidenceStepAt recognition visit) :
    left = right := by
  cases left
  cases right
  rfl

/-- Finite temporal rows expose their exact reachability material before its
numeric shadow is read. -/
def finiteArithmeticHistory
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root}
    {visit : RootVisit root.toAuthoritativeRoot.toRoot}
    (_step : RootArithmeticIncidenceStepAt recognition (.finite visit)) :
    UnitHistory :=
  rootVisitArithmeticHistory visit

end RootArithmeticIncidenceStepAt

/-- A bounded arithmetic runtime prefix is only the dependent family of
canonical incidence steps at the fixed root's generated finite visits.  It
adds no row wrapper, scheduler, registry, or arithmetic index field. -/
abbrev RootGeneratedArithmeticPrefixAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root)
    (history : ProductiveFiniteRootHistoryAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (fuel : Nat) :=
  (index : Fin fuel) →
    RootArithmeticIncidenceStepAt recognition
      (.finite (history.visitAt index.val))

/-- Generate every bounded row from the fixed productive root history. -/
def generateRootArithmeticPrefixAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root)
    (history : ProductiveFiniteRootHistoryAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (fuel : Nat) :
    RootGeneratedArithmeticPrefixAt recognition history fuel :=
  fun index => recognition.generateStepAt (.finite (history.visitAt index.val))

@[simp] theorem generatedRootArithmeticPrefixAt_step
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root)
    (history : ProductiveFiniteRootHistoryAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (fuel : Nat) (index : Fin fuel) :
    generateRootArithmeticPrefixAt recognition history fuel index =
      recognition.generateStepAt (.finite (history.visitAt index.val)) :=
  rfl

/-- The numeric row position is only the shadow of the exact visit's unit
history; it is not stored in the arithmetic source material or step. -/
theorem generatedRootArithmeticPrefixAt_shadow_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeRootArithmeticIncidenceRecognitionAt root)
    (history : ProductiveFiniteRootHistoryAt
      root.toAuthoritativeRoot.toLedgerRoot)
    (fuel : Nat) (index : Fin fuel) :
    UnitHistory.cardinalShadow
        (RootArithmeticIncidenceStepAt.finiteArithmeticHistory
          (generateRootArithmeticPrefixAt recognition history fuel index)) =
      index.val :=
  history.visitAt_arithmeticIndex index.val

end RootArithmeticIncidence
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
