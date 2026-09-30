import H0mework.Foundation.Runtime.EffectDynamics
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaRootEffect
import H0mework.Versions.Y.Arithmetic.RiemannRuntime.ClozelOriginalKSourceFace

/-!
# Source material for the A1c paired-Omega effect row

One exact unit-root occurrence generates the complete paired effect at its
own root-derived stage: retained incidence, phase residual, centered trace
and logarithmic q-rich readout.  The canonical native write updates this
effect at the compiler target and transports the unique root row through the
existing whole ledger.  Progress is the actual `UnitHistory.next` change.

No zero, fixedness, separator, endpoint branch, caller successor or new U7
obstruction enters the law.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open ArithmeticGeneration
open CanonicalUnitArithmeticRoot
open Character.GlobalCoPoissonCurrent

noncomputable section

structure RuntimeEffect where
  retained : QRich.ClozelJPair
  phase : QRich.ClozelJPair
  centeredTrace : QRich.ClozelJPair
  logNorm : ℝ
  originalK : OriginalKSourceFace

def currentEffectStage (current : Current) : Nat :=
  current.cardinalShadow - 1

def generateRuntimeEffect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (current : Current) : RuntimeEffect :=
  let stage := currentEffectStage current
  let scale := stageSqrtScaleUnit stage
  { retained := pairedOmegaMeasurementResidual observation nontrivial scale
    phase := pairedRootPhaseResidual observation nontrivial scale
    centeredTrace := pairedRootCenteredTrace observation nontrivial scale
    logNorm := omegaLogNormEffect observation nontrivial stage
    originalK := OriginalKSourceFace.generate observation nontrivial }

theorem generateRuntimeEffect_conservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (current : Current) :
    (generateRuntimeEffect observation nontrivial current).phase =
      (generateRuntimeEffect observation nontrivial current).retained +
        (generateRuntimeEffect observation nontrivial current).centeredTrace := by
  exact pairedRootPhaseResidual_eq_incidence_add_centeredTrace
    observation nontrivial _

def runtimeEffectAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (_occurrence : ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    RuntimeEffect :=
  generateRuntimeEffect observation nontrivial current

def runtimeOperationalAt {current : Current}
    (_occurrence : ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    Current := current

def runtimeEffectEventVocabulary
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeEffectEventVocabulary ledgerSource where
  Effect := RuntimeEffect
  Operational := Current
  effectAt := runtimeEffectAt observation nontrivial
  operationalAt := runtimeOperationalAt

def runtimeUpdateEffectAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (_occurrence : SourceNativeEffectOccurrenceAt
      (runtimeEffectEventVocabulary observation nontrivial) current)
    (_active : Unit) (_effect : RuntimeEffect) : RuntimeEffect :=
  generateRuntimeEffect observation nontrivial (next current)

theorem generateRuntimeEffect_originalK_preserved
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (current : Current) :
    (generateRuntimeEffect observation nontrivial (next current)).originalK =
      (generateRuntimeEffect observation nontrivial current).originalK := by
  rfl

theorem runtimeUpdateEffectAt_originalK_eq
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : SourceNativeEffectOccurrenceAt
      (runtimeEffectEventVocabulary observation nontrivial) current)
    (effect : RuntimeEffect) :
    (runtimeUpdateEffectAt observation nontrivial occurrence () effect).originalK =
      (generateRuntimeEffect observation nontrivial current).originalK :=
  generateRuntimeEffect_originalK_preserved observation nontrivial current

def runtimeUpdateOperationalAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (_occurrence : SourceNativeEffectOccurrenceAt
      (runtimeEffectEventVocabulary observation nontrivial) current)
    (_active : Unit) (_effect : RuntimeEffect) (_operational : Current) :
    Current :=
  next current

def runtimeEffectDynamicalVocabulary
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeEffectDynamicalVocabulary
      (runtimeEffectEventVocabulary observation nontrivial) where
  ActiveAt := fun _ => Unit
  InactiveAt := fun _ => PEmpty
  classify := fun _ => .inl ()
  effectEntryAt := fun occurrence _ => occurrenceLedgerEntry occurrence.lower
  updateEffectAt := runtimeUpdateEffectAt observation nontrivial
  updateOperationalAt := runtimeUpdateOperationalAt observation nontrivial

def emptyEffectU7 : U7ProducerCalculus N where
  DemandAt := fun obstruction => nomatch obstruction
  generateDemand := fun obstruction => nomatch obstruction

def emptyEffectU7Source : U7ActualSuccessorSource N emptyEffectU7 where
  EventAt := fun obstruction => nomatch obstruction
  emit := fun obstruction => nomatch obstruction
  demandGeneratedAt := fun event => nomatch event
  demandEntryAt := fun event => nomatch event

def emptyEffectU7Calculus :
    U7ObstructionEvolutionCalculus N emptyEffectU7 where
  source := emptyEffectU7Source
  compile := fun event => nomatch event

def runtimeEffectGeneratedEntryAt
    {current : Current}
    (occurrence : ledgerSource.source.toRootSource.actual.OccurrenceAt current) :
    SourceNativeEffectGeneratedEntryAt (source := ledgerSource)
      (occurrence := occurrence) (occurrenceLedgerEntry occurrence) := by
  rcases occurrence with ⟨support, ⟨support_eq, trace, trace_eq⟩⟩
  cases support_eq
  cases trace_eq
  let event : RootNativeEventAt current current :=
    ⟨rfl, nativeActionTrace current, rfl⟩
  exact ⟨(sourceNativeFiniteLedgerPatchGeneratedEntry?
    source ledgerCompiler.ExactTransitionAt ledgerWriteRowSource
      ledgerTerminalRowSource (ledgerCompiler.compile ⟨current, event⟩)
      (ledgerCompiler.compilePatch ⟨current, event⟩)
      (occurrenceLedgerEntry ⟨current, event⟩)).get (by rfl)⟩

/-- Canonical effect-row law indexed by the existing unit-root ledger
compiler image. -/
def runtimeEffectLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeEffectDynamicalClosureLaw ledgerSource :=
  .create emptyEffectU7 emptyEffectU7Calculus
    (runtimeEffectEventVocabulary observation nontrivial)
    (runtimeEffectDynamicalVocabulary observation nontrivial) <| by
      intro current occurrence active
      rcases occurrence with ⟨lower⟩
      rcases lower with ⟨support, ⟨support_eq, trace, trace_eq⟩⟩
      cases support_eq
      cases trace_eq
      let event : RootNativeEventAt current current :=
        ⟨rfl, nativeActionTrace current, rfl⟩
      let lower : ledgerSource.source.toRootSource.actual.OccurrenceAt current :=
        ⟨current, event⟩
      let generated := ledgerCompiler.compile lower
      let successor :=
        (@SourceNativeEffectGeneratedSuccessorAt.ofGenerated?
          N V ledgerSource current lower generated).get (by rfl)
      refine .next (runtimeEffectGeneratedEntryAt lower) successor () rfl
        ?_ ?_ ?_ ?_
      · exact ⟨rfl⟩
      · rfl
      · rfl
      · apply SourceNativeRecursiveEffectProgressAt.operationalChanged
        intro equality
        have cardinalEquality := congrArg UnitHistory.cardinalShadow equality
        change current.cardinalShadow = Nat.succ current.cardinalShadow at cardinalEquality
        omega

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
