import H0mework.Versions.R2.Physics.MotherSource.GroundedRealization

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.NativeFamily

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open StageNineEnrichedProofFreeSource Stage9C.Revision

noncomputable section

variable (prepared : MaterialState)

/-- A prepared local initial current under the original mother's literal law.
This does not change the initial current of `SpinPair.source`. -/
def source : SourceNativeSource MaterialN SpinPair.V where
  initial := .running (prepared)
  law := SpinPair.source.law

/-- The original event emitter, with a generated local chronological origin.
No authoritative root or runtime is installed by this structural closure. -/
def closure : SourceNativeRootClosure MaterialN SpinPair.V where
  source := source prepared
  emitted := SpinPair.emitted

theorem mother_law_inherited :
    (source prepared).law = SpinPair.source.law ∧
    (source prepared).toRootSource.actual =
      SpinPair.source.toRootSource.actual ∧
    HEq (source prepared).toRootSource.account
      SpinPair.source.toRootSource.account := ⟨rfl, rfl, HEq.rfl⟩

/-- The index counts local source writes; the field's spacetime argument and
the installed root's macro visits retain their original types. -/
def stateAt : Nat → MaterialState
  | 0 => prepared
  | step + 1 => materialStateNext (stateAt step)

theorem state_zero : stateAt prepared 0 = prepared := rfl

def historyAt : (step : Nat) → (closure prepared).toRoot.ReachableAt
    (.running (stateAt prepared step))
  | 0 => .initial
  | step + 1 => .step (historyAt step) rfl

def visitAt (step : Nat) : RootVisit (closure prepared).toRoot :=
  ⟨.running (stateAt prepared step),
    historyAt prepared step⟩

theorem visit_zero : visitAt prepared 0 =
    (closure prepared).toRoot.initialVisit := rfl

theorem visit_next (step : Nat) : visitAt prepared (step + 1) =
    (visitAt prepared step).next
      (next := SpinPair.next (visitAt prepared step).current) rfl := rfl

/-- The locally generated visit emits an occurrence accepted directly by the
original mother source, including its complete affected inventory. -/
def occurrenceAt (step : Nat) : SpinPair.source.toRootSource.actual.OccurrenceAt
    (visitAt prepared step).current :=
  (closure prepared).emitted
    (visitAt prepared step).current

def evolutionAt (step : Nat) : SourceNativeLedgerEvolutionAt SpinPair.source
    (occurrenceAt prepared step) :=
  SpinPair.ledgerCompiler.compile (occurrenceAt prepared step)

def successorAt (step : Nat) : SourceNativeLedgerGeneratedSuccessorAt
    (occurrenceAt prepared step)
    (evolutionAt prepared step) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (evolutionAt prepared step)).get (by rfl)

set_option maxHeartbeats 2000000 in
/-- Every finite local step is consumed by the original complete ledger
compiler and its full current-epoch field writer. -/
theorem next_consumed (step : Nat) :
    let current := stateAt prepared step
    let successor := successorAt prepared step
    SpinPair.source.toRootSource.actual.compile
        (occurrenceAt prepared step) =
      .nativeWrite (materialActionAt (SpinPair.underlying (.running current))) ∧
    successor.targetCurrent = (visitAt prepared (step + 1)).current ∧
    Recognition.wholeField successor.targetCurrent =
      Stage9C.Reduction.p286CartanNext positiveSmoothUnifiedSource current.current
        current.smooth current.nondegenerate 0 ∧
    successor.ledgerEvolution.destination (materialEntry (SpinPair.support (.running current))) =
      ⟨materialEntry (SpinPair.support (visitAt prepared (step + 1)).current),
        .transferred (.transfer (materialActionAt (SpinPair.underlying (.running current))))
          rfl rfl (Nat.le_refl _)⟩ := by
  exact ⟨rfl, rfl, Recognition.native_running_fold _, rfl⟩

theorem complete_patch_consumed (step : Nat) :
    (successorAt prepared step).ledgerEvolution =
      (SpinPair.generatedPatch (occurrenceAt prepared step)).toLedgerWriteEvolution :=
  rfl

/-- All existing mother projection fibres are read at this exact emitted
event. Their original payload meanings, including fixed weak witnesses, remain intact. -/
def readoutAt (step : Nat) (projection : SpinPair.Projection) :=
  SpinPair.authoritativeRoot.source.projectionLaw.outcomeAt projection
    (occurrenceAt prepared step)

theorem all_readouts_inherited (step : Nat) (projection : SpinPair.Projection) :
    readoutAt prepared step projection =
      SpinPair.authoritativeRoot.projectionOutcomeAt projection
        (visitAt prepared step).current := rfl

theorem physical_readouts (step : Nat) :
    SpinPair.authoritativeRoot.source.projectionLaw.project (.inherited .source)
        (occurrenceAt prepared step) PUnit.unit =
      positiveSmoothUnifiedSource ∧
    SpinPair.authoritativeRoot.source.projectionLaw.project (.inherited .configuration)
        (occurrenceAt prepared step) PUnit.unit =
      (stateAt prepared step).current ∧
    SpinPair.authoritativeRoot.source.projectionLaw.project .quantumField
        (occurrenceAt prepared step) PUnit.unit =
      Stage9DEF.Source.restrict (stateAt prepared step).current :=
  ⟨rfl, rfl, rfl⟩

theorem original_ingress_preserved :
    (source prepared).initial ≠ SpinPair.source.initial := by
  intro equal
  cases equal

theorem source_injective : Function.Injective source := by
  intro first second equal
  have initialEqual := congrArg SourceNativeSource.initial equal
  exact SpinPair.Current.running.inj initialEqual

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.NativeFamily
