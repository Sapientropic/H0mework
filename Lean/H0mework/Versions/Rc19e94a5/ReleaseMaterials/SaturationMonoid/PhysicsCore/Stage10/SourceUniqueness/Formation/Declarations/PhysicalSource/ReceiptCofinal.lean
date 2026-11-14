import H0mework.Versions.Rc19e94a5.Physics.MotherProgrammesFormation.Declarations.PhysicalSource.Consumer
import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionConsumer

/-!
# Physical source fields from the original duration receipt

The original duration root is `RawGeneratedRoot.root dynamics`. Its native
receipt is the positive duration itself. The already defined physical
exposure, seed, continuation and evaluator are read from that receipt,
preserving every exposure branch before the faithful and residual faces are
installed. No desired classification or next current enters the law.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RawGeneratedRoot.CofinalAction
open CofinalFaithfulSettlementFace CofinalHistorySettlementFace

noncomputable section

def receiptAction (law : MotherPhysicalLaws.Law) :
    Law MotherDurationExposure.dynamics Carrier where
  Generator := Generator
  rootExposureAt := rootExposureAt law
  rootExposure_root := rootExposure_root law
  seedAt := fun {state} duration =>
    seedAt law (MotherDurationExposure.occurrenceOf state duration)
  continuationAt := fun {state} duration =>
    continuationAt law (MotherDurationExposure.occurrenceOf state duration)
  evaluatorAt := fun {state} duration =>
    evaluatorAt law (MotherDurationExposure.occurrenceOf state duration)

theorem receipt_occurrence_recovered {current : Current}
    (occurrence : OccurrenceAt current) :
    MotherDurationExposure.occurrenceOf current
      (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence) =
        occurrence := by
  change MotherDurationExposure.occurrenceOf current
    (MotherDurationExposure.durationOf occurrence) = occurrence
  exact MotherDurationExposure.occurrence_recovered occurrence

theorem receiptAction_raw_fields (law : MotherPhysicalLaws.Law)
    {current : Current} (occurrence : OccurrenceAt current) :
    let raw := (RawGeneratedRoot.CofinalAction.faithfulLaw
      (receiptAction law)).rawAt occurrence
    raw.history.rootExposure = rootExposureAt law occurrence ∧
    raw.history.seed = seedAt law occurrence ∧
    raw.history.continuation = continuationAt law occurrence ∧
    raw.evaluator = evaluatorAt law occurrence := by
  have recovered := MotherDurationExposure.occurrence_recovered occurrence
  have receipt_eq :
      receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence =
        MotherDurationExposure.durationOf occurrence := rfl
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change seedAt law
        (MotherDurationExposure.occurrenceOf current
          (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence)) =
        seedAt law occurrence
    rw [receipt_eq, recovered]

  · change continuationAt law
        (MotherDurationExposure.occurrenceOf current
          (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence)) =
        continuationAt law occurrence
    rw [receipt_eq, recovered]
  · change evaluatorAt law
        (MotherDurationExposure.occurrenceOf current
          (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence)) =
        evaluatorAt law occurrence
    rw [receipt_eq, recovered]

theorem receipt_material_eq_original (law : MotherPhysicalLaws.Law) :
    RawGeneratedRoot.CofinalAction.faithfulLaw (receiptAction law) =
      materialLaw law := by
  let formedSeeds : SeedFamily := fun {current} occurrence =>
    seedAt law (MotherDurationExposure.occurrenceOf current
      (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence))
  let formedContinuations : ContinuationFamily := fun {current} occurrence =>
    continuationAt law (MotherDurationExposure.occurrenceOf current
      (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence))
  let formedEvaluators : EvaluatorFamily := fun {current} occurrence =>
    evaluatorAt law (MotherDurationExposure.occurrenceOf current
      (receiptFromCompiler (D := MotherDurationExposure.dynamics) occurrence))
  have seedsEq : @formedSeeds = @seedAt law := by
    funext current occurrence
    exact congrArg (seedAt law) (receipt_occurrence_recovered occurrence)
  have continuationsEq : @formedContinuations = @continuationAt law := by
    funext current occurrence
    exact congrArg (continuationAt law) (receipt_occurrence_recovered occurrence)
  have evaluatorsEq : @formedEvaluators = @evaluatorAt law := by
    funext current occurrence
    exact congrArg (evaluatorAt law) (receipt_occurrence_recovered occurrence)
  let build (seeds : SeedFamily) (continuations : ContinuationFamily)
      (evaluators : EvaluatorFamily) :
      SourceNativeCofinalFaithfulMaterialLaw ledgerSource Carrier :=
    .create (.create Generator (rootExposureAt law)
      (rootExposure_root law) seeds continuations) evaluators
  have fromReceipt :
      RawGeneratedRoot.CofinalAction.faithfulLaw (receiptAction law) =
        build formedSeeds formedContinuations formedEvaluators := rfl
  have fromOriginal : materialLaw law =
      build (fun {current} occurrence => seedAt law occurrence)
        (fun {current} occurrence => continuationAt law occurrence)
        (fun {current} occurrence => evaluatorAt law occurrence) := rfl
  rw [fromReceipt, fromOriginal, seedsEq, continuationsEq, evaluatorsEq]
/-- The original duration receipt now supplies the physical evaluator's
linear equation, installed residual, complete old row and native next. -/
theorem physical_receipt_equation_ledger_next
    (law : MotherPhysicalLaws.Law) (current : Current)
    (generator : Generator) (coefficient : ℤ) :
    let occurrence := RawGeneratedRoot.emitted MotherDurationExposure.dynamics current
    let sourceLaw := receiptAction law
    ((RawGeneratedRoot.CofinalAction.faithfulLaw sourceLaw).faithfulAt occurrence
      ).freeEvaluation (Finsupp.single generator coefficient) =
        coefficient • (evaluatorAt law occurrence).root generator ∧
    (RawGeneratedRoot.CofinalAction.residualRoot sourceLaw).source.projectionLaw.outcomeAt
      (.component PUnit.unit)
      ((RawGeneratedRoot.CofinalAction.residualRoot sourceLaw).emitted current) =
        .inl ⟨PUnit.unit,
          ((RawGeneratedRoot.CofinalAction.faithfulLaw sourceLaw).faithfulAt
            occurrence).settleWithResidual⟩ ∧
    HEq (((RawGeneratedRoot.CofinalAction.residualRoot sourceLaw).toLedgerRoot.generatedLedgerAt
      current).entryDisposition
        (RawGeneratedRoot.entry MotherDurationExposure.dynamics current))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred
          (MotherDurationExposure.dynamics.emit current)
            rfl rfl (Nat.le_refl _) :
          LedgerEntryEvolutionAt
            (RawGeneratedRoot.network MotherDurationExposure.dynamics)
            (RawGeneratedRoot.entry MotherDurationExposure.dynamics current)
            (RawGeneratedRoot.entry MotherDurationExposure.dynamics
              (MotherDurationExposure.dynamics.update
                (MotherDurationExposure.dynamics.emit current))))) ∧
    ((RawGeneratedRoot.CofinalAction.residualRoot sourceLaw).toRoot.evolutionAt
      current).nextCurrent? =
        some (MotherDurationExposure.dynamics.update
          (MotherDurationExposure.dynamics.emit current)) := by
  have equation :=
    (RawGeneratedRoot.CofinalAction.generated_single_equation
      (receiptAction law) current generator coefficient).1
  have generated :=
    RawGeneratedRoot.CofinalAction.generated_event_ledger_next
      (receiptAction law) current
  have fields :=
    (receiptAction_raw_fields law
      (RawGeneratedRoot.emitted MotherDurationExposure.dynamics current)).2.2.2
  refine ⟨?_, generated.1, generated.2.1, generated.2.2⟩
  change (receiptAction law).evaluatorAt
      (MotherDurationExposure.dynamics.emit current) =
    evaluatorAt law
      (RawGeneratedRoot.emitted MotherDurationExposure.dynamics current)
    at fields
  rw [fields] at equation
  exact equation

#print axioms receiptAction_raw_fields
#print axioms receipt_material_eq_original
#print axioms receipt_occurrence_recovered
#print axioms physical_receipt_equation_ledger_next

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource
