import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.Action.Source

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery.ActionFeed

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SourceGeneratedActionObservationHistory RawGeneratedRoot.CofinalAction

noncomputable section

theorem value_action_pow_include (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (stage : Nat) (word : G →₀ B) :
    ((valueAction law) ^ stage) (valueInclude law runtime word) =
      valueInclude law (runtime.advance stage) word := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [pow_succ']
      change valueAction law (((valueAction law) ^ stage) (valueInclude law runtime word)) =
        valueInclude law (runtime.advance stage).tick.next word
      rw [inductionHypothesis]
      exact LinearMap.congr_fun (whole_action_slice law (runtime.advance stage)) word

def modelWord (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (word : G →₀ B) :
    Model (valueAction law) (valueObserve law) :=
  projection (valueAction law) (valueObserve law) (valueInclude law runtime word)

theorem model_word_action (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (word : G →₀ B) :
    modelAction (valueAction law) (valueObserve law) (modelWord law runtime word) =
      modelWord law runtime.tick.next word := by
  rw [modelWord, modelAction_source]
  exact congrArg (projection (valueAction law) (valueObserve law))
    (LinearMap.congr_fun (whole_action_slice law runtime) word)

theorem model_word_fibre (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (left right : G →₀ B) :
    modelWord law runtime left = modelWord law runtime right ↔
      ∀ stage : Nat,
        valueWordEvaluation (MotherPhysicalSource.receiptAction law)
            (anchorAt law (runtime.advance stage).state).2 left =
          valueWordEvaluation (MotherPhysicalSource.receiptAction law)
            (anchorAt law (runtime.advance stage).state).2 right := by
  rw [modelWord, modelWord, model_fibre_iff]
  simp only [value_action_pow_include]
  constructor <;> intro same stage
  · exact (LinearMap.congr_fun (whole_value_slice law (runtime.advance stage)) left).symm.trans
      ((same stage).trans (LinearMap.congr_fun
        (whole_value_slice law (runtime.advance stage)) right))
  · exact (LinearMap.congr_fun (whole_value_slice law (runtime.advance stage)) left).trans
      ((same stage).trans (LinearMap.congr_fun
        (whole_value_slice law (runtime.advance stage)) right).symm)

theorem runtime_action_original_consumer (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (query : QueryAt law runtime.state)
    (left right : G) (leftCoefficient rightCoefficient : ℤ) :
    let anchor := anchorAt law runtime.state
    let key : Key law := ⟨anchor, query⟩
    let sourceLaw := MotherPhysicalSource.receiptAction law
    let occurrence := RawGeneratedRoot.emitted dynamics anchor.1
    anchor.2 = occurrence ∧
    (valueAction law).comp (valueInclude law runtime) = valueInclude law runtime.tick.next ∧
    (∀ word : G →₀ B,
      modelAction (valueAction law) (valueObserve law) (modelWord law runtime word) =
        modelWord law runtime.tick.next word) ∧
    (∀ first last : G →₀ B,
      modelWord law runtime first = modelWord law runtime last ↔
        ∀ stage : Nat,
          valueWordEvaluation sourceLaw (anchorAt law (runtime.advance stage).state).2 first =
            valueWordEvaluation sourceLaw (anchorAt law (runtime.advance stage).state).2 last) ∧
    (∀ word : G →₀ B,
      (operationExpression law).eval (operationEnvironment law runtime word) =
        valueObserve law (valueInclude law runtime.tick.next word)) ∧
    (∀ word : G →₀ B,
      valueWordCoimageRecovery sourceLaw occurrence
          (SourceGeneratedScalarPerfectification.canonicalMap
            (valueWordPairing sourceLaw occurrence) word) =
        valueObserve law (valueInclude law runtime word)) ∧
    (answer law key).2.1 =
      ((faithfulLaw sourceLaw).faithfulAt anchor.2).settleWithResidual ∧
    HEq ((inquiryAt law runtime.state).compileInquiry query).answerReadout (answer law key) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      ((livingRoot law).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (process law).stateAt ((process law).successor runtime.state) := by
  dsimp only
  obtain ⟨anchorEq, recover, _integerSquare, _oldRecovery, residual, compiled, ledger, next⟩ :=
    runtime_value_scalar_coimage_original_consumer law runtime query left right
      leftCoefficient rightCoefficient
  refine ⟨anchorEq, whole_action_slice law runtime, model_word_action law runtime,
    model_word_fibre law runtime, operation_proof_reads_next law runtime,
    ?_, residual, compiled, ledger, next⟩
  intro word
  exact (recover word).trans (LinearMap.congr_fun (whole_value_slice law runtime) word).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery.ActionFeed
