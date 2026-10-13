import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction

/-! The original event, installed residual, old row and next meet at one consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

universe u
variable {D : Dynamics.{u}} {Carrier : Type u} [AddCommGroup Carrier]

/-- A direct consumer of the generated residual: faithful recovery succeeds;
each other branch retains an effective nonzero obstruction. The same event
remains in the complete old ledger and generates the original next current. -/
theorem generated_recovery_or_residual (law : Law D Carrier)
    (state : D.State) :
    let face := (faithfulLaw law).faithfulAt (emitted D state)
    (match face.settleWithResidual with
      | .faithful soundness _coverage realization =>
          ∀ actual : Carrier,
            face.completionEvaluation soundness
              (realization.canonicalQuotientEquiv.symm actual) = actual
      | .unsound _obstruction coordinate =>
          coordinate.coordinate ≠ 0
      | .kernelResidual soundness _obstruction coordinate =>
          coordinate.coordinate ≠ 0 ∧
          face.completionEvaluation soundness coordinate.coordinate = 0
      | .coverageResidual soundness _obstruction coordinate =>
          ∀ recover : Carrier →
              ((faithfulLaw law).historyAt (emitted D state)).CompletionCarrier,
            face.completionEvaluation soundness
              (recover coordinate.representative) ≠ coordinate.representative) ∧
    HEq (((residualRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((residualRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  refine ⟨?_, (generated_event_ledger_next law state).2.1,
    (generated_event_ledger_next law state).2.2⟩
  generalize outcome_eq :
      ((faithfulLaw law).faithfulAt (emitted D state)).settleWithResidual = outcome
  cases outcome with
  | faithful soundness coverage realization =>
      intro actual
      exact realization.canonicalQuotientEquiv.apply_symm_apply actual
  | unsound obstruction coordinate =>
      exact coordinate.coordinate_ne_zero
  | kernelResidual soundness obstruction coordinate =>
      refine ⟨?_, coordinate.maps_to_zero⟩
      intro vanished
      exact coordinate.coordinate_ne_zero (congrArg Subtype.val vanished)
  | coverageResidual soundness obstruction coordinate =>
      intro recover recovered
      apply coordinate.representative_not_mem_range
      exact ⟨recover coordinate.representative, recovered⟩

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
