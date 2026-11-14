import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionCochain

/-!
# Scalar pairing from the original receipt's descended evaluator

The relation settlement is already computed from the actual scalar evaluator.
On its sound branch, the canonical quotient evaluation generates a rank-one
bilinear pairing. On its unsound branch no quotient pairing is fabricated; the
previously installed residual remains available. The pairing option is a
dependent source face beside the raw, residual and differential coordinates.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

variable {D : Dynamics.{0}}

def rankOnePairing {H : Type} [AddCommGroup H] [Module ℤ H]
    (read : H →ₗ[ℤ] ℤ) : H →ₗ[ℤ] H →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ
    (fun left right => read left * read right)
    (by intro left₁ left₂ right; simp [map_add, add_mul])
    (by intro coefficient left right; simp; ring)
    (by intro left right₁ right₂; rw [map_add, mul_add])
    (by intro coefficient left right; simp; ring)

def scalarPairing? (law : Law D ℤ)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    Option (((historyLaw law).historyAt occurrence).CompletionCarrier →ₗ[ℤ]
      ((historyLaw law).historyAt occurrence).CompletionCarrier →ₗ[ℤ] ℤ) :=
  let face := (faithfulLaw law).faithfulAt occurrence
  match face.settleRelations with
  | .sound soundness => some (rankOnePairing (face.completionEvaluation soundness))
  | .unsound _ => none

def scalarPairingComponent (law : Law D ℤ) :
    SourceNativeProjectionLaw (restructuringSource D).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} occurrence _ =>
    Option (((historyLaw law).historyAt occurrence).CompletionCarrier →ₗ[ℤ]
      ((historyLaw law).historyAt occurrence).CompletionCarrier →ₗ[ℤ] ℤ)
  project := fun _ {_} occurrence _ => scalarPairing? law occurrence

def scalarPairingSource (law : Law D ℤ) :
    SourceNativeAuthoritySource (network D) (vocabulary D) :=
  ((cochainRoot law).source).withProjectionCoface (scalarPairingComponent law)

def scalarPairingRoot (law : Law D ℤ) :
    SourceNativeAuthoritativeRootClosure (network D) (vocabulary D) where
  source := scalarPairingSource law
  emitted := emitted D
  compiler_commutes := (cochainRoot law).compiler_commutes

def oldCochainInstallation (law : Law D ℤ) :
    SourceNativeProjectionLaw.InstallationAt
      (cochainRoot law).source.projectionLaw
      (scalarPairingRoot law).source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (cochainRoot law).source (scalarPairingComponent law)

theorem scalarPairingRoot_same_lower (law : Law D ℤ) :
    (scalarPairingRoot law).toLedgerRoot = (root D).toAuthoritativeRoot.toLedgerRoot :=
  rfl

/-- The new face retains every older coordinate, the exact transfer row and
the original source-generated next at the same emitted event. -/
theorem scalarPairing_inventory_ledger_next (law : Law D ℤ) (state : D.State) :
    (∀ old : (cochainRoot law).source.projectionLaw.Projection,
      HEq ((scalarPairingRoot law).source.projectionLaw.outcomeAt
          ((oldCochainInstallation law).embed old)
          ((scalarPairingRoot law).emitted state))
        ((cochainRoot law).source.projectionLaw.outcomeAt old
          ((cochainRoot law).emitted state))) ∧
    HEq (((scalarPairingRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((scalarPairingRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  exact ⟨fun old => (oldCochainInstallation law).outcome_heq (emitted D state) old,
    (generated_event_ledger_next law state).2.1,
    (generated_event_ledger_next law state).2.2⟩

/-- The old relation classifier itself governs the source pairing face.
Soundness generates its actual scalar pairing; unsoundness retains a
nonzero installed differential instead of a fabricated quotient pairing. -/
theorem scalarPairing_source_branch (law : Law D ℤ) (state : D.State) :
    let occurrence := emitted D state
    let face := (faithfulLaw law).faithfulAt occurrence
    (scalarPairingRoot law).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((scalarPairingRoot law).emitted state) =
      .inl ⟨PUnit.unit, scalarPairing? law occurrence⟩ ∧
    (match face.settleRelations with
      | .sound soundness =>
          scalarPairing? law occurrence =
              some (rankOnePairing (face.completionEvaluation soundness)) ∧
            ∀ left right,
              rankOnePairing (face.completionEvaluation soundness) left right =
                face.completionEvaluation soundness left *
                  face.completionEvaluation soundness right
      | .unsound _ =>
          scalarPairing? law occurrence = none ∧
            ∃ relation : ((historyLaw law).historyAt occurrence).relationClosure,
              face.freeEvaluation
                (installedRelationAction law occurrence relation).1 ≠ 0) ∧
    HEq (((scalarPairingRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((scalarPairingRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  let occurrence := emitted D state
  let face := (faithfulLaw law).faithfulAt occurrence
  have branch :
      match face.settleRelations with
      | .sound soundness =>
          scalarPairing? law occurrence =
              some (rankOnePairing (face.completionEvaluation soundness)) ∧
            ∀ left right,
              rankOnePairing (face.completionEvaluation soundness) left right =
                face.completionEvaluation soundness left *
                  face.completionEvaluation soundness right
      | .unsound _ =>
          scalarPairing? law occurrence = none ∧
            ∃ relation : ((historyLaw law).historyAt occurrence).relationClosure,
              face.freeEvaluation
                (installedRelationAction law occurrence relation).1 ≠ 0 := by
    cases settled : face.settleRelations with
    | sound soundness =>
        refine ⟨?_, fun _ _ => rfl⟩
        change (match face.settleRelations with
          | .sound witness => some (rankOnePairing (face.completionEvaluation witness))
          | .unsound _ => none) = _
        rw [settled]
    | unsound obstruction =>
        obtain ⟨relation, belongs, nonzero⟩ :=
          face.unsoundRelationWitness obstruction
        refine ⟨?_, ⟨⟨relation, belongs⟩, ?_⟩⟩
        · change (match face.settleRelations with
            | .sound witness => some (rankOnePairing (face.completionEvaluation witness))
            | .unsound _ => none) = _
          rw [settled]
          rfl
        change face.freeEvaluation relation ≠ 0
        exact nonzero
  exact ⟨rfl, branch, (scalarPairing_inventory_ledger_next law state).2.1,
    (scalarPairing_inventory_ledger_next law state).2.2⟩

#print axioms scalarPairing_inventory_ledger_next
#print axioms scalarPairing_source_branch

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
