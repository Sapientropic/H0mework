import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionScalarPairing
import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel

/-!
# The complete free carrier enters the existing four-face producer

The actual scalar evaluator is defined on the entire free integer lattice,
including relations that it does not kill. Its rank-one pairing is therefore
source-generated at every branch of the original exposure. Quotient pairing
remains the separately installed conditional face; no unsound branch is
assigned a fake quotient map. The existing four-face producer consumes the
full exposure, history, cochain, topology and evaluator in one occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalHistorySettlement
open CofinalRelationGeneratedComplex
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open CofinalAllPrimeTopology
open UnifiedFourFace
open CategoryTheory

noncomputable section

variable {D : Dynamics.{0}}

abbrev FreeLattice (law : Law D ℤ) := law.Generator →₀ ℤ

def freeSourcePairing (law : Law D ℤ)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    FreeLattice law →ₗ[ℤ] Module.Dual ℤ (FreeLattice law) :=
  rankOnePairing ((faithfulLaw law).faithfulAt occurrence).freeEvaluation

def freePairingComponent (law : Law D ℤ) :
    SourceNativeProjectionLaw (restructuringSource D).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} _ _ =>
    FreeLattice law →ₗ[ℤ] Module.Dual ℤ (FreeLattice law)
  project := fun _ {_} occurrence _ => freeSourcePairing law occurrence

def fullSource (law : Law D ℤ) :
    SourceNativeAuthoritySource (network D) (vocabulary D) :=
  ((scalarPairingRoot law).source).withProjectionCoface (freePairingComponent law)

def fullRoot (law : Law D ℤ) :
    SourceNativeAuthoritativeRootClosure (network D) (vocabulary D) where
  source := fullSource law
  emitted := emitted D
  compiler_commutes := (scalarPairingRoot law).compiler_commutes

def oldScalarInstallation (law : Law D ℤ) :
    SourceNativeProjectionLaw.InstallationAt
      (scalarPairingRoot law).source.projectionLaw
      (fullRoot law).source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (scalarPairingRoot law).source (freePairingComponent law)

def residualToFullInstallation (law : Law D ℤ) :
    SourceNativeProjectionLaw.InstallationAt
      (residualRoot law).source.projectionLaw
      (fullRoot law).source.projectionLaw :=
  ((oldFaceInstallation law).trans (oldCochainInstallation law)).trans
    (oldScalarInstallation law)

theorem fullRoot_same_lower (law : Law D ℤ) :
    (fullRoot law).toLedgerRoot = (root D).toAuthoritativeRoot.toLedgerRoot :=
  rfl

abbrev SourceOccurrence (_law : Law D ℤ) (state : D.State) :=
  (source D).toRootSource.actual.OccurrenceAt state

abbrev AlgebraFace (law : Law D ℤ) (state : D.State) :=
  SourceOccurrence law state ×
    (FreeLattice law →ₗ[ℤ] Module.Dual ℤ (FreeLattice law))

abbrev CombinatorialFace (law : Law D ℤ) (state : D.State) :=
  Σ occurrence : SourceOccurrence law state,
    RootGeneratedCofinalHistoryAt
      ((historyLaw law).rootOccurrenceAt occurrence)
      ((historyLaw law).seedAt occurrence)
      ((historyLaw law).continuationAt occurrence)

abbrev TopologicalFace (law : Law D ℤ) (state : D.State) :=
  Σ occurrence : SourceOccurrence law state,
    TopologicalAt ((historyLaw law).historyAt occurrence)

abbrev LogicalFace (law : Law D ℤ) (state : D.State) :=
  Σ occurrence : SourceOccurrence law state,
    PLift (∀ degree : Nat,
      differential ((historyLaw law).historyAt occurrence) degree ≫
        differential ((historyLaw law).historyAt occurrence) (degree + 1) = 0)

abbrev RelationFace (law : Law D ℤ) (state : D.State) :=
  Σ occurrence : SourceOccurrence law state,
    RootGeneratedCofinalFaithfulRealizationAt
      ((historyLaw law).historyAt occurrence)
      ((faithfulLaw law).evaluatorOccurrenceAt occurrence)

abbrev CochainFace (law : Law D ℤ) (state : D.State) :=
  SourceOccurrence law state ×
    CochainComplex (ModuleCat ℤ) ℕ

def fullInput (law : Law D ℤ) (state : D.State) :
    UnifiedFourFace.Input
      (SourceOccurrence law state)
      (AlgebraFace law state)
      (CombinatorialFace law state)
      (TopologicalFace law state)
      (LogicalFace law state)
      (RelationFace law state)
      (CochainFace law state)
      (FreeLattice law) (FreeLattice law) where
  occurrence := law.rootExposureAt (emitted D state)
  algebraAt := fun occurrence => ⟨occurrence, freeSourcePairing law occurrence⟩
  combinatorialAt := fun occurrence =>
    ⟨occurrence, (historyLaw law).historyAt occurrence⟩
  topologicalAt := fun occurrence =>
    ⟨occurrence, TopologicalAt.generate ((historyLaw law).historyAt occurrence)⟩
  logicalAt := fun occurrence =>
    ⟨occurrence, ⟨fun degree =>
      differential_sq ((historyLaw law).historyAt occurrence) degree⟩⟩
  relationAt := fun occurrence =>
    ⟨occurrence, (faithfulLaw law).faithfulAt occurrence⟩
  cochainAt := fun occurrence =>
    ⟨occurrence, natComplex ((historyLaw law).historyAt occurrence)⟩
  dualEvaluationAt := freeSourcePairing law
  faithfulAt := fun _ => LinearMap.id

def fullGenerated (law : Law D ℤ) (state : D.State) :
    UnifiedFourFace.Generated (fullInput law state) :=
  UnifiedFourFace.generate (fullInput law state)

/-- On the source-generated sound branch, the complete free pairing and the
quotient pairing agree after the original completion projection. Unsound
branches retain the free pairing and their nonzero relation residual. -/
theorem free_pairing_quotient_square
    (law : Law D ℤ) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state)
    (soundness : GeneratedRelationSoundnessAt
      ((faithfulLaw law).faithfulAt occurrence))
    (left right : ((historyLaw law).historyAt occurrence).generatorClosure) :
    rankOnePairing
      (((faithfulLaw law).faithfulAt occurrence).completionEvaluation soundness)
        (((historyLaw law).historyAt occurrence).completionProjection left)
        (((historyLaw law).historyAt occurrence).completionProjection right) =
      freeSourcePairing law occurrence left.1 right.1 :=
  rfl

theorem fullInput_root (law : Law D ℤ) (state : D.State) :
    (fullInput law state).occurrence.root = emitted D state :=
  law.rootExposure_root (emitted D state)

/-- The existing coimage/dual embedding equation is generated from the
actual free-lattice pairing, even when that evaluator cannot descend through
the source's relation completion. -/
theorem full_dual_equation (law : Law D ℤ) (state : D.State) :
    ((fullGenerated law state).embedding).comp
        (fullGenerated law state).canonical =
      freeSourcePairing law (emitted D state) := by
  have generated := UnifiedFourFace.generated_dual_readback (fullInput law state)
  change ((fullGenerated law state).embedding).comp
      (fullGenerated law state).canonical =
        freeSourcePairing law (fullInput law state).occurrence.root at generated
  rw [fullInput_root] at generated
  exact generated

theorem full_faces_original_receipt_ledger_next (law : Law D ℤ) (state : D.State) :
    let occurrence := emitted D state
    let input := fullInput law state
    let generated := fullGenerated law state
    input.occurrence.root = occurrence ∧
    generated.algebraFace = input.AlgebraOccurrence ∧
    generated.combinatorialFace = input.CombinatorialOccurrence ∧
    generated.topologicalFace = input.TopologicalOccurrence ∧
    generated.logicalFace = input.LogicalOccurrence ∧
    generated.relationFace = input.RelationOccurrence ∧
    generated.cochainFace = input.CochainOccurrence ∧
    generated.evaluationFace = input.EvaluationOccurrence ∧
    generated.faithfulFace = input.FaithfulOccurrence ∧
    generated.embedding.comp generated.canonical = freeSourcePairing law occurrence ∧
    (fullRoot law).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((fullRoot law).emitted state) =
      .inl ⟨PUnit.unit, freeSourcePairing law occurrence⟩ ∧
    (∀ old : (scalarPairingRoot law).source.projectionLaw.Projection,
      HEq ((fullRoot law).source.projectionLaw.outcomeAt
          ((oldScalarInstallation law).embed old) ((fullRoot law).emitted state))
        ((scalarPairingRoot law).source.projectionLaw.outcomeAt old
          ((scalarPairingRoot law).emitted state))) ∧
    HEq (((fullRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((fullRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  have oldFact := scalarPairing_inventory_ledger_next law state
  refine ⟨fullInput_root law state, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    full_dual_equation law state,
    rfl, fun old => (oldScalarInstallation law).outcome_heq (emitted D state) old,
    oldFact.2.1, oldFact.2.2⟩

#print axioms fullGenerated
#print axioms free_pairing_quotient_square
#print axioms full_dual_equation
#print axioms full_faces_original_receipt_ledger_next

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
