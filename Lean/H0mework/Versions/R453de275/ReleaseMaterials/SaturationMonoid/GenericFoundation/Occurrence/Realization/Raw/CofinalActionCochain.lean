import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalAction
import H0mework.Versions.R453de275.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel

/-!
# A relation-differential face of the original raw action receipt

The source event already supplies the complete relation history. The existing
relation-complex producer computes its complex and evaluator from that history.
The source projection has a `Type 0` payload; its category-valued complex lives
in `Type 1`. Install the actual relation differential in the original payload
universe, then read the full complex from that action and history. The raw
material and faithful residual remain installed beside it on the same root.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalHistorySettlementFace
open CofinalRelationGeneratedComplex
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section

variable {D : Dynamics.{0}} {Carrier : Type} [AddCommGroup Carrier]

/-- The installed `Type 0` action is the differential's actual relation
inclusion. Its full `Type 1` complex is generated from the same history. -/
def cochainComponent (law : Law D Carrier) :
    SourceNativeProjectionLaw (restructuringSource D).toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun _ {_} occurrence _ =>
    ((historyLaw law).historyAt occurrence).relationClosure →ₗ[ℤ]
      ((historyLaw law).historyAt occurrence).generatorClosure
  project := fun _ {_} occurrence _ =>
    relationInclusion ((historyLaw law).historyAt occurrence)

def installedRelationAction (law : Law D Carrier)
    {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ((historyLaw law).historyAt occurrence).relationClosure →ₗ[ℤ]
      ((historyLaw law).historyAt occurrence).generatorClosure :=
  (cochainComponent law).project PUnit.unit occurrence PUnit.unit

def cochainSource (law : Law D Carrier) :
    SourceNativeAuthoritySource (network D) (vocabulary D) :=
  ((residualRoot law).source).withProjectionCoface (cochainComponent law)

def cochainRoot (law : Law D Carrier) :
    SourceNativeAuthoritativeRootClosure (network D) (vocabulary D) where
  source := cochainSource law
  emitted := emitted D
  compiler_commutes := (residualRoot law).compiler_commutes

theorem cochainRoot_same_lower (law : Law D Carrier) :
    (cochainRoot law).toLedgerRoot = (root D).toAuthoritativeRoot.toLedgerRoot :=
  rfl

/-- The old raw material and residual coordinates are inherited, rather than
being reconstructed or replaced by the new differential projection. -/
def oldFaceInstallation (law : Law D Carrier) :
    SourceNativeProjectionLaw.InstallationAt
      (residualRoot law).source.projectionLaw
      (cochainRoot law).source.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (residualRoot law).source (cochainComponent law)

theorem generated_cochain_residual_ledger_next
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    (cochainRoot law).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((cochainRoot law).emitted state) =
      .inl ⟨PUnit.unit,
        relationInclusion ((historyLaw law).historyAt occurrence)⟩ ∧
    HEq ((cochainRoot law).source.projectionLaw.outcomeAt
        (.inherited (.component PUnit.unit))
        ((cochainRoot law).emitted state))
      ((residualRoot law).source.projectionLaw.outcomeAt
        (.component PUnit.unit) ((residualRoot law).emitted state)) ∧
    HEq (((cochainRoot law).toLedgerRoot.generatedLedgerAt state).entryDisposition
      (entry D state))
      (LedgerEntryDispositionAt.evolved
        (LedgerEntryEvolutionAt.transferred (D.emit state)
          rfl rfl (Nat.le_refl _) :
            LedgerEntryEvolutionAt (network D)
              (entry D state) (entry D (D.update (D.emit state))))) ∧
    ((cochainRoot law).toRoot.evolutionAt state).nextCurrent? =
      some (D.update (D.emit state)) := by
  exact ⟨rfl, (oldFaceInstallation law).outcome_heq (emitted D state)
      (.component PUnit.unit), (generated_event_ledger_next law state).2.1,
    (generated_event_ledger_next law state).2.2⟩

/-- The installed action is the canonical complex's differential. The old
completion kills exactly its image; a zero read cannot erase an additional
relation or manufacture a free inverse. -/
theorem generated_cochain_kernel_exact
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    ((natComplex history).d 0 1).hom =
      installedRelationAction law occurrence ∧
    ∀ value : history.generatorClosure,
      history.completionProjection value = 0 ↔
        ∃ relation : history.relationClosure,
          installedRelationAction law occurrence relation = value := by
  dsimp only
  have differential_eq :
      ((natComplex ((historyLaw law).historyAt (emitted D state))).d 0 1).hom =
        installedRelationAction law (emitted D state) := by
    rw [natComplex_d_zero_one]
    rfl
  refine ⟨differential_eq, ?_⟩
  intro value
  rw [← differential_eq]
  exact completion_zero_iff_generated_boundary
    ((historyLaw law).historyAt (emitted D state)) value

/-- The actual evaluator kills every installed source differential exactly
when it descends to the original relation completion. The positive map is
constructed by the existing faithful face; the negative side cannot be
filled by a target-supplied factor. -/
theorem generated_differential_descent_iff
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    let face := (faithfulLaw law).faithfulAt occurrence
    (∀ relation : history.relationClosure,
      face.freeEvaluation
        (installedRelationAction law occurrence relation).1 = 0) ↔
      ∃ factor : history.CompletionCarrier →ₗ[ℤ] Carrier,
        ∀ value : history.generatorClosure,
          factor (history.completionProjection value) =
            face.freeEvaluation value.1 := by
  let occurrence := emitted D state
  let history := (historyLaw law).historyAt occurrence
  let face := (faithfulLaw law).faithfulAt occurrence
  constructor
  · intro killed
    have sound : face.RelationsSound := by
      intro relation belongs
      change face.freeEvaluation relation = 0
      have killedRelation := killed ⟨relation, belongs⟩
      change face.freeEvaluation relation = 0 at killedRelation
      exact killedRelation
    cases outcome : face.settleRelations with
    | sound soundness =>
        refine ⟨face.completionEvaluation soundness, ?_⟩
        intro value
        rfl
    | unsound obstruction =>
        obtain ⟨relation, belongs, nonzero⟩ :=
          face.unsoundRelationWitness obstruction
        exact False.elim (nonzero (sound belongs))
  · rintro ⟨factor, factors⟩ relation
    have zero : history.completionProjection
        (installedRelationAction law occurrence relation) = 0 :=
      ((generated_cochain_kernel_exact law state).2 _).2 ⟨relation, rfl⟩
    have atBoundary := factors (installedRelationAction law occurrence relation)
    rw [zero, map_zero] at atBoundary
    exact atBoundary.symm

#print axioms generated_cochain_residual_ledger_next
#print axioms generated_cochain_kernel_exact
#print axioms generated_differential_descent_iff

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
