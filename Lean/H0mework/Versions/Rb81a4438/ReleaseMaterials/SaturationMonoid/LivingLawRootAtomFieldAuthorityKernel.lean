import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.LivingLawAtomFieldSeparation
import H0mework.Foundation.Authority.SourceProjectionInventory
import H0mework.Foundation.Authority.Representation

/-!
# Generated atom field at the source-native constructive root

A registered chart and a `SurfaceAtomFieldRecognition` are presentation data.
They do not, by themselves, make the chart's local value an actual current
atom: a constant chart can expose a completed `Nat -> A` field at every finite
coordinate and make `shift` look local.

This kernel now moves the presentation law upstream of emission.  A
`SourceNativeAtomFieldGenerationLaw` fixes:

* a source-owned fixed-law native producer;
* one explicitly recognized presentation registry;
* the P7/P68 locality recognition;
* a map from constructive-root currents to the producer current;
* fixed root restrictions for anchor, incidence, and law lineage; and
* a commuting identification of every root occurrence with one native write.

The law is installed as a coordinate of the complete authority source before
the root emitter exists.  A causal `RootVisit` then fixes an exact P98/P99
finite prefix and generates its registered P7/P68 local section.  Every state
and residual chart must also have `ProperFiniteSections`: no finite section
may decode either whole ambient field.  Thus a constant chart exposing a
completed future is rejected before it can become a primitive source law.

Function types remain legal.  Pointwise finite prefixes remain legal.  What is
rejected is precisely completed-field authority, whether selected before or
after root emission.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

open ResidualProjection
open EffectiveResidualUpdate

/-! ## Constructive causal depth -/

/-- Number of actual root transitions in one causal reachability witness. -/
def RootClosure.ReachableAt.depth
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {R : RootClosure N V} {current : V.Current} :
    R.ReachableAt current -> Nat
  | .initial => 0
  | .step prior _ => prior.depth + 1

/-- One more fixed-law write reaches the target after one more generated
prefix step.  This is the P98/P99 recursion law in `GeneratedPrefix` form. -/
theorem FixedLawNativeTotal.generatedPrefix_target_succ
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {LV : _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Vocabulary C}
    (T : FixedLawNativeTotal LV)
    (source : _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current C)
    (length : Nat) :
    (T.generatedPrefix source (length + 1)).target =
      (T.write (T.generatedPrefix source length).target).next := by
  induction length generalizing source with
  | zero => rfl
  | succ length ih =>
      exact ih (T.write source).next

/-! ## Source-native generated-section law -/

/-- The atom/field law owned by one source-native ledger compiler before a
root emitter is installed.

This is the producer-side half of the earlier atom/field adapter.  A registry
and a prefix-local effective update may no longer be selected after an
authoritative root has already revealed its occurrences.  Nor may a finite
chart recover the complete ambient field.  The exact root write, its
structural compiler equation, target commuting equation, and complete source
account restriction are part of the same pre-emitter source law. -/
structure SourceNativeAtomFieldGenerationLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V)
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    (C : Carrier (K := K) (E := E)) : Type (u + 1) where
  livingVocabulary :
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Vocabulary C
  total : FixedLawNativeTotal livingVocabulary
  registry : CarrierAtomFieldRegistry C
  recognition : CarrierAtomFieldRecognition C registry
  stateProper : (surface : C.LawSurface) ->
    (registry.state surface).ProperFiniteSections
  residualProper : (surface : C.LawSurface) ->
    (registry.residual surface).ProperFiniteSections
  initial :
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current C
  currentAt : V.Current ->
    _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.Current C
  /-- The domain anchor is a fixed restriction of the root anchor. -/
  anchorProjection : V.Anchor ->
    MinimalRegistrableSourceAnchor C.SourceObservation C.Scope C.Lineage
  /-- The domain incidence is a fixed restriction of the root incidence. -/
  incidenceProjection : V.Incidence -> C.Incidence
  /-- The domain law lineage is a fixed restriction of the root lineage. -/
  lawLineageProjection : V.Lineage -> C.LawLineage
  anchor_commutes : (current : V.Current) ->
    (currentAt current).anchor = anchorProjection (V.anchorAt current)
  incidence_commutes : (current : V.Current) ->
    (currentAt current).incidence = incidenceProjection (V.incidenceAt current)
  lawLineage_commutes : (current : V.Current) ->
    (currentAt current).lawLineage =
      lawLineageProjection (V.lineageAt current)
  initial_current_eq :
    currentAt source.source.toRootSource.initial = initial
  rootWrite : {current : V.Current} ->
    source.source.toRootSource.actual.OccurrenceAt current ->
      V.NativeWriteAt current
  structural_eq : {current : V.Current} ->
    (occurrence :
      source.source.toRootSource.actual.OccurrenceAt current) ->
      source.source.toRootSource.actual.compile occurrence =
        .nativeWrite (rootWrite occurrence)
  target_commutes : {current : V.Current} ->
    (occurrence :
      source.source.toRootSource.actual.OccurrenceAt current) ->
      currentAt (V.nativeTarget (rootWrite occurrence)) =
        (total.write (currentAt current)).next

/-- No finite registered state section of an authority-bearing atom/field law
can decode its completed ambient state. -/
theorem SourceNativeAtomFieldGenerationLaw.noCompletedStateAmbientAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    (law : SourceNativeAtomFieldGenerationLaw source C)
    (surface : C.LawSurface) (scope : Nat) :
    IsEmpty ((law.registry.state surface).CompletedAmbientAt scope) :=
  (law.stateProper surface).noCompletedAmbient scope

/-- Residual fields obey the same finite-section wall as state fields.  A
completed future cannot move from `State` into the residual carrier and regain
authority through an otherwise local update. -/
theorem SourceNativeAtomFieldGenerationLaw.noCompletedResidualAmbientAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    (law : SourceNativeAtomFieldGenerationLaw source C)
    (surface : C.LawSurface) (scope : Nat) :
    IsEmpty ((law.registry.residual surface).CompletedAmbientAt scope) :=
  (law.residualProper surface).noCompletedAmbient scope

/-- The exact atom/field compiler image at one source-native occurrence.  The
payload contains the two equations which make the local effective write the
same actual root transition; a projection carrying only a branch tag cannot
stand in for this law. -/
structure SourceNativeGeneratedAtomFieldOccurrenceAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    (law : SourceNativeAtomFieldGenerationLaw source C)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    Type u where
  structural_eq :
    source.source.toRootSource.actual.compile occurrence =
      .nativeWrite (law.rootWrite occurrence)
  target_commutes :
    law.currentAt (V.nativeTarget (law.rootWrite occurrence)) =
      (law.total.write (law.currentAt current)).next

/-- The atom/field producer as a singleton source component.  `PUnit` selects
the one coordinate; the dependent payload retains the complete generation law
and exact root occurrence. -/
def SourceNativeAtomFieldGenerationLaw.toProjectionLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeLedgerSource N V}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    (law : SourceNativeAtomFieldGenerationLaw source C) :
    SourceNativeProjectionLaw source where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ =>
    SourceNativeGeneratedAtomFieldOccurrenceAt law occurrence
  project := fun _ {_current} occurrence _ =>
    ⟨law.structural_eq occurrence, law.target_commutes occurrence⟩

/-- Source-inventory coordinate used when adjoining the generated atom/field
law to an existing projection inventory. -/
inductive SourceNativeAtomFieldProjection (Base : Type u) : Type u
  | atomField
  | inherited (projection : Base)

/-- Install the atom/field producer in the complete authority-source identity
before emission.  Existing coordinates are preserved verbatim. -/
def SourceNativeAtomFieldGenerationLaw.toAuthoritySource
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeAtomFieldGenerationLaw
      base.restructuringSource.toLedgerSource C) :
    SourceNativeAuthoritySource N V where
  restructuringSource := base.restructuringSource
  eventInventoryAdmission := base.eventInventoryAdmission
  lawSurface := base.lawSurface
  projectionLaw :=
    { Projection := SourceNativeAtomFieldProjection
        base.projectionLaw.Projection
      ActiveAt := fun projection {_current} occurrence =>
        match projection with
        | .atomField => PUnit
        | .inherited inherited =>
            base.projectionLaw.ActiveAt inherited occurrence
      InactiveAt := fun projection {_current} occurrence =>
        match projection with
        | .atomField => PEmpty
        | .inherited inherited =>
            base.projectionLaw.InactiveAt inherited occurrence
      classify := by
        intro projection current occurrence
        cases projection with
        | atomField => exact .inl PUnit.unit
        | inherited inherited =>
            exact base.projectionLaw.classify inherited occurrence
      PayloadAt := fun projection {_current} occurrence active =>
        match projection with
        | .atomField => SourceNativeGeneratedAtomFieldOccurrenceAt law occurrence
        | .inherited inherited =>
            base.projectionLaw.PayloadAt inherited occurrence active
      project := by
        intro projection current occurrence active
        cases projection with
        | atomField =>
            exact ⟨law.structural_eq occurrence, law.target_commutes occurrence⟩
        | inherited inherited =>
            exact base.projectionLaw.project inherited occurrence active }

/-- Compatibility installation for roots constructed by adjoining the
atom/field component to a base source.  Recognition itself consumes only this
installed singleton component and cannot reconstruct the base source. -/
def SourceNativeProjectionLaw.InstallationAt.atomFieldComponent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    (base : SourceNativeAuthoritySource N V)
    (law : SourceNativeAtomFieldGenerationLaw
      base.restructuringSource.toLedgerSource C) :
    SourceNativeProjectionLaw.InstallationAt law.toProjectionLaw
      (law.toAuthoritySource base).projectionLaw where
  embed := fun _ => SourceNativeAtomFieldProjection.atomField
  embed_injective := by
    intro left right _
    cases left
    cases right
    rfl
  outcome_heq := by
    intro current occurrence projection
    cases projection
    rfl

/-! ## Fixed-root installed recognition -/

/-- Recognition that an already fixed authoritative root was born with this
atom/field law in its complete source inventory.  The recognition can no
longer add a registry or compiler after seeing the emitted branch. -/
structure SourceNativeAtomFieldRecognitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (world : SourceNativeAuthoritativeRootClosure N V)
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    (C : Carrier (K := K) (E := E)) : Type (u + 1) where
  generationLaw : SourceNativeAtomFieldGenerationLaw world.toLedgerRoot.source C
  installation : SourceNativeProjectionLaw.InstallationAt
    generationLaw.toProjectionLaw
    world.source.projectionLaw

namespace SourceNativeAtomFieldRecognitionAt

/-- Exact component law installed in the fixed source inventory. -/
def component
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C) :
    SourceNativeProjectionLaw world.toLedgerRoot.source :=
  recognition.generationLaw.toProjectionLaw

/-- Root coordinate occupied by the installed generated atom/field law. -/
def rootProjection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C) :
    world.source.projectionLaw.Projection :=
  recognition.installation.embed PUnit.unit

/-- The atom/field current cannot open a sibling source account: its anchor is
the source-fixed restriction of the exact root current's anchor. -/
theorem currentAnchor_eq_rootProjection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (current : V.Current) :
    (recognition.generationLaw.currentAt current).anchor =
      recognition.generationLaw.anchorProjection (V.anchorAt current) :=
  recognition.generationLaw.anchor_commutes current

/-- The atom/field current's responsibility incidence is the fixed root
restriction, not a domain-selected parallel slot. -/
theorem currentIncidence_eq_rootProjection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (current : V.Current) :
    (recognition.generationLaw.currentAt current).incidence =
      recognition.generationLaw.incidenceProjection (V.incidenceAt current) :=
  recognition.generationLaw.incidence_commutes current

/-- Law lineage is restricted from the same root current. -/
theorem currentLawLineage_eq_rootProjection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (current : V.Current) :
    (recognition.generationLaw.currentAt current).lawLineage =
      recognition.generationLaw.lawLineageProjection (V.lineageAt current) :=
  recognition.generationLaw.lawLineage_commutes current

/-- The exact generated atom/field compiler image is already a coordinate of
the fixed root source.  It is not attached to the world after emission. -/
theorem componentOutcome_heq_rootOutcome
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    {current : V.Current}
    (occurrence : world.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    HEq (world.source.projectionLaw.outcomeAt
          recognition.rootProjection occurrence)
      (recognition.component.outcomeAt
        PUnit.unit occurrence) :=
  recognition.installation.outcome_heq occurrence PUnit.unit

/-- The installed atom/field payload is a dependent restriction of the exact
temporal root occurrence.  The generated local section may refine this
payload, but it cannot acquire authority from a sibling current or a detached
field presentation. -/
theorem installedAuthority_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    {visit : SourceNativeTemporalVisitAt world.toLedgerRoot}
    (authority : SourceNativeAuthoritativeTemporalEvolutionAt world visit) :
    authority.toLedgerReadout =
        world.toLedgerRoot.generatedAtTemporalVisit visit ∧
      HEq (authority.toLedgerReadout.projectionOutcome
          recognition.rootProjection)
        (recognition.component.outcomeAt
          PUnit.unit
          (world.emitted visit.current)) := by
  exact
    authority.installedSubsystemAuthority_factorizes
      recognition.installation PUnit.unit

/-- Every causal root visit is the exact target of the same source-owned
P98/P99 native prefix. -/
private theorem currentAt_eq_generatedPrefix_target
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (visit : RootVisit world.toRoot) :
    recognition.generationLaw.currentAt visit.current =
      (recognition.generationLaw.total.generatedPrefix
        recognition.generationLaw.initial
        visit.history.depth).target := by
  cases visit with
  | mk current history =>
    change recognition.generationLaw.currentAt current =
      (recognition.generationLaw.total.generatedPrefix
        recognition.generationLaw.initial history.depth).target
    induction history with
    | initial =>
        exact recognition.generationLaw.initial_current_eq
    | @step current next prior next_eq ih =>
        let occurrence := world.emitted current
        let write := recognition.generationLaw.rootWrite occurrence
        have structural :
            world.toRoot.evolutionAt current =
              .nativeWrite write := by
          exact recognition.generationLaw.structural_eq occurrence
        have target_eq : V.nativeTarget write = next := by
          rw [structural] at next_eq
          exact Option.some.inj next_eq
        have commute := recognition.generationLaw.target_commutes occurrence
        rw [target_eq] at commute
        calc
          recognition.generationLaw.currentAt next =
              (recognition.generationLaw.total.write
                (recognition.generationLaw.currentAt current)).next := commute
          _ = (recognition.generationLaw.total.write
                (recognition.generationLaw.total.generatedPrefix
                  recognition.generationLaw.initial
                  prior.depth).target).next := by rw [ih]
          _ = (recognition.generationLaw.total.generatedPrefix
                recognition.generationLaw.initial
                (prior.depth + 1)).target :=
              (ConstructiveRoot.FixedLawNativeTotal.generatedPrefix_target_succ
                recognition.generationLaw.total
                recognition.generationLaw.initial prior.depth).symm

/-- Canonical P7/P68/P98/P99 local section at one exact root visit.

The section is computed from the registered charts and the same fixed-law
prefix already forced by the root chronology.  No local value, ambient state,
scope, or chart is supplied at this mouth. -/
def generatedLocalSectionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (visit : RootVisit world.toRoot) :
    GeneratedLocalSectionAt recognition.generationLaw.total
      recognition.generationLaw.recognition
      recognition.generationLaw.initial visit.history.depth := by
  let generated := recognition.generationLaw.total.generatedPrefix
    recognition.generationLaw.initial
    visit.history.depth
  exact
    { generated := generated
      stateSection :=
        (recognition.generationLaw.registry.state
          generated.target.surface).cover.toLocal
          visit.history.depth generated.target.residual.state
      stateSection_eq := rfl
      residualSection :=
        (recognition.generationLaw.registry.residual
          generated.target.surface).cover.toLocal
          visit.history.depth generated.target.residual.value
      residualSection_eq := rfl
      target_state_eq_generatedField :=
        recognition.generationLaw.total.generatedPrefix_target_state_eq_generatedTimeField
          recognition.generationLaw.initial visit.history.depth }

/-- The registered atom/field section and the source-fixed projected current
are the same fixed-law prefix target at this exact causal depth.  This is a
coordinate theorem: it does not assert that `currentAt` is injective on the
whole root current. -/
theorem projectedCurrent_eq_localSection
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (visit : RootVisit world.toRoot) :
    recognition.generationLaw.currentAt visit.current =
      (recognition.generatedLocalSectionAt visit).generated.target :=
  recognition.currentAt_eq_generatedPrefix_target visit

/-- The root-indexed local section retains its source-backed finite temporal
scope. -/
theorem localSection_sourceBacked
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {K E : Type u} [Field K] [AddCommGroup E] [Module K E]
    {C : Carrier (K := K) (E := E)}
    {world : SourceNativeAuthoritativeRootClosure N V}
    (recognition : SourceNativeAtomFieldRecognitionAt world C)
    (visit : RootVisit world.toRoot) :
    satisfiesC1
      (recognition.generatedLocalSectionAt visit).temporalSection :=
  (recognition.generatedLocalSectionAt visit).sourceBacked

end SourceNativeAtomFieldRecognitionAt

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
