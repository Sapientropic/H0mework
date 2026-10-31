import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.SourceNativeDependentFaceLaw

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.UniversalRootGrammar
universe u
noncomputable section
variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  (source : SourceNativeLedgerSource N V)

/-- Reflect the exact existing whole-ledger compiler output. A passed
reflection does not assert that an economic task has been completed. -/
def vocabulary : SourceNativeDependentFaceVocabulary source where
  Scenario := PUnit.{u+1}
  scenarioDecidableEq := inferInstance
  actualScenario := PUnit.unit
  FaceAt := fun _ => PUnit.{u+1}
  PassedAt := fun occurrence _ _ =>
    {image : SourceNativeLedgerEvolutionAt source.source occurrence //
      image = source.ledgerCompiler.compile occurrence}
  ResidualBearerAt := fun _ _ _ => PEmpty.{u+1}
  SourceOwnershipAt := fun _ _ _ _ => PEmpty.{u+1}
  ConsumerAt := fun _ _ _ _ => PEmpty.{u+1}
  DispositionAt := fun _ _ _ _ _ => PEmpty.{u+1}

def point {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    SourceGeneratedClassifiedDependentFacePointAt (vocabulary source) occurrence :=
  ⟨PUnit.unit,PUnit.unit,.inl ⟨source.ledgerCompiler.compile occurrence,rfl⟩⟩

def trace {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :=
  RootedAccountedUnfolding.occur (point source occurrence) .nil

theorem trace_is_the_exact_single_source_image {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) :
    (trace source occurrence).trace = [point source occurrence] := rfl

def law : SourceNativeDependentFaceFamilyLaw source where
  vocabulary := vocabulary source
  traceAt := trace source
  traceNodup := by intro current occurrence; rw [trace_is_the_exact_single_source_image]; simp
  scenarioNonempty := by
    intro current occurrence scenario
    cases scenario
    exact ⟨point source occurrence,by rw [trace_is_the_exact_single_source_image]; exact List.mem_singleton_self _,rfl⟩
  scenarioFaceExactlyOnce := by
    intro current occurrence scenario face
    cases scenario
    cases face
    refine ⟨point source occurrence,⟨?_,rfl,rfl⟩,?_⟩
    · rw [trace_is_the_exact_single_source_image]
      exact List.mem_singleton_self _
    · intro candidate present
      have listed := present.1
      rw [trace_is_the_exact_single_source_image] at listed
      exact List.mem_singleton.mp listed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition
