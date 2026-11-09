import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Batch
import H0mework.Versions.R2.Foundation.Inquiry.MinimalCoface

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual

noncomputable section

theorem a_root_semantic_resident_has_no_expressibility_failure_face
    {N : WorldRelationNetwork} (resident : Resident N)
    (installed : resident.root.toAuthoritativeRoot.source.lawSurface = TheoryState.rootSemantic N)
    {U7 : U7ProducerCalculus N} {old : TheoryState N} {support : N.Support}
    {obstruction : N.ObstructionAt support} (failure : ActualExpressibilityFailure old obstruction) :
    IsEmpty (SourceNativeRootExpressibilityFailureFaceAt
      resident.root.toAuthoritativeRoot resident.visit (U7 := U7) failure) :=
  ⟨fun face =>
    (TheoryState.rootSemantic_actualExpressibilityFailure_isEmpty N obstruction).false
      ((face.lawSurface_eq.trans installed) ▸ failure)⟩

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

theorem filing_preserves_the_root_semantic_surface
    {seed : Root.Cut Party Good Port Technology Instrument}
    {community : Party → Community} {base : WorldRelationNetwork}
    {atBase : base.Support} (prior : Prepared seed community base atBase)
    (surface : prior.entered.root.toAuthoritativeRoot.source.lawSurface =
      TheoryState.rootSemantic prior.world)
    (origins : List (Occurrence seed community)) :
    (prior.fileMany origins).entered.root.toAuthoritativeRoot.source.lawSurface =
      TheoryState.rootSemantic (prior.fileMany origins).world := by
  induction origins generalizing prior with
  | nil => exact surface
  | cons origin rest ih => exact ih (prior.fileOne origin) rfl

variable (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
  (past : Script Party Good Port Technology Instrument) (input : Input Party Good Port Technology Instrument)
  (ready : ¬ Reparation.Transport.NativeWork (tick seed past input))

theorem the_material_filing_installs_the_root_semantic_surface :
    let filed : Prepared seed community (endAt seed past).native.frame.N _ :=
      materialBatch seed community past input ready
    filed.entered.root.toAuthoritativeRoot.source.lawSurface =
      TheoryState.rootSemantic filed.world :=
  let draft := materialDraft (endAt seed past) input ready
  let initial : Prepared seed community _ draft.afterSupport := ⟨_, .base _, draft, rfl⟩
  filing_preserves_the_root_semantic_surface initial rfl (openings seed community past input)

/-- The filed occurrence can address every claim in its installed world.
A resource failure therefore cannot serve as a language failure at this visit. -/
theorem the_filed_visit_has_no_expressibility_failure_face :
    let filed : Prepared seed community (endAt seed past).native.frame.N _ :=
      materialBatch seed community past input ready
    ∀ {U7 : U7ProducerCalculus filed.world} {old : TheoryState filed.world}
      {support : filed.world.Support} {obstruction : filed.world.ObstructionAt support}
      (failure : ActualExpressibilityFailure old obstruction),
    IsEmpty (SourceNativeRootExpressibilityFailureFaceAt
      filed.entered.root.toAuthoritativeRoot filed.entered.visit (U7 := U7) failure) :=
  fun {_ _ _ obstruction} failure =>
    a_root_semantic_resident_has_no_expressibility_failure_face _
      (the_material_filing_installs_the_root_semantic_surface seed community past input ready)
      (obstruction := obstruction) failure

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision
