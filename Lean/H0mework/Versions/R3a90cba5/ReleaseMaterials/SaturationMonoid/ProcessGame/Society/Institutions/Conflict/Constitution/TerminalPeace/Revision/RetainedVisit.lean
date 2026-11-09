import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision.OriginalRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open Reparation.Actual
open Original (seed community history state)

noncomputable section

private theorem the_original_history_has_a_write : history ≠ [] := by
  rw [Original.exact_history]
  simp

theorem the_original_post_assault_theory_is_root_semantic :
    state.resident.root.toAuthoritativeRoot.source.lawSurface = TheoryState.rootSemantic state.world :=
  every_nonempty_original_run_installs_semantic_theory history the_original_history_has_a_write

theorem the_original_post_assault_visit_has_no_failure_face
    {U7 : U7ProducerCalculus state.world} {old : TheoryState state.world} {support : state.world.Support}
    {obstruction : state.world.ObstructionAt support} (failure : ActualExpressibilityFailure old obstruction) :
    IsEmpty (SourceNativeRootExpressibilityFailureFaceAt
      state.resident.root.toAuthoritativeRoot state.resident.visit (U7 := U7) failure) :=
  a_root_semantic_resident_has_no_expressibility_failure_face
    state.resident the_original_post_assault_theory_is_root_semantic failure

theorem old_publication_never_changes_the_post_assault_theory (suffix : Original.Word) :
    let reached := (publishAfter state suffix).next
    reached.resident.root.toAuthoritativeRoot.source.lawSurface = TheoryState.rootSemantic reached.world := by
  have nextIsOriginal : (publishAfter state suffix).next = (publish seed community (history ++ suffix)).next :=
    publication_consumes_the_retained_visit seed community history suffix
  dsimp only
  rw [nextIsOriginal]
  exact every_nonempty_original_run_installs_semantic_theory (history ++ suffix)
    (fun empty => the_original_history_has_a_write (List.append_eq_nil_iff.mp empty).1)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Revision
