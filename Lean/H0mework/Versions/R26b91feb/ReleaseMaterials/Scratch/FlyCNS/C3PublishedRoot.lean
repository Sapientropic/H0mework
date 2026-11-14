import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentReentryRoot
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3FiniteOccurrence

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3PublishedRoot
open ContentReentryIO ContentReentryRoot

def complete {source : ContentReentryIO.Source} {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {before : Current source.material} (event : ContentReentryRoot.PublishedAt source installed before) :
    C3CompleteInventory.Image :=
  ⟨capture event.sourceReply.reply.after,
    ⟨#[event.sourceReply.published.numerical.events,event.sourceReply.published.learning,
      event.sourceReply.published.numerical.physics.getD ByteArray.empty],rfl⟩,
    C3CompleteInventory.sourceMetadata source⟩

theorem same_complete_occurrence {source : ContentReentryIO.Source}
    {installed : _root_.FlyCNS.C3BoundKernel.Installation} {before : Current source.material}
    (event : ContentReentryRoot.PublishedAt source installed before) :
    complete event=C3CompleteInventory.fromActual event.original := by
  simp only [complete,C3CompleteInventory.fromActual,ContentReentryRoot.PublishedAt.original,
    ContentReentryRoot.GeneratedAt.next,event.sourceReply.events,event.sourceReply.learning,event.sourceReply.physics]

theorem every_original_reader {source : ContentReentryIO.Source}
    {installed : _root_.FlyCNS.C3BoundKernel.Installation} {before : Current source.material}
    (event : ContentReentryRoot.PublishedAt source installed before) (reader : C3CompleteInventory.Reader) :
    C3CompleteInventory.read reader (complete event)=
      C3CompleteInventory.read reader (C3CompleteInventory.fromActual event.original) :=
  congrArg (C3CompleteInventory.read reader) (same_complete_occurrence event)

theorem actual_whole_six {source : ContentReentryIO.Source}
    {installed : _root_.FlyCNS.C3BoundKernel.Installation} {before : Current source.material}
    (event : ContentReentryRoot.PublishedAt source installed before) (responsibility : Responsibility) :
    (event.original.patch.toLedgerWriteEvolution.destination (ContentReentryRoot.entry source before responsibility)).1 =
      ContentReentryRoot.entry source event.sourceReply.reply.after responsibility :=
  ContentReentryRoot.published_all_original_rows source event responsibility

end C3PublishedRoot
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
