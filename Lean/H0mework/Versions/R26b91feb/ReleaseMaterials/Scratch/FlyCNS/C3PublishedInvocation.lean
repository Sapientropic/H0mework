import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BoundPublication
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3RootSplice
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3CompleteInventory

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3PublishedInvocation
open ContentReentryIO

def raw (source : ContentReentryIO.Source) (before : Current source.material) : _root_.FlyCNS.C3BoundState.RawCurrent :=
  let named := (List.finRange 59).toArray.map fun i =>
    let field := before.words.get i
    ((source.material.layout.get i).name,
      _root_.FlyCNS.C3Integer.Word.mk field.vector.width (field.bytes.extract field.vector.dataStart field.bytes.size))
  ⟨named,before.backend.get ⟨3,by decide⟩,before.visit⟩

structure At (source : ContentReentryIO.Source) (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (before : Current source.material) where
  private mk ::
  published : _root_.FlyCNS.C3Published.Result
  after : Current source.material
  generated : _root_.FlyCNS.C3BoundPublication.generate installed (raw source before)=.ok published
  parsed : C3RootSplice.current source published.numerical=.ok after
  nextVisit : after.visit=before.visit+1
  nextTick : after.tick=before.tick+(BodyFullIO.operationAt before.visit).microTicks
  nextPhysics : physicsTick source.material after.words=physicsTick source.material before.words+
    10*(BodyFullIO.operationAt before.visit).microTicks

/-- Source-owned pure invocation retains the result produced by its own
fixed kernel and parser. No after or completed commuting equation is input. -/
def generate (source : ContentReentryIO.Source) (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (before : Current source.material) : Except String (At source installed before) := do
  if installed.identity.instanceId != source.material.instanceId ||
      installed.identity.occurrenceId != source.material.occurrenceId ||
      installed.identity.installationId != source.material.installationId then
    throw "pure material belongs to another source"
  match generated:_root_.FlyCNS.C3BoundPublication.generate installed (raw source before) with
  | .error why => throw why
  | .ok published =>
    match parsed:C3RootSplice.current source published.numerical with
    | .error why => throw why
    | .ok after =>
      if visit:after.visit=before.visit+1 then
        if tick:after.tick=before.tick+(BodyFullIO.operationAt before.visit).microTicks then
          if physical:physicsTick source.material after.words=physicsTick source.material before.words+
              10*(BodyFullIO.operationAt before.visit).microTicks then
            return ⟨published,after,generated,parsed,visit,tick,physical⟩
          else throw "the pure source omits a physical microcycle"
        else throw "the pure source omits a neural microcycle"
      else throw "the pure source omits its registered next visit"

def complete {source : ContentReentryIO.Source} {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {before : Current source.material} (event : At source installed before) : C3CompleteInventory.Image :=
  ⟨capture event.after,
    ⟨#[event.published.numerical.events,event.published.learning,
      event.published.numerical.physics.getD ByteArray.empty],rfl⟩,
    C3CompleteInventory.sourceMetadata source⟩

theorem generated_source {source : ContentReentryIO.Source} {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {before : Current source.material} (event : At source installed before) :
    _root_.FlyCNS.C3BoundPublication.generate installed (raw source before)=.ok event.published := event.generated

theorem parsed_current {source : ContentReentryIO.Source} {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {before : Current source.material} (event : At source installed before) :
    C3RootSplice.current source event.published.numerical=.ok event.after := event.parsed

end C3PublishedInvocation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
