import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentReentryIO
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SuccessfulKernel
set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3RootSplice
open ContentReentryIO RepresentationIO

/-- The source-owned writer's complete output enters the original Current
type. This mouth decodes produced data; it does not accept an evaluator of F. -/
def current (source : ContentReentryIO.Source) (result : _root_.FlyCNS.C3Successful.Result) :
    Except String (Current source.material) := do
  let written := result.written
  if count : written.words.size=59 then
    let words : Vector ByteArray 59 := ⟨written.words,count⟩
    let parsed ← Vector.ofFnM fun i => BodyIO.parseWord (source.material.layout.get i) (words.get i)
    if backendCount : written.archives.size=3 then
      let backends : Vector ByteArray 3 := ⟨written.archives,backendCount⟩
      let complete : Vector ByteArray 4 := backends++(⟨#[written.sourceDocument],rfl⟩ : Vector ByteArray 1)
      let image : ContentFullPackedIO.Image := ⟨parsed.map captureWord,complete,written.header,written.visit⟩
      ContentReentryIO.parseCurrentImage source image
    else .error "the pure source writer omitted an original backend"
  else .error "the pure source writer omitted an original word"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3RootSplice
