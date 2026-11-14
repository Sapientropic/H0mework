import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeMinimum

set_option autoImplicit false
namespace FlyCNS.C3NativeMinimumControls
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence C3NativeMinimum

example {boundary : Boundary} (installed : Installed boundary) (input : Letter) (why : String) :
    effect installed input (.error why)=.error why := rfl
example {boundary : Boundary} (installed : Installed boundary) (word : List Letter) (why : String) :
    execute installed word (.error why)=.error why := execute_error _ _ _
example {boundary : Boundary} (installed : Installed boundary) (anchor : Anchor boundary) :
    decode installed anchor (encode (fromWord boundary installed anchor []))=.ok anchor.base := decode_encode (fromWord boundary installed anchor [])
example {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (current : Carrier boundary installed anchor) : unpack (pack current)=current := unpack_pack current
example {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (word : List Letter) (observer : Fin 69) (current : Carrier boundary installed anchor) :
    encodedRead observer (WholeRepresentation.runMap encodedAction word (pack current))=
      read observer (execute installed word current.val) := all_readers_zero_error _ _ _
example {boundary : Boundary} {installed : Installed boundary} {anchor : Anchor boundary}
    (before : Ready boundary installed anchor)
    (event : ContentReentryRoot.PublishedAt boundary.source installed.material before.current.current)
    (observer : Fin 69) : read observer (consumePublished before event).val=
      Except.ok (C3CompleteInventory.read (C3ReachableModel.reader observer) (C3CompleteInventory.fromActual event.original)) :=
  consumed_same_image before event observer

#print axioms C3NativeMinimum.key_injective
#print axioms C3NativeMinimum.minimum_future_kernel
#print axioms C3NativeMinimum.all_readers_zero_error
#print axioms C3NativeMinimum.minimal_other_implementations
#print axioms C3NativeMinimum.advance_published
#print axioms C3NativeMinimum.consumePublished
#print axioms C3NativeMinimum.consumed_same_image

end FlyCNS.C3NativeMinimumControls
