import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeFinite

set_option autoImplicit false
namespace FlyCNS.C3NativeCodec
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence C3NativeMinimum

structure Seal (boundary : Boundary) where
  private mk ::
  anchor : Anchor boundary
  visit : anchor.base.current.visit=4
  tick : anchor.base.current.tick=400
  physics : C3NativePrecision.physics anchor.base=4000
  wordWidth : (ContentReentryIO.wordAt boundary.source.material anchor.base.current.words ⟨34,by decide⟩).vector.width=8
  layoutWidth : (boundary.source.material.layout.get (boundary.source.material.addresses.get ⟨34,by decide⟩)).width=8

/-- Seal the already emitted original NN400 occurrence. Its private Current,
physical word and fixed source layout determine the admitted codec width. -/
def at400 {boundary : Boundary} {before : ContentReentryIO.Current boundary.source.material}
    (event : ContentReentryRoot.GeneratedAt boundary.source before) : Except String (Seal boundary) :=
  let anchor:=fromActual (boundary:=boundary) event
  if visit:anchor.base.current.visit=4 then
    if tick:anchor.base.current.tick=400 then
      if physics:C3NativePrecision.physics anchor.base=4000 then
        if wordWidth:(ContentReentryIO.wordAt boundary.source.material anchor.base.current.words ⟨34,by decide⟩).vector.width=8 then
          if layoutWidth:(boundary.source.material.layout.get (boundary.source.material.addresses.get ⟨34,by decide⟩)).width=8 then
            .ok ⟨anchor,visit,tick,physics,wordWidth,layoutWidth⟩
          else .error "original physical layout is not an eight-byte word"
        else .error "actual physical counter is not an eight-byte word"
      else .error "actual source is not at physical4000"
    else .error "actual source is not at neural400"
  else .error "actual source is not at visit4"

theorem sealed_width {boundary : Boundary} (context : Seal boundary) : C3NativePrecision.width boundary context.anchor=8 := by
  dsimp only [C3NativePrecision.width]
  have word:=context.wordWidth
  dsimp only [ContentReentryIO.wordAt] at word
  rw [word,context.layoutWidth]
  rfl

theorem sealed_address_bound {boundary : Boundary} (context : Seal boundary) :
    C3NativePrecision.stateBound boundary context.anchor<2^56 := by
  rw [C3NativePrecision.stateBound,context.visit,sealed_width]
  norm_num

theorem sealed_payload_bound {boundary : Boundary} (context : Seal boundary)
    (address : Fin (C3NativePrecision.stateBound boundary context.anchor)) : address.val*256<2^64 := by
  have bounded:=sealed_address_bound context
  have admitted:=address.isLt
  norm_num at bounded ⊢
  omega

end FlyCNS.C3NativeCodec
