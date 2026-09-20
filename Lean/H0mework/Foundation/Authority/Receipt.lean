import Mathlib.Data.Set.Basic

/-!
# Canonical receipt authority

Evidence authority is the image of an actual event under a designated
compiler.  A receipt-shaped type being indexed, proof relevant, or inhabited
does not by itself make one of its values authoritative.

This kernel deliberately says nothing about how the compiler is obtained.
A source-local compiler may be designated without a higher authority; its
receipts are authoritative only relative to that exact event source and
compiler.  Cross-source lifecycle use is governed separately by source-anchor
conservation, while concrete effective-process compilation is installed by a
shared lower constructor rather than a thin recognition record.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace CanonicalReceiptAuthority

universe u v

/-- A designated compiler from actual source events to receipts.  Event and
receipt carriers may live in different universes; authority is the exact image
equation, not a same-universe encoding accident. -/
structure Compiler (ActualEvent : Type u) (Receipt : Type v) where
  compile : ActualEvent → Receipt

/-- A receipt is canonical exactly when it is the compiled image of an exact
actual event.  The event and the on-the-nose compilation equation remain
available to every consumer. -/
structure CanonicalReceipt
    {ActualEvent : Type u} {Receipt : Type v}
    (compiler : Compiler ActualEvent Receipt) (receipt : Receipt) :
    Type (max u v) where
  actualEvent : ActualEvent
  compile_eq : compiler.compile actualEvent = receipt

/-- The designated compiler emits a receipt authoritative in its own source
and compiler context. -/
def Compiler.compileCanonical
    {ActualEvent : Type u} {Receipt : Type v}
    (compiler : Compiler ActualEvent Receipt) (actualEvent : ActualEvent) :
    CanonicalReceipt compiler (compiler.compile actualEvent) :=
  ⟨actualEvent, rfl⟩

/-- Forward half of the canonical receipt law. -/
theorem Compiler.compile_mem_range
    {ActualEvent : Type u} {Receipt : Type v}
    (compiler : Compiler ActualEvent Receipt) (actualEvent : ActualEvent) :
    compiler.compile actualEvent ∈ Set.range compiler.compile :=
  ⟨actualEvent, rfl⟩

/-- No-Free Evidence / Canonical Receipt Law:
authoritative receipts are exactly the image of the shared compiler. -/
theorem canonicalReceipt_iff_mem_range
    {ActualEvent : Type u} {Receipt : Type v}
    (compiler : Compiler ActualEvent Receipt) (receipt : Receipt) :
    Nonempty (CanonicalReceipt compiler receipt) ↔
      receipt ∈ Set.range compiler.compile := by
  constructor
  · rintro ⟨canonical⟩
    exact ⟨canonical.actualEvent, canonical.compile_eq⟩
  · rintro ⟨actualEvent, compile_eq⟩
    exact ⟨⟨actualEvent, compile_eq⟩⟩

/-- Converse half: every authoritative receipt exposes the exact actual event
and the exact compiler equation which generated it. -/
theorem CanonicalReceipt.exists_exactActualEvent
    {ActualEvent : Type u} {Receipt : Type v}
    {compiler : Compiler ActualEvent Receipt} {receipt : Receipt}
    (canonical : CanonicalReceipt compiler receipt) :
    ∃ actualEvent : ActualEvent,
      compiler.compile actualEvent = receipt :=
  ⟨canonical.actualEvent, canonical.compile_eq⟩

/-- Inhabitation of a raw receipt carrier cannot create authority when there
is no actual event to compile. -/
instance canonicalReceiptIsEmptyOfActualEventIsEmpty
    {ActualEvent : Type u} {Receipt : Type v} [IsEmpty ActualEvent]
    (compiler : Compiler ActualEvent Receipt) (receipt : Receipt) :
    IsEmpty (CanonicalReceipt compiler receipt) where
  false canonical := isEmptyElim canonical.actualEvent

theorem no_canonicalReceipt_of_no_actualEvent
    {ActualEvent : Type u} {Receipt : Type v} [IsEmpty ActualEvent]
    (compiler : Compiler ActualEvent Receipt) (receipt : Receipt) :
    ¬ Nonempty (CanonicalReceipt compiler receipt) := by
  exact not_nonempty_iff.mpr inferInstance

end CanonicalReceiptAuthority
end SaturationMonoid
