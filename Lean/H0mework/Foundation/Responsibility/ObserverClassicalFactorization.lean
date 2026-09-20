import H0mework.Foundation.Responsibility.Observer
import Mathlib.Data.Set.Image

/-!
# Classical observer factorization adapter

This adapter chooses a representative of an observer image only after
`ConsumerSafe` has constructively proved that every representative yields the
same disposition.  The choice is a readout convenience and is deliberately
absent from the constructive authority core.
-/

set_option autoImplicit false

universe u v w

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace ConsumerSafe

/-- A certified-safe observer admits a classical factorization on its image.
This is a presentation readout, not an authority producer. -/
noncomputable def factorOnImage
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition}
    (_safe : ConsumerSafe observe consumer) : Set.range observe → Disposition :=
  fun observed => consumer (Classical.choose observed.property)

theorem factorOnImage_apply
    {State : Type u} {Observation : Type v} {Disposition : Type w}
    {observe : State → Observation} {consumer : State → Disposition}
    (safe : ConsumerSafe observe consumer) (state : State) :
    safe.factorOnImage ⟨observe state, ⟨state, rfl⟩⟩ = consumer state := by
  unfold factorOnImage
  apply safe
  exact Classical.choose_spec (show observe state ∈ Set.range observe from ⟨state, rfl⟩)

end ConsumerSafe
end ResponsibilityLifecycle
end SaturationMonoid
