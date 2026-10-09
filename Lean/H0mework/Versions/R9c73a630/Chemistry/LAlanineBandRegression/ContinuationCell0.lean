import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Full
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.FieldsAll
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.ContinuationFull

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandContinuation

open WholeBandActual
noncomputable section

theorem cell0_source_fields : ∀ d, DirectionFields 0 d := WholeBandCell0Fields.all_actual_fields

theorem cell0_fullflow_recovered (p : Cell0Point) :
    type_of% (WholeBandCell0Continuation.cell0_full_starts p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_original p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_sourceCube p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_tubes p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_fields p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_field_cover p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_endpoints p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_next_initial p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_actual_caps p) ∧
    type_of% (WholeBandCell0Continuation.cell0_full_agrees_with_first p) :=
  ⟨full_starts 0 p.val, full_original 0 cell0_source_fields p.val p.property,
    full_sourceCube 0 cell0_source_fields p.val p.property,
    full_tubes 0 cell0_source_fields p.val p.property, full_fields 0 cell0_source_fields p.val p.property,
    full_field_cover 0 cell0_source_fields p.val p.property, full_endpoints 0 cell0_source_fields p.val p.property,
    full_next_initial 0 cell0_source_fields p.val p.property, full_actual_caps 0 cell0_source_fields p.val p.property,
    WholeBandActual.fullFlow_eq_sourceRaw p⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandContinuation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
