import H0mework.Versions.AB.Physics.MotherSource.CanonicalMatter.Dual

/-! The original canonical dual fixes every external source vertex at once.
This is a readout of the existing prepared source, independent of which field
variation produced the vertex. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.ExternalState
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction Stage9C.Material.SpinPair
open Stage10.CanonicalMatter YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

/-- Use the same action-normalized dual for all vertices, including the
non-gauge entries of the original field source. -/
theorem original_prepared_vertex (point : BasePoint) (left right vertex : Mother) :
    actual.conjugateMatter point
      (canonicalDual left (vertex (right (actual.matter point)))) =
      4 * (spinScale : ℂ) * inner ℂ
        (operator left (prepared point))
        (operator (phaseInverse.comp (vertex.comp right)) (prepared point)) := by
  have paired (matter : DiracExteriorMatterCarrier) :
      canonicalDual left (vertex (right matter)) =
        pairedMother left (phaseInverse.comp (vertex.comp right)) matter := by
    simp [canonicalDual, pairedMother, fromOperator, operator]
  rw [paired, dual_gram]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.ExternalState
