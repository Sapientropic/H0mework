import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.CurrentFamilies.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Restriction

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open MotherHandoffRestriction MotherHandoffSource MotherNativeCurrent
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

/-- All source and target currents use one sufficient rank. These inputs
occur only in coverage of the material-only current-family reader. -/
theorem current_family_at {rank : Ordinal.{0}} (I : Type) (N : I → WorldRelationNetwork.{0})
    (currents : (index : I) → SourceNativeLivingRootCurrentAt (N index))
    (events : (index : I) → EventFamily (currents index).root.source.base)
    (declarations : (index : I) → Declaration (currents index).root.source.base (events index))
    (lawSame : ∀ index, assembleLaw (declarations index) = (currents index).root.source.terminalHandoff)
    (indexCode : I ↪ MotherArenaHigher.Base rank)
    (rootCode : (Σ index, JointAddress (currents index).root.toAuthoritativeRoot
      (events index) (declarations index)) ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ indices : I ≃ MotherCurrentFamilies.Member material,
        Nonempty ((index : I) → Restriction rank (currents index)
          (MotherCurrentFamilies.atMember material (indices index))) := by
  have allCurrents : ∀ index : I, ∃ materials, CurrentFormationAt rank (currents index) materials := fun index =>
    current_at_rank (currents index) (events index) (declarations index) (lawSame index)
      ((Function.Embedding.sigmaMk index).trans rootCode)
  choose values formed using allCurrents
  obtain ⟨base, ⟨indexMap⟩⟩ := MotherAuthorityFamilies.every_index I indexCode
  obtain ⟨material, indices, recovered⟩ := MotherCurrentFamilies.every_material_family I base indexMap values
  refine ⟨material, indices, ⟨fun index => ?_⟩⟩
  have actualFormed : CurrentFormationAt rank (currents index)
      (MotherCurrentFamilies.atMember material (indices index)) := by
    rw [recovered]
    exact formed index
  exact Classical.choice actualFormed.restriction

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
