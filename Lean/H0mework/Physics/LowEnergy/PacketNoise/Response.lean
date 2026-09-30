import H0mework.Physics.LowEnergy.PacketNoise.Bounded
import H0mework.Physics.LowEnergy.PacketNoise.Current

/-! The bounded Green composites agree with the actual unbounded current on every source response. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen GaugeHistory
noncomputable section
attribute [local irreducible] freeAction

theorem SourceMap.current_original {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (transfer : Position) (input : FullMatterL2) :
    map.current transfer input=currentField transfer (map.generator positive input) := by
  rw [map.current_value positive,currentField_apply]
  have same : (map.boundary.cosine transfer).generator positive input=
      cosineDomain transfer (boundaryDomain (map.generator positive input)) := Subtype.ext rfl
  rw [same]

def responseDomain (energy damping : ℝ) (positive : 0 < damping) (input : FullMatterL2) :
    Quantum.Generator.domain freeAction :=
  ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) •
    (greenMap energy damping positive).generator positive input

theorem responseDomain_value (energy damping : ℝ) (positive : 0 < damping) (input : FullMatterL2) :
    (responseDomain energy damping positive input).val=sourceFilter energy damping positive input := rfl

theorem currentFilter_original (energy damping : ℝ) (positive : 0 < damping)
    (transfer : Position) (input : FullMatterL2) :
    currentFilter energy damping positive transfer input=
      currentField transfer (responseDomain energy damping positive input) := by
  change ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) •
    (greenMap energy damping positive).current transfer input=_
  rw [(greenMap energy damping positive).current_original positive]
  exact (currentField_smul transfer _ _).symm

theorem currentFilter_prepared (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    currentFilter energy damping positive transfer HistoryPrepared.preparedPacket=
      currentField transfer (preparedDomain energy damping positive) := by
  rw [currentFilter_original]
  congr 1

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
