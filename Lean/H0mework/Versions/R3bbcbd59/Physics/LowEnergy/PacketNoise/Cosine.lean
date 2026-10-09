import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Domain
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Group
import H0mework.Versions.AB.Physics.LowEnergy.PacketNoise.Filtered

/-! The same continuum state admits a bounded self-adjoint cosine transfer which preserves the original Dirac domain. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen HistoryGenerator GaugeHistory
noncomputable section

def cosineShift (shift : Position) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (1/2 : ℂ) • ((phaseShift shift).toContinuousLinearMap+(phaseShift (-shift)).toContinuousLinearMap)

theorem cosineShift_selfAdjoint (shift : Position) : star (cosineShift shift)=cosineShift shift := by
  have first : star (phaseShift shift).toContinuousLinearMap=(phaseShift (-shift)).toContinuousLinearMap :=
    phaseShift_adjoint shift
  have second : star (phaseShift (-shift)).toContinuousLinearMap=(phaseShift shift).toContinuousLinearMap := by
    change (phaseShift (-shift)).toContinuousLinearMap.adjoint=(phaseShift shift).toContinuousLinearMap
    simpa only [neg_neg] using phaseShift_adjoint (-shift)
  rw [cosineShift,star_smul,star_add,first,second]
  norm_num
  rw [add_comm]

theorem cosineShift_norm (shift : Position) : ‖cosineShift shift‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro field
  have bound : ‖phaseShift shift field+phaseShift (-shift) field‖ ≤ 2*‖field‖ := by
    calc
      _ ≤ ‖phaseShift shift field‖+‖phaseShift (-shift) field‖ := norm_add_le _ _
      _ = _ := by rw [phaseShift_norm,phaseShift_norm]; ring
  change ‖(1/2 : ℂ) • (phaseShift shift field+phaseShift (-shift) field)‖ ≤ 1*‖field‖
  rw [norm_smul]
  norm_num
  linarith

theorem cosineShift_domain (energy damping : ℝ) (positive : 0 < damping)
    (field : Domain 0 energy damping) (shift : Position) :
    MemLp (sourceField 0 energy damping (cosineShift shift field.val)) 2 volume := by
  have first := (generator_domain_iff_original energy damping positive _).mpr
    (phaseShift_domain 0 energy damping field shift)
  have second := (generator_domain_iff_original energy damping positive _).mpr
    (phaseShift_domain 0 energy damping field (-shift))
  exact (generator_domain_iff_original energy damping positive _).mp
    ((Quantum.Generator.domain freeAction).smul_mem (1/2 : ℂ)
      ((Quantum.Generator.domain freeAction).add_mem first second))

theorem filtered_cosine_domain (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    cosineShift shift (filteredPacket energy damping positive) ∈ Quantum.Generator.domain freeAction := by
  have packet := (generator_domain_iff_original energy damping positive _).mp
    (filteredPacket_domain energy damping positive)
  exact (generator_domain_iff_original energy damping positive _).mpr
    (cosineShift_domain energy damping positive ⟨_,packet⟩ shift)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
