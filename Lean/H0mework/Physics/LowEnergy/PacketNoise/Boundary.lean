import H0mework.Physics.LowEnergy.PacketNoise.Chiral

set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen SpatialWeak HistoryGenerator GaugeHistory
open ProofFreeRicherAnholonomicSource YangMills.FullPairing
noncomputable section
attribute [local irreducible] chiral chiralContact

def boundaryAction : FullMatterL2 →L[ℂ] FullMatterL2 := chiral.compLpL 2 volume

theorem sourceField_boundary (point : BasePoint) (energy damping : ℝ) (field : FullMatterL2) :
    sourceField point energy damping (boundaryAction field) =ᵐ[volume]
      fun frequency => chiralContact point energy damping (fourier field frequency)-
        chiral (sourceField point energy damping field frequency) := by
  filter_upwards [chiral.coeFn_compLpL (fourier field)] with frequency image
  simp only [sourceField,boundaryAction,GaugeGreen.constant_fourier,image]
  change (symbol point energy damping frequency*chiral) (fourier field frequency)=_
  rw [symbol_chiral]
  rfl

theorem boundaryAction_domain (point : BasePoint) (energy damping : ℝ) (field : Domain point energy damping) :
    MemLp (sourceField point energy damping (boundaryAction field.val)) 2 volume := by
  have first := (chiralContact point energy damping).comp_memLp (fourier field.val)
  have second := chiral.comp_memLp' field.property
  exact (first.sub second).ae_eq (sourceField_boundary point energy damping field.val).symm

theorem boundary_generator_domain (energy damping : ℝ) (positive : 0 < damping)
    (field : Quantum.Generator.domain freeAction) :
    boundaryAction field.val ∈ Quantum.Generator.domain freeAction := by
  have original := (generator_domain_iff_original energy damping positive field.val).mp field.property
  exact (generator_domain_iff_original energy damping positive _).mpr
    (boundaryAction_domain 0 energy damping ⟨field.val,original⟩)

def boundaryDomain (field : Quantum.Generator.domain freeAction) : Quantum.Generator.domain freeAction :=
  ⟨boundaryAction field.val,boundary_generator_domain 0 1 (by norm_num) field⟩

def cosineDomain (shift : Position) (field : Quantum.Generator.domain freeAction) : Quantum.Generator.domain freeAction :=
  ⟨cosineShift shift field.val,by
    have original := (generator_domain_iff_original 0 1 (by norm_num) field.val).mp field.property
    exact (generator_domain_iff_original 0 1 (by norm_num) _).mpr
      (cosineShift_domain 0 1 (by norm_num) ⟨field.val,original⟩ shift)⟩

def preparedDomain (energy damping : ℝ) (positive : 0 < damping) : Quantum.Generator.domain freeAction :=
  ⟨filteredPacket energy damping positive,filteredPacket_domain energy damping positive⟩

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
