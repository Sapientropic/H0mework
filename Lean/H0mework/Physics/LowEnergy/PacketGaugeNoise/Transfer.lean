import H0mework.Physics.LowEnergy.PacketGaugeNoise.Profiles

/-! A real primitive cosine field produces both actual Fourier transfers in
the same unchanged packet. No orthogonality of transfers is used. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
open FullQuantum FullSpace PacketNoise GaugeGreen StageNineP286GaugeConnectionVariation
noncomputable section
attribute [local irreducible] GaugeGreen.gaugePotential boundaryAction phaseShift

theorem phase_cosine (shift probe : Position) (field : FullMatterL2) :
    phaseShift shift (cosineShift probe field)=(1/2 : ℂ) •
      (phaseShift (shift+probe) field+phaseShift (shift-probe) field) := by
  change phaseShift shift ((1/2 : ℂ) • (phaseShift probe field+phaseShift (-probe) field))=_
  rw [map_smul,map_add,phaseShift_add,phaseShift_add,sub_eq_add_neg]

theorem cosine_phase (probe shift : Position) (field : FullMatterL2) :
    cosineShift probe (phaseShift shift field)=(1/2 : ℂ) •
      (phaseShift (shift+probe) field+phaseShift (shift-probe) field) := by
  change (1/2 : ℂ) •
    (phaseShift probe (phaseShift shift field)+phaseShift (-probe) (phaseShift shift field))=_
  rw [phaseShift_add,phaseShift_add,add_comm probe shift,add_comm (-probe) shift,sub_eq_add_neg]

theorem currentVariation_cosine (gauge : P286GaugeOneForm) (probe shift : Position)
    (field : FullMatterL2) :
    currentVariation (cosineProfile gauge probe) shift field=(1/2 : ℂ) •
      (currentVariation (constantProfile gauge) (shift+probe) field+
        currentVariation (constantProfile gauge) (shift-probe) field) := by
  have real (profile : GaugeProfile) :
      (GaugeGreen.gaugePotential profile).adjoint=GaugeGreen.gaugePotential profile :=
    gaugePotential_selfAdjoint profile
  simp only [currentVariation_apply,real,cosinePotential,gaugePotential_phase]
  rw [phase_cosine,phase_cosine]
  simp only [map_smul,map_add]
  module

theorem selected_cosine (probe shift : Position) (field : FullMatterL2) :
    currentVariation (cosineProfile LightInteraction.sourceGaugeOneForm probe) shift field=
      (1/2 : ℂ) • (currentVariation selectedProfile (shift+probe) field+
        currentVariation selectedProfile (shift-probe) field) :=
  currentVariation_cosine LightInteraction.sourceGaugeOneForm probe shift field

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketGaugeNoise
