import H0mework.Physics.LowEnergy.PacketDynamics.Current

/-! Plane-wave transfer preserves the original common domain and its adjoint
is the opposite transfer on the same continuum carrier. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace SpatialGreen HistoryGenerator GaugeHistory PacketNoise PacketDynamics
noncomputable section
attribute [local irreducible] freeAction

theorem phase_generator_domain (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    phaseShift transfer field.val ∈ Quantum.Generator.domain freeAction := by
  have original := (generator_domain_iff_original 0 1 zero_lt_one field.val).mp field.property
  exact (generator_domain_iff_original 0 1 zero_lt_one _).mpr
    (phaseShift_domain 0 0 1 ⟨field.val,original⟩ transfer)

def phaseDomain (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    Quantum.Generator.domain freeAction :=
  ⟨phaseShift transfer field.val,phase_generator_domain transfer field⟩

theorem phaseDomain_value (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    (phaseDomain transfer field).val=phaseShift transfer field.val := rfl

def phaseDomainLinear (transfer : Position) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] Quantum.Generator.domain freeAction where
  toFun := phaseDomain transfer
  map_add' left right := Subtype.ext (map_add (phaseShift transfer) left.val right.val)
  map_smul' scale field := Subtype.ext (map_smul (phaseShift transfer) scale field.val)

theorem phaseDomainLinear_apply (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    phaseDomainLinear transfer field=phaseDomain transfer field := rfl

theorem phaseDomain_zero (field : Quantum.Generator.domain freeAction) : phaseDomain 0 field=field :=
  Subtype.ext (phaseShift_zero field.val)

theorem cosineDomain_phases (transfer : Position) (field : Quantum.Generator.domain freeAction) :
    cosineDomain transfer field=(1/2 : ℂ) • (phaseDomain transfer field+phaseDomain (-transfer) field) :=
  Subtype.ext rfl

theorem phase_pair (transfer : Position) (left right : FullMatterL2) :
    inner ℂ (phaseShift transfer left) right=inner ℂ left (phaseShift (-transfer) right) := by
  have original := ContinuousLinearMap.adjoint_inner_right
    (phaseShift transfer).toContinuousLinearMap left right
  rw [phaseShift_adjoint] at original
  exact original.symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
