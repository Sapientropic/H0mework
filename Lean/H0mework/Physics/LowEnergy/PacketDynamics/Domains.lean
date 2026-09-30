import H0mework.Physics.LowEnergy.PacketDynamics.Flow
import H0mework.Physics.LowEnergy.PacketDynamics.AdjointGraph

/-! The original Dirac inverse recovers every generator-domain field. Its two
actual graph transports therefore preserve the whole common Hamiltonian domain. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen PacketNoise HistoryGenerator GaugeHistory
noncomputable section
attribute [local irreducible] freeAction

private def originalDomain (field : Quantum.Generator.domain freeAction) : SpatialGreen.Domain 0 0 1 :=
  ⟨field.val,(generator_domain_iff_original 0 1 zero_lt_one field.val).mp field.property⟩

private def originalLoad (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  dirac 0 0 1 (originalDomain field)

private theorem original_recovered (field : Quantum.Generator.domain freeAction) :
    green 0 0 1 zero_lt_one (originalLoad field)=field.val :=
  green_dirac 0 0 1 zero_lt_one (originalDomain field)

theorem flow_generator_domain (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    spatialFlow 0 time field.val ∈ Quantum.Generator.domain freeAction := by
  have generated := ((evolve (greenMap 0 1 zero_lt_one) time).generator
    zero_lt_one (originalLoad field)).property
  change spatialFlow 0 time (green 0 0 1 zero_lt_one (originalLoad field)) ∈
    Quantum.Generator.domain freeAction at generated
  rwa [original_recovered] at generated

theorem adjoint_generator_domain (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    adjointFlow time field.val ∈ Quantum.Generator.domain freeAction := by
  have generated := ((adjointEvolve (greenMap 0 1 zero_lt_one) time).generator
    zero_lt_one (originalLoad field)).property
  change adjointFlow time (green 0 0 1 zero_lt_one (originalLoad field)) ∈
    Quantum.Generator.domain freeAction at generated
  rwa [original_recovered] at generated

def flowDomain (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    Quantum.Generator.domain freeAction :=
  ⟨spatialFlow 0 time field.val,flow_generator_domain time field⟩

def adjointDomain (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    Quantum.Generator.domain freeAction :=
  ⟨adjointFlow time field.val,adjoint_generator_domain time field⟩

theorem flowDomain_value (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    (flowDomain time field).val=spatialFlow 0 time field.val := rfl

theorem adjointDomain_value (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    (adjointDomain time field).val=adjointFlow time field.val := rfl

def flowDomainLinear (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] Quantum.Generator.domain freeAction where
  toFun := flowDomain time
  map_add' left right := Subtype.ext (map_add (spatialFlow 0 time) left.val right.val)
  map_smul' scale field := Subtype.ext (map_smul (spatialFlow 0 time) scale field.val)

def adjointDomainLinear (time : ℝ) :
    Quantum.Generator.domain freeAction →ₗ[ℂ] Quantum.Generator.domain freeAction where
  toFun := adjointDomain time
  map_add' left right := Subtype.ext (map_add (adjointFlow time) left.val right.val)
  map_smul' scale field := Subtype.ext (map_smul (adjointFlow time) scale field.val)

theorem flowDomainLinear_apply (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    flowDomainLinear time field=flowDomain time field := rfl

theorem adjointDomainLinear_apply (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    adjointDomainLinear time field=adjointDomain time field := rfl

theorem adjointFlow_zero (field : FullMatterL2) : adjointFlow 0 field=field := by
  have original : spatialFlow 0 0=(1 : FullMatterL2 →L[ℂ] FullMatterL2) := by
    apply ContinuousLinearMap.ext
    intro initial
    exact spatialFlow_zero 0 initial
  rw [adjointFlow_original,original,ContinuousLinearMap.adjoint_one]
  rfl

theorem flowDomain_zero (field : Quantum.Generator.domain freeAction) : flowDomain 0 field=field :=
  Subtype.ext (spatialFlow_zero 0 field.val)

theorem adjointDomain_zero (field : Quantum.Generator.domain freeAction) : adjointDomain 0 field=field :=
  Subtype.ext (adjointFlow_zero field.val)

theorem flowDomain_hamiltonian (time : ℝ) (field : Quantum.Generator.domain freeAction) :
    sourceHamiltonian (flowDomain time field)=spatialFlow 0 time (sourceHamiltonian field) := by
  have before : (greenMap 0 1 zero_lt_one).generator zero_lt_one (originalLoad field)=field :=
    Subtype.ext (original_recovered field)
  have after : (evolve (greenMap 0 1 zero_lt_one) time).generator zero_lt_one (originalLoad field)=
      flowDomain time field :=
    Subtype.ext (congrArg (spatialFlow 0 time) (original_recovered field))
  rw [← after,evolve_hamiltonian,before]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
