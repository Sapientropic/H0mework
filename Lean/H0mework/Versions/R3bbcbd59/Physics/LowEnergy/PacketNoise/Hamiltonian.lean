import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Boundary

/-! The whole source Hamiltonian and its formal adjoint share the already generated domain; the one-way Yukawa term is retained as a bounded operator. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen HistoryGenerator GaugeHistory GaugeGreen
noncomputable section
attribute [local irreducible] freeAction backgroundY chiral

def yukawaOperator : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (-Complex.I) • (inversePrincipal 0).comp (backgroundY 0)

def sourceHamiltonian (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  Quantum.Generator.hamiltonian freeAction field+yukawaOperator field.val

def conjugateHamiltonian (field : Quantum.Generator.domain freeAction) : FullMatterL2 :=
  Quantum.Generator.hamiltonian freeAction field+yukawaOperator.adjoint field.val

theorem sourceHamiltonian_pair (left right : Quantum.Generator.domain freeAction) :
    inner ℂ (sourceHamiltonian left) right.val=inner ℂ left.val (conjugateHamiltonian right) := by
  rw [sourceHamiltonian,conjugateHamiltonian,inner_add_left,inner_add_right,
    Quantum.Generator.hamiltonian_symmetric freeAction left right,
    ContinuousLinearMap.adjoint_inner_right]

theorem source_hamiltonian_dirac (energy damping : ℝ) (positive : 0 < damping)
    (field : SpatialGreen.Domain 0 energy damping) :
    sourceHamiltonian ⟨field.val,(generator_domain_iff_original energy damping positive field.val).mpr field.property⟩=
      ((energy : ℂ)+Complex.I*(damping : ℂ)) • field.val-
        Complex.I • inversePrincipal 0 (dirac 0 energy damping field) := by
  rw [sourceHamiltonian,original_generator_value energy damping positive field]
  have kernel : originalKernel 0 energy damping 0 0 0 field=
      dirac 0 energy damping field-backgroundY 0 field.val := by
    simp only [originalKernel,Complex.ofReal_zero,zero_smul,add_zero,
      ScalarGreen.potential,ScalarGreen.matrixField,map_zero,zero_apply,sub_eq_add_neg,zero_add]
  rw [kernel]
  change ((energy : ℂ)+Complex.I*(damping : ℂ)) • field.val-
      Complex.I • inversePrincipal 0 (dirac 0 energy damping field-backgroundY 0 field.val)+
      (-Complex.I) • inversePrincipal 0 (backgroundY 0 field.val)=_
  rw [map_sub,smul_sub,neg_smul]
  abel

theorem boundaryAction_symmetric (left right : FullMatterL2) :
    inner ℂ (boundaryAction left) right=inner ℂ left (boundaryAction right) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [chiral.coeFn_compLpL left,chiral.coeFn_compLpL right] with x leftAt rightAt
  change inner ℂ (boundaryAction left x) (right x)=inner ℂ (left x) (boundaryAction right x)
  change boundaryAction left x=chiral (left x) at leftAt
  change boundaryAction right x=chiral (right x) at rightAt
  rw [leftAt,rightAt]
  have self : chiral.adjoint=chiral := chiral_selfAdjoint
  simpa only [self] using ContinuousLinearMap.adjoint_inner_left chiral (right x) (left x)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
