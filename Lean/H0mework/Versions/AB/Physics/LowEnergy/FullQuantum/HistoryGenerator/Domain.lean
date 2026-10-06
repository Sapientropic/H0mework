import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryGenerator.Resolvent

/-! The actual free-generator domain is exactly the original maximal Fourier Dirac domain. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGenerator
open FullSpace GaugeGreen GaugeHistory HistoryGreen
noncomputable section
attribute [local irreducible] fullG HistoryLaplace.value

theorem zero_fields_fullG (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    fullG 0 energy damping positive 0 0 0 source=Complex.I • freeR 0 energy damping positive (inversePrincipal 0 source) := by
  have generated := free_history_integral energy damping positive (inversePrincipal 0 source)
  rw [stationary_diracValue_original 0 0 0 energy damping positive source] at generated
  exact generated

theorem freeR_originalG (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    freeR 0 energy damping positive source=fullG 0 energy damping positive 0 0 0 (-Complex.I • principal 0 source) := by
  rw [zero_fields_fullG,map_smul,inversePrincipal_left,map_smul,smul_smul]
  simp

theorem original_domain_resolvent (energy damping : ℝ) (positive : 0<damping)
    (field : SpatialGreen.Domain 0 energy damping) :
    field.val=freeR 0 energy damping positive
      (Complex.I • inversePrincipal 0 (originalKernel 0 energy damping 0 0 0 field)) := by
  have generated := (fullG_originalKernel 0 energy damping positive 0 0 0 field).symm
  rw [zero_fields_fullG,← map_smul] at generated
  exact generated

theorem generator_domain_iff_original (energy damping : ℝ) (positive : 0<damping) (field : FullMatterL2) :
    field ∈ Quantum.Generator.domain freeAction ↔
      MemLp (SpatialGreen.sourceField 0 energy damping field) 2 volume := by
  constructor
  · intro member
    have generated := generator_resolvent_recovers energy damping positive ⟨field,member⟩
    change field=_ at generated
    rw [generated,freeR_originalG]
    exact fullG_domain 0 energy damping positive 0 0 0 _
  · intro admissible
    have generated := original_domain_resolvent energy damping positive ⟨field,admissible⟩
    change field=_ at generated
    rw [generated]
    exact freeR_generator_domain energy damping positive _

theorem original_generator_value (energy damping : ℝ) (positive : 0<damping)
    (field : SpatialGreen.Domain 0 energy damping) :
    Quantum.Generator.hamiltonian freeAction
      ⟨field.val,(generator_domain_iff_original energy damping positive field.val).mpr field.property⟩=
      ((energy : ℂ)+Complex.I*(damping : ℂ)) • field.val-
        Complex.I • inversePrincipal 0 (originalKernel 0 energy damping 0 0 0 field) := by
  let source := Complex.I • inversePrincipal 0 (originalKernel 0 energy damping 0 0 0 field)
  have represented : field.val=freeR 0 energy damping positive source :=
    original_domain_resolvent energy damping positive field
  calc
    _ = Quantum.Generator.hamiltonian freeAction
        ⟨freeR 0 energy damping positive source,freeR_generator_domain energy damping positive source⟩ :=
      congrArg (Quantum.Generator.hamiltonian freeAction) (Subtype.ext represented)
    _ = ((energy : ℂ)+Complex.I*(damping : ℂ)) • freeR 0 energy damping positive source-source :=
      freeR_generator_value energy damping positive source
    _ = _ := by rw [← represented]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGenerator
