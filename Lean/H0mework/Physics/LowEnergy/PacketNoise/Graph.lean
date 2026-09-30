import H0mework.Physics.LowEnergy.PacketNoise.Hamiltonian

/-! A bounded field/load pair records a true original Dirac graph. Every current map below is generated from the original Green pair. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen HistoryGenerator GaugeHistory
noncomputable section
attribute [local irreducible] freeAction yukawaOperator inversePrincipal

structure SourceMap (energy damping : ℝ) where
  field : FullMatterL2 →L[ℂ] FullMatterL2
  load : FullMatterL2 →L[ℂ] FullMatterL2
  equation : ∀ input, Equation 0 energy damping (field input) (load input)

def SourceMap.domain {energy damping : ℝ} (map : SourceMap energy damping) (input : FullMatterL2) :
    SpatialGreen.Domain 0 energy damping :=
  ⟨map.field input,(Lp.memLp (fourier (map.load input))).ae_eq (map.equation input).symm⟩

def SourceMap.generator {energy damping : ℝ} (map : SourceMap energy damping) (positive : 0 < damping)
    (input : FullMatterL2) : Quantum.Generator.domain freeAction :=
  ⟨map.field input,(generator_domain_iff_original energy damping positive _).mpr (map.domain input).property⟩

theorem SourceMap.dirac_value {energy damping : ℝ} (map : SourceMap energy damping) (input : FullMatterL2) :
    dirac 0 energy damping (map.domain input)=map.load input := by
  apply fourier.injective
  apply Lp.ext
  exact (dirac_fourier_ae 0 energy damping (map.domain input)).trans (map.equation input)

def greenMap (energy damping : ℝ) (positive : 0 < damping) : SourceMap energy damping where
  field := green 0 energy damping positive
  load := 1
  equation input := green_solves 0 energy damping positive input

def SourceMap.hamiltonian {energy damping : ℝ} (map : SourceMap energy damping) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((energy : ℂ)+Complex.I*(damping : ℂ)) • map.field-
    Complex.I • (inversePrincipal 0).comp map.load

theorem SourceMap.hamiltonian_value {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (input : FullMatterL2) :
    sourceHamiltonian (map.generator positive input)=map.hamiltonian input := by
  have actual := source_hamiltonian_dirac energy damping positive (map.domain input)
  rw [map.dirac_value] at actual
  exact actual

def SourceMap.adjointHamiltonian {energy damping : ℝ} (map : SourceMap energy damping) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  map.hamiltonian+(yukawaOperator.adjoint-yukawaOperator).comp map.field

theorem SourceMap.adjoint_hamiltonian_value {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (input : FullMatterL2) :
    conjugateHamiltonian (map.generator positive input)=map.adjointHamiltonian input := by
  have actual := map.hamiltonian_value positive input
  change Quantum.Generator.hamiltonian freeAction (map.generator positive input)+yukawaOperator (map.field input)=
    map.hamiltonian input at actual
  change Quantum.Generator.hamiltonian freeAction (map.generator positive input)+yukawaOperator.adjoint (map.field input)=
    map.hamiltonian input+(yukawaOperator.adjoint (map.field input)-yukawaOperator (map.field input))
  have rearrange (first second third : FullMatterL2) :
      first+third=(first+second)+(third-second) := by abel
  exact (rearrange _ _ _).trans
    (congrArg (fun value => value+
      (yukawaOperator.adjoint (map.field input)-yukawaOperator (map.field input))) actual)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
