import H0mework.Physics.LowEnergy.FullQuantum.HistoryPrepared.Source
import H0mework.Physics.LowEnergy.FullQuantum.HistoryGenerator.Domain

/-! The original fixed packet is used as a source. Its actual Dirac Green response generates a normalized field in the original generator domain. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen HistoryPrepared HistoryGenerator GaugeHistory
open ProofFreeRicherAnholonomicSource YangMills.FullPairing Stage9DEF
noncomputable section

def rawPacket (energy damping : ℝ) (positive : 0 < damping) : FullMatterL2 :=
  green 0 energy damping positive preparedPacket

theorem rawPacket_nonzero (energy damping : ℝ) (positive : 0 < damping) : rawPacket energy damping positive≠0 := by
  apply nonzero_response 0 energy damping positive preparedPacket
  intro zero
  have unit := preparedPacket_unit
  rw [zero,norm_zero] at unit
  norm_num at unit

def sourceFilter (energy damping : ℝ) (positive : 0 < damping) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) • green 0 energy damping positive

def filteredPacket (energy damping : ℝ) (positive : 0 < damping) : FullMatterL2 :=
  sourceFilter energy damping positive preparedPacket

theorem filteredPacket_unit (energy damping : ℝ) (positive : 0 < damping) :
    ‖filteredPacket energy damping positive‖=1 := by
  change ‖((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) • rawPacket energy damping positive‖=1
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (rawPacket_nonzero energy damping positive))

theorem filteredPacket_domain (energy damping : ℝ) (positive : 0 < damping) :
    filteredPacket energy damping positive ∈ Quantum.Generator.domain freeAction := by
  have raw := (generator_domain_iff_original energy damping positive _).mpr
    (green_domain 0 energy damping positive preparedPacket)
  exact (Quantum.Generator.domain freeAction).smul_mem
    ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) raw

def filteredMother (energy damping : ℝ) (positive : 0 < damping)
    (observable : FullMatterL2 →L[ℂ] FullMatterL2) : YangMills.FullPairing.Mother :=
  sourceMother ((sourceFilter energy damping positive).adjoint.comp
    (observable.comp (sourceFilter energy damping positive)))

theorem filtered_source_read (energy damping : ℝ) (positive : 0 < damping)
    (observable : FullMatterL2 →L[ℂ] FullMatterL2) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (filteredMother energy damping positive observable))=
        inner ℂ (filteredPacket energy damping positive) (observable (filteredPacket energy damping positive)) := by
  rw [filteredMother,sourceMother_read]
  change inner ℂ preparedPacket ((sourceFilter energy damping positive).adjoint
    (observable (sourceFilter energy damping positive preparedPacket)))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
