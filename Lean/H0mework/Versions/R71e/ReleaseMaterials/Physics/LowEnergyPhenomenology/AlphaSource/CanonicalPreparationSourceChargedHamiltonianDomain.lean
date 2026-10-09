import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedQuantumPrice
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.PacketNoise.Hamiltonian

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedHamiltonianRead
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace SpatialGreen HistoryPrepared HistoryGenerator GaugeHistory
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open MeasureTheory Filter
open scoped InnerProductSpace Topology

def sourceChargedDiracDomain (side edge : Fin 2) : SpatialGreen.Domain 0 0 1 :=
  ⟨sourceChargedFilteredPacket side edge,
    (generator_domain_iff_original 0 1 (by norm_num) _).mp (sourceChargedFilteredPacket_domain side edge)⟩

/-- The same exact Dirac equation returns the source packet and its generated normalization. -/
theorem sourceChargedDirac_response (side edge : Fin 2) :
    dirac 0 0 1 (sourceChargedDiracDomain side edge)=
      ((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedSpatialPacket side edge := by
  apply green_injective 0 0 1 (by norm_num)
  rw [green_dirac]
  change ((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) •
      green 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)=_
  exact (map_smul _ _ _).symm

def sourceChargedGeneratorDomain (side edge : Fin 2) : Quantum.Generator.domain freeAction :=
  ⟨sourceChargedFilteredPacket side edge,sourceChargedFilteredPacket_domain side edge⟩

def sourceChargedHamiltonianVector (side edge : Fin 2) : FullMatterL2 :=
  PacketNoise.sourceHamiltonian (sourceChargedGeneratorDomain side edge)

/-- Original full Hamiltonian response, including its one-way Yukawa term and original C0 inverse. -/
theorem sourceChargedHamiltonian_response (side edge : Fin 2) :
    sourceChargedHamiltonianVector side edge=
      Complex.I • sourceChargedFilteredPacket side edge-
        Complex.I • inversePrincipal 0
          (((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedSpatialPacket side edge) := by
  change PacketNoise.sourceHamiltonian
    ⟨(sourceChargedDiracDomain side edge).val,
      (generator_domain_iff_original 0 1 (by norm_num) _).mpr (sourceChargedDiracDomain side edge).property⟩=_
  rw [PacketNoise.source_hamiltonian_dirac 0 1 (by norm_num),sourceChargedDirac_response]
  simp only [Complex.ofReal_zero,Complex.ofReal_one,mul_one,zero_add,sourceChargedDiracDomain]

def sourceChargedHamiltonianPrice (side edge : Fin 2) : ℝ :=
  1+‖inversePrincipal 0‖/‖sourceChargedRawPacket side edge‖

/-- The actual source Dirac equation pays the complete Hamiltonian norm without self-adjointness of the full H. -/
theorem sourceChargedHamiltonian_bound (side edge : Fin 2) :
    ‖sourceChargedHamiltonianVector side edge‖≤ sourceChargedHamiltonianPrice side edge := by
  rw [sourceChargedHamiltonian_response]
  calc
    _≤‖Complex.I • sourceChargedFilteredPacket side edge‖+
        ‖Complex.I • inversePrincipal 0
          (((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedSpatialPacket side edge)‖ := norm_sub_le _ _
    _=1+‖inversePrincipal 0
        (((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedSpatialPacket side edge)‖ := by
      rw [norm_smul,norm_smul,Complex.norm_I,one_mul,one_mul,sourceChargedFilteredPacket_unit]
    _≤1+‖inversePrincipal 0‖*
        ‖((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedSpatialPacket side edge‖ :=
      add_le_add le_rfl ((inversePrincipal 0).le_opNorm _)
    _=sourceChargedHamiltonianPrice side edge := by
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        sourceChargedSpatialPacket_unit,mul_one]
      rfl

def sourceChargedEnergyPair (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  inner ℂ (sourceChargedFilteredPacket sideL edgeL) (sourceChargedHamiltonianVector sideR edgeR)

theorem sourceChargedEnergyPair_bound (sideL edgeL sideR edgeR : Fin 2) :
    ‖sourceChargedEnergyPair sideL edgeL sideR edgeR‖≤ sourceChargedHamiltonianPrice sideR edgeR := by
  unfold sourceChargedEnergyPair
  exact (norm_inner_le_norm _ _).trans (by
    rw [sourceChargedFilteredPacket_unit,one_mul]
    exact sourceChargedHamiltonian_bound sideR edgeR)

end LowEnergy.PreparationPhysicalChargedHamiltonianRead
