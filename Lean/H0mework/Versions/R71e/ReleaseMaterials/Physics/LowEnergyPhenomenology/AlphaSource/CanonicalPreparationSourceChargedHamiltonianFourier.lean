import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedHamiltonianDomain

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedHamiltonianRead
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open FullQuantum FullSpace SpatialGreen HistoryPrepared HistoryGenerator GaugeHistory
open YangMills.FullPairing StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open MeasureTheory Filter
open scoped InnerProductSpace Topology

private theorem sourceHamiltonian_dirac_fiber (p : Fin 3→ℝ) (v : Hilbert) :
    Complex.I • v-Complex.I • operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0))
      (operator (Triangular.diracKernel actual 0 p Complex.I) v)=
      operator (FullQuantum.hamiltonian actual 0 p) v := by
  obtain ⟨u,rfl⟩:=naturalCoordinates.surjective v
  rw [Triangular.diracKernel_factor actual 0 p Complex.I (actual_noncharacteristic 0)]
  simp only [operator_coordinates,LinearMap.smul_apply,Module.End.mul_apply,
    Triangular.fullKernel,LinearMap.sub_apply,Module.End.one_apply,map_smul,
    currentCoframeMatterTemporalPrincipalInverse_left _ (actual_noncharacteristic 0)]
  simp only [map_sub,map_smul,smul_sub,smul_smul,Complex.I_mul_I,neg_mul,neg_neg,one_smul,neg_smul]
  simp only [smul_neg,smul_smul,Complex.I_mul_I,neg_one_smul,neg_neg]
  abel

/-- The original full Hamiltonian acts at every physical momentum 2πξ on the actual Fourier packet. -/
theorem sourceChargedHamiltonian_fourier (side edge : Fin 2) :
    fourier (sourceChargedHamiltonianVector side edge)=ᵐ[volume]
      fun frequency=>operator (FullQuantum.hamiltonian actual 0 (physicalMomentum frequency))
        (fourier (sourceChargedFilteredPacket side edge) frequency) := by
  let chi : FullMatterL2:=((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) • sourceChargedSpatialPacket side edge
  let L:=operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0))
  let u:=fourier (sourceChargedFilteredPacket side edge)
  let v:=L.compLpL 2 volume (fourier chi)
  have inverseFourier : fourier (inversePrincipal 0 chi)=v := GaugeGreen.constant_fourier L chi
  have equation:=dirac_fourier_ae 0 0 1 (sourceChargedDiracDomain side edge)
  rw [sourceChargedDirac_response] at equation
  rw [sourceChargedHamiltonian_response,map_sub,map_smul,map_smul,inverseFourier]
  filter_upwards [Lp.coeFn_sub (Complex.I • u) (Complex.I • v),Lp.coeFn_smul Complex.I u,
    Lp.coeFn_smul Complex.I v,L.coeFn_compLpL (fourier chi),equation] with frequency subAt leftAt rightAt inverseAt sourceAt
  change (Complex.I • u-Complex.I • v) frequency=_
  rw [subAt]
  simp only [Pi.sub_apply]
  rw [leftAt,rightAt]
  change Complex.I • u frequency-Complex.I • v frequency=_
  change v frequency=L (fourier chi frequency) at inverseAt
  change fourier chi frequency=SpatialGreen.symbol 0 0 1 frequency (u frequency) at sourceAt
  simp only [SpatialGreen.symbol,Retarded.spectralParameter,Complex.ofReal_zero,Complex.ofReal_one,
    mul_one,zero_add] at sourceAt
  rw [inverseAt,sourceAt]
  exact sourceHamiltonian_dirac_fiber (physicalMomentum frequency) (u frequency)

theorem sourceChargedEnergyPair_fourier_integrable (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (fun frequency : Position=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (operator (FullQuantum.hamiltonian actual 0 (physicalMomentum frequency))
        (fourier (sourceChargedFilteredPacket sideR edgeR) frequency))) := by
  apply (L2.integrable_inner (𝕜:=ℂ) (fourier (sourceChargedFilteredPacket sideL edgeL))
    (fourier (sourceChargedHamiltonianVector sideR edgeR))).congr
  filter_upwards [sourceChargedHamiltonian_fourier sideR edgeR] with frequency generated
  rw [generated]

/-- Both independent physical source legs consume the complete Fourier multiplier, with the original measure. -/
theorem sourceChargedEnergyPair_fourier (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedEnergyPair sideL edgeL sideR edgeR=
      ∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
        (operator (FullQuantum.hamiltonian actual 0 (physicalMomentum frequency))
          (fourier (sourceChargedFilteredPacket sideR edgeR) frequency)) := by
  unfold sourceChargedEnergyPair
  rw [←fourier.inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceChargedHamiltonian_fourier sideR edgeR] with frequency generated
  rw [generated]

theorem sourceChargedEnergyPair_fourier_bound (sideL edgeL sideR edgeR : Fin 2) :
    ‖∫frequency : Position,inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (operator (FullQuantum.hamiltonian actual 0 (physicalMomentum frequency))
        (fourier (sourceChargedFilteredPacket sideR edgeR) frequency))‖≤
      sourceChargedHamiltonianPrice sideR edgeR := by
  rw [←sourceChargedEnergyPair_fourier]
  exact sourceChargedEnergyPair_bound sideL edgeL sideR edgeR

end LowEnergy.PreparationPhysicalChargedHamiltonianRead
