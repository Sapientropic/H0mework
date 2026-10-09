import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedHamiltonianMatrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedEnergyVariation
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9C.Material.SpinPair
open FullQuantum FullSpace YangMills.FullPairing Electromagnetic.CanonicalCoframe
open FullQuantum.CoframeResponse FullQuantum.StateGreen FullQuantum.Triangular
open CanonicalGradedSpatialSource
open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalNormalizedFullField
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationVacuumVoltageGaussGreen PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization PreparationVacuumPhysicalQuantumLockedCharge
open StageNineCurrentCoframeMatterTemporalPrincipal
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- This reads the original Hamiltonian matrix, with no charge or phase rescaling. -/
def sourceEnergyMatrixRead : SourceMatrix→ₗ[ℂ] FiberOperators where
  toFun A:=operator (Quantum.operatorMatrix.symm A)
  map_add' A B:=by simp only [map_add,operator_add]
  map_smul' a A:=by simp only [map_smul,operator_smul]; rfl

def sourceEnergyCoefficients (v : ActionState) : Fin 4→FiberOperators :=
  fun k=>sourceEnergyMatrixRead (sourceHamiltonianJetMatrix sourceVoltageActualState v k)

theorem sourceEnergyCoefficients_affine (v : ActionState) (p : PhysicalMomentum) :
    affine (sourceEnergyCoefficients v) p=
      sourceEnergyMatrixRead (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v) p) := by
  simp only [affine,affineMatrix,map_add,map_sum,map_smul,sourceEnergyCoefficients]

/-- The Retarded value already contains i; its original Dirac factorization adds only C0 inverse. -/
def sourceEnergyDiracLeg (v : ActionState) : FullMatterL2→L[ℂ] FullMatterL2 :=
  (spatialLeg (sourceEnergyCoefficients v)).comp (inversePrincipal 0)

def sourceEnergyDiracPrice (v : ActionState) : ℝ :=
  affineBound (sourceEnergyCoefficients v)*‖inversePrincipal 0‖

theorem sourceEnergyDiracLeg_norm (v : ActionState) :
    ‖sourceEnergyDiracLeg v‖ ≤ sourceEnergyDiracPrice v := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (spatialLeg_norm _) (norm_nonneg _))

theorem sourceEnergyDiracLeg_fourier (v : ActionState) (field : FullMatterL2) :
    fourier (sourceEnergyDiracLeg v field)=ᵐ[volume] fun frequency=>
      sourceEnergyMatrixRead (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v)
        (physicalMomentum frequency)) (fourier (sourcePacketDiracFilter field) frequency) := by
  let C:=operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0))
  have constant : fourier (inversePrincipal 0 field)=C.compLpL 2 volume (fourier field):=
    GaugeGreen.constant_fourier C field
  have original:=spatialLeg_fourier (sourceEnergyCoefficients v) (inversePrincipal 0 field)
  rw [constant] at original
  filter_upwards [original,C.coeFn_compLpL (fourier field),
    SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) field] with frequency legAt inverseAt greenAt
  change fourier (sourceEnergyDiracLeg v field) frequency=_ at legAt
  rw [legAt,sourceEnergyCoefficients_affine,inverseAt]
  change _=sourceEnergyMatrixRead _ (fourier (SpatialGreen.green 0 0 1 (by norm_num) field) frequency)
  rw [greenAt,Retarded.diracValue_side 0 _ 0 1 (by norm_num)]
  rfl

/-- Both source legs retain their independently generated normalization; the input packet has unit norm. -/
def sourceChargedEnergyVector (v : ActionState) (side edge : Fin 2) : FullMatterL2 :=
  ((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) •
    sourceEnergyDiracLeg v (sourceChargedSpatialPacket side edge)

attribute [local irreducible] sourceEnergyDiracLeg sourceEnergyDiracPrice sourceEnergyCoefficients

theorem sourceChargedEnergyVector_norm (v : ActionState) (side edge : Fin 2) :
    ‖sourceChargedEnergyVector v side edge‖ ≤
      sourceEnergyDiracPrice v/‖sourceChargedRawPacket side edge‖ := by
  have bound : ‖sourceEnergyDiracLeg v (sourceChargedSpatialPacket side edge)‖ ≤ sourceEnergyDiracPrice v := by
    calc
      _ ≤ ‖sourceEnergyDiracLeg v‖*‖sourceChargedSpatialPacket side edge‖ :=
        (sourceEnergyDiracLeg v).le_opNorm _
      _ = ‖sourceEnergyDiracLeg v‖ := by rw [sourceChargedSpatialPacket_unit,mul_one]
      _ ≤ _ := sourceEnergyDiracLeg_norm v
  change ‖((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ) •
    sourceEnergyDiracLeg v (sourceChargedSpatialPacket side edge)‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (sourceChargedRawPacket side edge)))]
  calc
    _ ≤ ‖sourceChargedRawPacket side edge‖⁻¹*sourceEnergyDiracPrice v :=
      mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

theorem sourceChargedEnergyVector_fourier (v : ActionState) (side edge : Fin 2) :
    fourier (sourceChargedEnergyVector v side edge)=ᵐ[volume] fun frequency=>
      sourceEnergyMatrixRead (affineMatrix (sourceHamiltonianJetMatrix sourceVoltageActualState v)
        (physicalMomentum frequency)) (fourier (sourceChargedFilteredPacket side edge) frequency) := by
  let a : ℂ:=((‖sourceChargedRawPacket side edge‖⁻¹ : ℝ):ℂ)
  have original:=sourceEnergyDiracLeg_fourier v (sourceChargedSpatialPacket side edge)
  change fourier (a • sourceEnergyDiracLeg v (sourceChargedSpatialPacket side edge))=ᵐ[volume] _
  rw [map_smul]
  have filtered : sourceChargedFilteredPacket side edge=a • sourceChargedRawPacket side edge:=rfl
  rw [filtered,map_smul]
  filter_upwards [original,Lp.coeFn_smul a (fourier (sourceEnergyDiracLeg v (sourceChargedSpatialPacket side edge))),
    Lp.coeFn_smul a (fourier (sourceChargedRawPacket side edge))] with frequency legAt leftAt rightAt
  rw [leftAt,rightAt]
  simp only [Pi.smul_apply]
  rw [legAt,map_smul]
  rfl

end LowEnergy.PreparationPhysicalChargedEnergyVariation
