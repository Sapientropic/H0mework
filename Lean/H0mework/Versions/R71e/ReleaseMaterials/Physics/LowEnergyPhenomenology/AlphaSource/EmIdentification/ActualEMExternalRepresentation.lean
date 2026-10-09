import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMNativeChargeFull
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMPoleWard
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMVoltage
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMDressedCharacter
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorJointFacts

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMExternalRepresentation
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open DiracExteriorMatterAction DiracCliffordRepresentation YangMills.FullPairing
open CanonicalGradedSpatialSource GaussNativeMatter
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumFockGauge
open FullQuantum.FullSpace FullQuantum.Triangular
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalNativeOriginPhaseWard
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNormalizedFullField PreparationPhysicalJointRotationCharge
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMPoleWard GaussComposite.PhysicalEMNativeChargePrimal
open GaussComposite.PhysicalEMNativeChargeFull GaussComposite.PhysicalEMDressedCharacter
open ChargedPreparation.Dynamics
open MixedSpectatorCandidate NamedColorQtNext
open GaussQuantumMultiplier CanonicalGradedCharge GaussCoreHilbert GaussFockLift
open SU7ExteriorMatterRestriction
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The independent conjugate-dual branch keeps the opposite charge at every one of the original252 modes. -/
def actualEMBranchWeight : Quantum.Index⊕Quantum.Index→ℚ :=
  Sum.elim emChargeWeight (fun i=> -emChargeWeight i)

private theorem primal_literal :
    emPrimalCharge=Quantum.operatorMatrix (Complex.I • emGaugeAction) := by
  rw [emPrimalCharge,←sourcePhaseGaugeGenerator_native,em_phase_gauge_action,map_smul]

/-- Full504 literal EM charge, including every fractional charge and the independent dual sign. -/
theorem actual_em_full_spectrum :
    emFullCharge=Matrix.diagonal (fun i=>(actualEMBranchWeight i:ℂ)) := by
  rw [em_full_charge_generated,primal_literal,em_charge_matrix_diagonal]
  ext i j
  cases i <;> cases j <;>
    simp [actualEMBranchWeight,Matrix.fromBlocks,Matrix.diagonal_apply,eq_comm]

/-- The exterior dressed weight and the Hermitian physical charge are read from the same literal operator. -/
theorem actual_em_exterior_weight (i : Quantum.Index) :
    (emChargeWeight i:ℂ)= -(emDressedWholeWeight i:ℂ) := by
  have literal:=congrArg (fun M : Matrix Quantum.Index Quantum.Index ℂ=>M i i) em_charge_matrix_diagonal
  rw [map_smul,emDressed_matrix] at literal
  simp only [Matrix.smul_apply,Matrix.diagonal_apply,if_true,smul_eq_mul] at literal
  calc
    _=Complex.I*((emDressedWholeWeight i:ℂ)*Complex.I) := literal.symm
    _=_ := by ring_nf;simp only [Complex.I_sq];ring

/-- The two owners literally supply the same native Lie occurrence. -/
theorem composite_em_lie_same : actualSourcePhaseGaugeLie=sourcePhaseGaugeLie := rfl

/-- The actual independent-dual504 CAR Noether is the same literal EM charge, before selecting an external state. -/
theorem composite_em_charge_same : quantized emFullCharge=phaseCharge := by
  change quantizer (Complex.I • nativeFull sourcePhaseGaugeLie)=
    Complex.I • quantizer (nativeFull actualSourcePhaseGaugeLie)
  rw [composite_em_lie_same,map_smul]

def actualCompositeUnit (dual : Bool) : FockFiber :=
  ((Real.sqrt 2:ℂ)⁻¹) • candidate dual

theorem actual_composite_unit_norm (dual : Bool) : ‖actualCompositeUnit dual‖=1 := by
  have square : ‖candidate dual‖^2=2 := by
    rw [@norm_sq_eq_re_inner ℂ,actual_candidate_norm_sq]
    norm_num
  have normvalue : ‖candidate dual‖=Real.sqrt 2 := by
    have root:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have nonnegative:=norm_nonneg (candidate dual)
    have rootNonnegative:=Real.sqrt_nonneg (2:ℝ)
    nlinarith
  rw [actualCompositeUnit,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2),normvalue,inv_mul_cancel₀ (by positivity : Real.sqrt 2≠0)]

/-- A normalized actual source external state has literal EM charge, genuine Dirac spin and the full color kernel simultaneously. -/
theorem actual_composite_em_spin_color (dual : Bool) :
    ‖actualCompositeUnit dual‖=1 ∧
    quantized emFullCharge (actualCompositeUnit dual)=
      (if dual then (-1:ℂ) else 1) • actualCompositeUnit dual ∧
    originalSpinCasimir (actualCompositeUnit dual)=(3/4:ℂ) • actualCompositeUnit dual ∧
    (∀A : SU7MotherLieAlgebra.SU3BlockLieMatrix,nativeFock (MixedSpectatorCandidate.colorNative A)
      (actualCompositeUnit dual)=0) := by
  refine ⟨actual_composite_unit_norm dual,?_,?_,?_⟩
  · rw [composite_em_charge_same,actualCompositeUnit,map_smul,actual_candidate_phase_charge]
    module
  · rw [actualCompositeUnit,map_smul,actual_candidate_spin_half]
    module
  · intro A
    rw [actualCompositeUnit,map_smul,actual_candidate_color_singlet A dual,smul_zero]

end LowEnergy.GaussComposite.ActualEMExternalRepresentation
