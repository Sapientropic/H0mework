import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualChargedPoleDynamics
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMExternalRepresentation
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.GaussComposite.ActualChargedIdentityAudit
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage10 Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open DiracExteriorMatterAction DiracCliffordRepresentation YangMills.FullPairing
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNormalizedFullField PreparationPhysicalJointRotationCharge
open PreparationPhysicalChargedScatteringPoleReturn PreparationVacuumPhysicalFeedback
open ChargedPreparation.Dynamics GaussCoreHilbert FullQuantum.FullSpace FullQuantum.Triangular
open FullQuantum FullSpace
open GaussComposite.PhysicalEMVoltage GaussComposite.PhysicalEMChargeReadout
open PreparationPhysicalActualPhaseChargeReturn
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace
open CanonicalGradedSpatialSource GaussNativeMatter
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumFockGauge
open FullQuantum.FullSpace FullQuantum.Triangular
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalNativeOriginPhaseWard
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMPoleWard GaussComposite.PhysicalEMNativeChargePrimal
open GaussComposite.PhysicalEMNativeChargeFull GaussComposite.PhysicalEMDressedCharacter
open ChargedPreparation.Dynamics
open MixedSpectatorCandidate NamedColorQtNext
open GaussQuantumMultiplier CanonicalGradedCharge GaussCoreHilbert GaussFockLift
open SU7ExteriorMatterRestriction
open scoped Matrix BigOperators
open ActualChargedPoleDynamics ActualEMExternalRepresentation

theorem checked_actual_charged_hamiltonian (p : PhysicalMomentum) (side edge : Fin 2) :
    FullQuantum.hamiltonian actual 0 p (sourceChargedRestriction side edge)=
      (chargedEnergyDiagonal p side edge:ℂ) • sourceChargedRestriction side edge+
        chargedTransverseCoefficient p side edge • chargedTransverseRestriction side edge := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_hamiltonian p side edge

theorem checked_actual_charged_axis_hamiltonian (k : ℝ) (side edge : Fin 2) :
    FullQuantum.hamiltonian actual 0 (chargedAxisMomentum k) (sourceChargedRestriction side edge)=
      (chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ) • sourceChargedRestriction side edge := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_hamiltonian k side edge

theorem checked_actual_charged_positive_axis (k : ℝ) (nonnegative : 0≤k) :
    0<chargedEnergyDiagonal (chargedAxisMomentum k) 1 0 := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_positive_axis k nonnegative

theorem checked_actual_charged_axis_rest (side edge : Fin 2) :
    chargedEnergyDiagonal (chargedAxisMomentum 0) side edge=sourceActualChargedRestEnergy side := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_rest side edge

theorem checked_actual_charged_axis_velocity (k : ℝ) (side edge : Fin 2) :
    HasDerivAt (fun x : ℝ=>chargedEnergyDiagonal (chargedAxisMomentum x) side edge)
      (chargedSideSign side*chargedEdgeSign edge*lapse) k := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_velocity k side edge

theorem checked_actual_charged_axis_value (k : ℝ) (side edge : Fin 2) (energy damping : ℝ)
    (positive : 0<damping) :
    Retarded.value 0 (chargedAxisMomentum k) energy damping (naturalCoordinates (sourceChargedRestriction side edge))=
      (Complex.I/(Retarded.spectralParameter energy damping-
        (chargedEnergyDiagonal (chargedAxisMomentum k) side edge:ℂ))) •
        naturalCoordinates (sourceChargedRestriction side edge) := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_value k side edge energy damping positive

theorem checked_actual_charged_axis_dirac (k : ℝ) (side edge : Fin 2) (energy damping : ℝ)
    (positive : 0<damping) :
    Retarded.diracValue 0 (chargedAxisMomentum k) energy damping (naturalCoordinates (sourceChargedRestriction side edge))=
      ((-(lapse:ℂ)*sourceRestSign side)/(Retarded.spectralParameter energy damping-
        (chargedEnergyDiagonal (chargedAxisMomentum k) (1-side) edge:ℂ))) •
        naturalCoordinates (sourceChargedRestriction (1-side) edge) := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_dirac k side edge energy damping positive

theorem checked_actual_charged_axis_radial_gap (k : ℝ) (positive : 0<k) :
    ChargedPreparation.SpatialSpectrum.upperEnergy (chargedAxisMomentum k)<
      chargedEnergyDiagonal (chargedAxisMomentum k) 1 0 := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_radial_gap k positive

theorem checked_actual_charged_axis_velocity_constant (k : ℝ) (side edge : Fin 2) :
    HasDerivAt (fun _ : ℝ=>chargedSideSign side*chargedEdgeSign edge*lapse) 0 k := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_velocity_constant k side edge

theorem checked_actual_charged_axis_residue_exact (k : ℝ) (side edge : Fin 2) (damping : ℝ)
    (positive : 0<damping) :
    (damping:ℂ) • Retarded.diracValue 0 (chargedAxisMomentum k)
      (chargedEnergyDiagonal (chargedAxisMomentum k) (1-side) edge) damping
      (naturalCoordinates (sourceChargedRestriction side edge))=
        (Complex.I*(lapse:ℂ)*sourceRestSign side) •
          naturalCoordinates (sourceChargedRestriction (1-side) edge) := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_residue_exact k side edge damping positive

theorem checked_actual_charged_moving_support (k : ℝ) (side edge : Fin 2) (state : RestStateIndex)
    (different : sourceMovingPoleEnergy (chargedAxisMomentum k) state≠
      chargedEnergyDiagonal (chargedAxisMomentum k) side edge) :
    sourceChargedMovingCoefficient (chargedAxisMomentum k) side edge state=0 := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_support k side edge state different

theorem checked_actual_charged_moving_energy_fiber (k : ℝ) (side edge : Fin 2) :
    sourceChargedRestriction side edge=∑state : RestStateIndex,
      if sourceMovingPoleEnergy (chargedAxisMomentum k) state=chargedEnergyDiagonal (chargedAxisMomentum k) side edge
      then sourceChargedMovingCoefficient (chargedAxisMomentum k) side edge state •
        actualMovingPolePreparation (chargedAxisMomentum k) state (embed (Source.vector 0)) else 0 := by
  exact @LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_energy_fiber k side edge

theorem checked_actual_em_full_spectrum :
    emFullCharge=Matrix.diagonal (fun i=>(actualEMBranchWeight i:ℂ)) := by
  exact @LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_full_spectrum

theorem checked_actual_em_exterior_weight (i : Quantum.Index) :
    (emChargeWeight i:ℂ)= -(emDressedWholeWeight i:ℂ) := by
  exact @LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_exterior_weight i

theorem checked_composite_em_lie_same : actualSourcePhaseGaugeLie=sourcePhaseGaugeLie := by
  exact @LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_lie_same

theorem checked_composite_em_charge_same : quantized emFullCharge=phaseCharge := by
  exact @LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_charge_same

theorem checked_actual_composite_unit_norm (dual : Bool) : ‖actualCompositeUnit dual‖=1 := by
  exact @LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_unit_norm dual

theorem checked_actual_composite_em_spin_color (dual : Bool) :
    ‖actualCompositeUnit dual‖=1 ∧
    quantized emFullCharge (actualCompositeUnit dual)=
      (if dual then (-1:ℂ) else 1) • actualCompositeUnit dual ∧
    originalSpinCasimir (actualCompositeUnit dual)=(3/4:ℂ) • actualCompositeUnit dual ∧
    (∀A : SU7MotherLieAlgebra.SU3BlockLieMatrix,nativeFock (MixedSpectatorCandidate.colorNative A)
      (actualCompositeUnit dual)=0) := by
  exact @LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_em_spin_color dual

theorem checked_composite_nonzero (dual : Bool) : actualCompositeUnit dual≠0 := by
  intro zero
  have normed:=actual_composite_unit_norm dual
  rw [zero,norm_zero] at normed
  exact zero_ne_one normed

theorem checked_actual_positive_rest : 0<chargedEnergyDiagonal (chargedAxisMomentum 0) 1 0 :=
  actual_charged_positive_axis 0 le_rfl

theorem checked_gap_at_one :
    ChargedPreparation.SpatialSpectrum.upperEnergy (chargedAxisMomentum 1)<
      chargedEnergyDiagonal (chargedAxisMomentum 1) 1 0 :=
  actual_charged_axis_radial_gap 1 (by norm_num)

theorem checked_independent_dual_weights (i : Quantum.Index) :
    actualEMBranchWeight (Sum.inl i)=emChargeWeight i ∧
    actualEMBranchWeight (Sum.inr i)=-emChargeWeight i := ⟨rfl,rfl⟩

theorem checked_charged_index_same_actual :
    sourceChargedRestIndex 1 0=((1:Fin 2),(1:Fin 4)) ∧
    sourceChargedRestIndex 1 0≠((0:Fin 2),(0:Fin 4)) := by decide +kernel

end LowEnergy.GaussComposite.ActualChargedIdentityAudit

