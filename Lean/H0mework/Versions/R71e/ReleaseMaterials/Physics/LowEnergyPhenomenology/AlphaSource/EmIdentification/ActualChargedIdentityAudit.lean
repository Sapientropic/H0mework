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

open Lean Elab Command
private def identityCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def identityCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (identityCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def identityCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := identityCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_actual_charged_identity" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualChargedPoleDynamics,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMExternalRepresentation]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedSideSign,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedEdgeSign,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedAxisMomentum,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedEnergyDiagonal,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedTransverseIndex,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedTransverseRestriction,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.chargedTransverseCoefficient,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_hamiltonian,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_hamiltonian,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_positive_axis,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_rest,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_velocity,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_value,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_dirac,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_radial_gap,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_velocity_constant,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_residue_exact,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_support,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_energy_fiber,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actualEMBranchWeight,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_full_spectrum,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_exterior_weight,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_lie_same,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_charge_same,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actualCompositeUnit,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_unit_norm,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_em_spin_color]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_hamiltonian,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_hamiltonian,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_positive_axis,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_rest,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_velocity,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_value,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_dirac,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_radial_gap,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_velocity_constant,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_axis_residue_exact,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_moving_support,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_charged_moving_energy_fiber,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_em_full_spectrum,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_em_exterior_weight,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_composite_em_lie_same,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_composite_em_charge_same,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_composite_unit_norm,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_composite_em_spin_color,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_composite_nonzero,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_actual_positive_rest,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_gap_at_one,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_independent_dual_weights,
    ``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_charged_index_same_actual]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_hamiltonian,#[
    ``LowEnergy.PreparationPhysicalJointRotationCharge.sourceMovingHamiltonian_original,
    ``LowEnergy.PreparationPhysicalNormalizedFullField.sourceChargedRestriction_basis]),
    (``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_hamiltonian,#[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_hamiltonian]),
    (``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_value,#[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_hamiltonian,
    ``SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded.value_kernel_right]),
    (``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_dirac,#[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_value,
    ``LowEnergy.PreparationPhysicalChargedScatteringPoleReturn.sourceActualChargedTemporalInverse]),
    (``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_residue_exact,#[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_dirac]),
    (``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_energy_fiber,#[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_support,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestriction_moving]),
    (``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_full_spectrum,#[
    ``LowEnergy.GaussComposite.PhysicalEMNativeChargeFull.em_full_charge_generated,
    ``LowEnergy.GaussComposite.PhysicalEMVoltage.em_charge_matrix_diagonal,
    ``LowEnergy.GaussComposite.PhysicalEMPoleWard.em_phase_gauge_action]),
    (``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_exterior_weight,#[
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressed_matrix,
    ``LowEnergy.GaussComposite.PhysicalEMVoltage.em_charge_matrix_diagonal]),
    (``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_charge_same,#[
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_lie_same,
    ``LowEnergy.GaussComposite.PhysicalEMNativeChargeFull.emFullCharge]),
    (``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_unit_norm,#[
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_norm_sq]),
    (``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_em_spin_color,#[
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_unit_norm,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_charge_same,
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_phase_charge,
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_spin_half,
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_color_singlet]),
    (``LowEnergy.GaussComposite.ActualChargedIdentityAudit.checked_gap_at_one,#[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_radial_gap])]
  for (mouth,required) in direct do identityCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_hamiltonian,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_hamiltonian,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_positive_axis,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_rest,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_velocity,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_value,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_dirac,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_radial_gap,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_velocity_constant,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_axis_residue_exact,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_support,
    ``LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_energy_fiber,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_full_spectrum,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_exterior_weight,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_lie_same,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.composite_em_charge_same,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_unit_norm,
    ``LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_em_spin_color]
  for i in [:testProducers.size] do identityCertRequire env tests[i]! #[testProducers[i]!]
  let all ← identityCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.PreparationPhysicalJointRotationCharge.sourceMovingHamiltonian_original,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestriction,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestriction_moving,
    ``LowEnergy.PreparationVacuumElectromagneticIdentity.sourceMovingFullHamiltonian,
    ``LowEnergy.PreparationVacuumElectromagneticIdentity.sourceMovingFullHamiltonian_hermitian,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestIndex,
    ``LowEnergy.GaussComposite.PhysicalEMGaugeRealization.emGaugeAction,
    ``LowEnergy.GaussComposite.PhysicalEMVoltage.em_charge_matrix_diagonal,
    ``LowEnergy.GaussComposite.PhysicalEMNativeChargeFull.emFullCharge,
    ``LowEnergy.GaussComposite.PhysicalEMPoleWard.em_phase_gauge_action,
    ``LowEnergy.MixedSpectatorCandidate.candidate,
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_phase_charge,
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_spin_half,
    ``LowEnergy.MixedSpectatorCandidate.actual_candidate_color_singlet,
    ``LowEnergy.NamedColorQtNext.originalSpinCasimir,
    ``LowEnergy.PreparationPhysicalPhaseGaugeRealization.actualSourcePhaseGaugeLie]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaques : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaques := opaques + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  if let some path ← liftIO (IO.getEnv "ALPHA_IDENTITY_AUDIT_OUTPUT") then
    let project := all.toArray.filter fun name =>
      match owner name with
      | none => false
      | some m => !(#["Mathlib","Init","Lean","Std","Batteries","Aesop","Qq","Plausible","ImportGraph","ProofWidgets"].any (fun h => h.isPrefixOf m.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)),("public",toJson (mouths.map Name.toString)),
      ("tests",toJson (tests.map Name.toString)),("nodes",toJson all.size),("opaque_read",toJson opaques),
      ("axioms",toJson axioms),("anchors",toJson (anchors.map Name.toString)),
      ("direct",toJson (direct.map fun p => (p.1.toString,p.2.map Name.toString))),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"ACTUAL_CHARGED_IDENTITY_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_actual_charged_identity
#print axioms LowEnergy.GaussComposite.ActualChargedPoleDynamics.actual_charged_moving_energy_fiber
#print axioms LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_composite_em_spin_color
#print axioms LowEnergy.GaussComposite.ActualEMExternalRepresentation.actual_em_full_spectrum
