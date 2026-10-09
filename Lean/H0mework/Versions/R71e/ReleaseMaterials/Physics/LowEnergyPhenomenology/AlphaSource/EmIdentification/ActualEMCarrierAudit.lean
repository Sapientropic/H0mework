import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPreparedResidue
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierCertification
open ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineHolonomicField StageNineP286GaugeAuxiliaryVariation
open Stage10 SourceQuantumScalarOrbitDimensions
open PhysicalEMGaugeRealization PhysicalEMFieldCurrent
open PreparationCoordinates PreparationVacuumGaugeSourceInjection
open PreparationPhysicalNativePhotonFluxReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
open PreparationVacuumElectromagneticIdentity Electromagnetic.CanonicalCoframe
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNativePolarizationEmitter
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage10
open PreparationCoordinates PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumNativeDimensions
open SourcePropagationNativeActionHessian PreparationVacuumNativePoleTensor
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalActualPolarizationResponse PreparationPhysicalElectromagneticDirectionReturn
open PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalQuantumLockedCharge CanonicalGradedSpatialSource
open scoped Matrix BigOperators Topology
open PreparationPhysicalNormalizedFullField PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
open CanonicalGradedSpatialSource PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback PreparationVacuumNativePoleTensor
open PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalCommonCurrentStaticRead
open PreparationPhysicalActualPolarizationResponse PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalFinitePoleVertices Electromagnetic.CanonicalCoframe
open PreparationVacuumElectromagneticIdentity PreparationVacuumFullPoleContinuation

theorem checked_em_original_coordinates : rawCoordinates (p286CoordinateEquiv emDirection) =
    -(1/2:ℝ) • Pi.single 6 1 + (1/2:ℝ) • Pi.single 7 1 - (1/2:ℝ) • Pi.single 11 1 :=
  em_original_coordinates

theorem checked_em_origin_projection (w : Fin 289 → ℂ) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ (fullNativeOrigin *ᵥ w)) mu = 0 :=
  em_origin_projection w mu

theorem checked_em_frequency_projection_generated (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon ≠ 0) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ sourceNativeFrequencyPolarization branch epsilon s n) mu =
      emFrequencyProjection branch epsilon s n mu :=
  em_frequency_projection_generated branch epsilon s n nonzero mu

theorem checked_em_actual_mode_cosource (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) :
    nativeModeForcing epsilon s n (sheetCurrent q epsilon s n p left right T) =
      emActualModeCosource q epsilon s n p left right T :=
  em_actual_mode_cosource q epsilon s n p left right T

theorem checked_em_actual_frequency_projection (q : PhysicalResponsePoint) (branch : Fin 2)
    (n p : PhysicalMomentum) (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach, ∀ mu : Fin 4,
      (emInsertion.transpose *ᵥ actualFrequencyResidue q e.val (sourceSheet branch n unit e.val) n p left right T) mu =
        emActualCofactorAmplitude q branch e.val (sourceSheet branch n unit e.val) n p left right T *
          emFrequencyProjection branch e.val (sourceSheet branch n unit e.val) n mu :=
  em_actual_frequency_projection q branch n p unit left right T

theorem checked_em_electron_source_nonzero (side : Fin 2) :
    actualRestNativeComplexForcingCovector 0 (sourceChargedRestIndex side 0)
      (sourceChargedRestIndex side 0) ≠ 0 :=
  em_electron_source_nonzero side

theorem checked_em_actual_background_derivative_nonzero (point : BasePoint) :
    emBackgroundDerivative point ≠ 0 :=
  em_actual_background_derivative_nonzero point

theorem checked_em_prepared_cofactor_all64 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (branch : Fin 2)
    (epsilon s : ℝ) (n : PhysicalMomentum) :
    emCofactorRead branch epsilon s n (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) =
      ∑a : RestStateIndex, ∑b : RestStateIndex,
        sourceActualPreparedWeight 0 0 sL eL sR eR a b *
          emCofactorRead branch epsilon s n (returnedCurrentWindow q pL pR a b lambda T) :=
  em_prepared_cofactor_all64 q pL pR sL eL sR eR lambda T branch epsilon s n

theorem checked_em_prepared_ordinary_return (qd : PhysicalResponsePoint) (pDL pDR : PhysicalMomentum)
    (dSL dEL dSR dER : Fin 2) (lambda : ℂ) (T : ℝ)
    (qs : PhysicalResponsePoint) (pSL pSR : PhysicalMomentum) (sSL sEL sSR sER : Fin 2)
    (mu : ℂ) (S : ℝ) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hzd : qd.z.im ≠ 0) (hwd : qd.w.im ≠ 0) :
    ∀ᶠ e in scaleApproach,
      sourceQuantumChargedRead qd dSL dEL dSR dER
        (sourceActualPreparedKernel qd pDL pDR lambda T
          (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
            sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S)) =
      emCofactorRead branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent qs pSL pSR sSL sEL sSR sER mu S) *
      sourceQuantumChargedRead qd dSL dEL dSR dER
        (sourceActualPreparedKernel qd pDL pDR lambda T
          (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)) :=
  em_prepared_ordinary_return qd pDL pDR dSL dEL dSR dER lambda T qs pSL pSR sSL sEL sSR sER mu S branch n unit hzd hwd

theorem checked_em_prepared_frequency_projection (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (sL eL sR eR : Fin 2) (lambda : ℂ) (T : ℝ) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach, ∀ mu : Fin 4,
      (emInsertion.transpose *ᵥ
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
          sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)) mu =
      emCofactorRead branch e.val (sourceSheet branch n unit e.val) n
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) *
      emFrequencyProjection branch e.val (sourceSheet branch n unit e.val) n mu :=
  em_prepared_frequency_projection q pL pR sL eL sR eR lambda T branch n unit

theorem checked_em_raw_slot6 : rawCoordinates (p286CoordinateEquiv emDirection) 6 = -(1/2:ℝ) := by
  rw [em_original_coordinates]
  norm_num [Pi.single_apply, Fin.ext_iff]

theorem checked_em_raw_slot7 : rawCoordinates (p286CoordinateEquiv emDirection) 7 = (1/2:ℝ) := by
  rw [em_original_coordinates]
  norm_num [Pi.single_apply, Fin.ext_iff]

theorem checked_em_raw_slot11 : rawCoordinates (p286CoordinateEquiv emDirection) 11 = -(1/2:ℝ) := by
  rw [em_original_coordinates]
  norm_num [Pi.single_apply, Fin.ext_iff]

end LowEnergy.GaussComposite.ActualEMCarrierCertification

open Lean Elab Command
private def carrierCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def carrierCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (carrierCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def carrierCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := carrierCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_actual_em_carrier" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`ActualEMCarrier,`ActualEMResidueTensor,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPreparedResidue]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emInsertion,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emPropagatingCarrier,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emPropagator,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emPoleTensor,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_pole_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_carrier_homogeneous,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_flux_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emBackgroundDerivative,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_background_derivative,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emElectronCarrier,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_source_current,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_source_unit,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_homogeneous,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_constraint_return,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_residue_flux,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_source_nonzero,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_pole_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emElectronFrequencyCarrier,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_physical_frequency_flux,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_background_derivative_nonzero,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emElectronPoleAmplitude,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_native_factor,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_null_constraint,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_visibility_iff,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_frequency_pole_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_original_coordinates,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_projection_coordinates,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emLiteralA,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emLiteralB,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_literal_projection,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_origin_projection,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emFrequencyProjection,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_frequency_projection_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emActualModeCosource,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_mode_cosource,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emActualCofactorAmplitude,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_cofactor_amplitude,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_frequency_factor,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_frequency_projection,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emModeReadLinear,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emCofactorRead,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_cofactor_read_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_cofactor_all64,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_frequency_factor,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_ordinary_return,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_frequency_projection]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_original_coordinates,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_origin_projection,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_frequency_projection_generated,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_actual_mode_cosource,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_actual_frequency_projection,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_electron_source_nonzero,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_actual_background_derivative_nonzero,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_prepared_cofactor_all64,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_prepared_ordinary_return,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_prepared_frequency_projection,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_raw_slot6,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_raw_slot7,
    ``LowEnergy.GaussComposite.ActualEMCarrierCertification.checked_em_raw_slot11]
  let all ← carrierCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.PhysicalEMGaugeRealization.emDirection,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonGreen,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourcePhotonSheetJacobiJet,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonFrequencyResidue,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourcePhotonFrequencyJacobiJet,
    ``LowEnergy.PreparationPhysicalNormalizedFullField.sourceEnergyChannelTerms,
    ``LowEnergy.PreparationPhysicalNativePoleChargeReturn.sourcePoleFastJet,
    ``LowEnergy.PreparationPhysicalNativePoleChargeReturn.sourcePoleFrameResidual,
    ``LowEnergy.PreparationVacuumNativePoleTensor.sheetCurrent_ward,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedWeight,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedCurrent,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedKernel,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceQuantumChargedRead]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_pole_generated, #[``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonGreen_residue]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_carrier_homogeneous, #[``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_homogeneous]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_flux_generated, #[``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_sheetFlux]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_source_unit, #[``LowEnergy.GaussComposite.PhysicalEMFieldCurrent.em_forcing_temporal_unit]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_source_nonzero, #[``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_source_unit]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_native_factor, #[``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_factor]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_visibility_iff, #[``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_native_factor,``LowEnergy.PreparationPhysicalNativePolarizationEmitter.sourceNativePolarization_generated]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_literal_projection, #[``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_projection_coordinates]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_frequency_projection_generated, #[``LowEnergy.PreparationPhysicalNativePoleChargeReturn.sourceNativeFrequencyPolarization_firstReturn,``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_origin_projection,``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_literal_projection]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_mode_cosource, #[``LowEnergy.PreparationVacuumNativePoleTensor.sheetCurrent_ward]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_cofactor_amplitude, #[``LowEnergy.PreparationVacuumPhysicalPoleSheet.sourceSheet_simple,``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_mode_cosource]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_frequency_factor, #[``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_cofactor_amplitude,``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_factor]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_frequency_projection, #[``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_frequency_factor,``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_frequency_projection_generated]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_cofactor_all64, #[``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedCurrent,``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedWeight]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_frequency_factor, #[``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedDetector_frequency,``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_cofactor_read_generated]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_ordinary_return, #[``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_frequency_factor,``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedDetector_action]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_frequency_projection, #[``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonResidue_factor,``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_frequency_projection_generated])]
  for (mouth,required) in direct do
    carrierCertRequire env mouth required
  for i in [:10] do
    let producer := #[
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_original_coordinates,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_origin_projection,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_frequency_projection_generated,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_mode_cosource,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_frequency_projection,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_electron_source_nonzero,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_actual_background_derivative_nonzero,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_cofactor_all64,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_ordinary_return,
      ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_frequency_projection][i]!
    carrierCertRequire env tests[i]! #[producer]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_ACTUAL_EM_CARRIER_AUDIT_OUTPUT") then
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
  logInfo m!"ACTUAL_EM_CARRIER_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_actual_em_carrier

#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_origin_projection
#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_frequency_projection_generated
#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_prepared_ordinary_return
