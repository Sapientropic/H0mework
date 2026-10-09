import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualCoulombScalar
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

open Lean Elab Command

noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumRawJointFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumStaticPoleResponse PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumElectromagneticIdentity
open PreparationPhysicalStaticCompositeProjectionReturn
open PreparationPhysicalGaugePreparedStaticCEM PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalCoframePreparedReturn
open GaussComposite.PhysicalEMStaticReaderRecognition
open GaussComposite.PhysicalEMActualStaticWindow GaussComposite.PhysicalEMActualCoulombScalar
open scoped BigOperators

theorem checked_complete_source_reader (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    currentRestriction sourceStaticCompositeGauge p F 0=
      rawReader (gaugeField 1 0) p F 0-rawReader (gaugeField 2 1) p F 0+
        emStaticReaderCompensation p F :=
  em_static_reader_currentRestriction_generated p F

theorem checked_original_age_window (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    actualOriginWeight q pL pR l r lambda T=
      emFullStaticWindow q pL pR l r lambda T+
        emCompensationStaticWindow q pL pR l r lambda T :=
  em_actual_origin_window_split q pL pR l r lambda T

theorem checked_source_configuration_age (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    emFullStaticWindow q pL pR l r lambda T=
      -(3/10:ℂ)*rootTwo*∫t in (0:ℝ)..T,laplaceWeight lambda t*
        sourceStaticCompositeConfiguration pR
          (sourceTestApprox q.F ((physicalTime pL q.F (-t) 0*jointResolvent pL q.F q.z 0).adjoint
            (sourcePolePrepared q.epsilon q.precision pL l)))
          (sourceTestApprox q.F ((jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0)
            (sourcePolePrepared q.epsilon q.precision pR r))) :=
  em_fullStaticWindow_config q pL pR l r lambda T

theorem checked_zero_age (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (lambda : ℂ) :
    actualOriginWeight q pL pR l r lambda 0=0 ∧
      emFullStaticWindow q pL pR l r lambda 0=0 ∧
      emCompensationStaticWindow q pL pR l r lambda 0=0 :=
  em_actual_origin_window_zero q pL pR l r lambda

section ActualCoulomb
variable (branch : Fin 2) (qd q : PhysicalResponsePoint)
  (dSL dEL dSR dER sL eL sR eR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
  (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0)
include hzd hwd hz hw

theorem checked_original_raw_scalar :
    sourceGaugeStaticCEM branch qd q dSL dEL dSR dER sL eL sR eR T n=
      sourceActualLegNormalization qd dSL dEL dSR dER*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*
          emActualOriginScalar qd dSL dEL dSR dER T*
          emCoframeStaticScalar q sL eL sR eR n-
          sourceActualLegCorrection qd dSL dEL dSR dER
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceGaugeActualCoulombField q sL eL sR eR n))) :=
  em_staticCEM_scalar_generated branch qd q
    dSL dEL dSR dER sL eL sR eR T n hzd hwd hz hw

theorem checked_single_source_unit :
    sourceGaugeStaticAlpha branch qd q dSL dEL dSR dER sL eL sR eR T n=
      (((Stage10.ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹)*
        (sourceActualLegNormalization qd dSL dEL dSR dER*
          (((9023/9000:ℂ)*rootTwo*rootFifteen)*
            emActualOriginScalar qd dSL dEL dSR dER T*
            emCoframeStaticScalar q sL eL sR eR n-
            sourceActualLegCorrection qd dSL dEL dSR dER
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL eL sR eR n)))) :=
  em_staticAlpha_scalar_generated branch qd q
    dSL dEL dSR dER sL eL sR eR T n hzd hwd hz hw

end ActualCoulomb
end LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit
end

private def actualCoulombChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def actualCoulombClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (actualCoulombChildren info).toList ++ pending
      seen := seen.insert name
  return seen

elab "#audit_actual_coulomb" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`PhysicalEMStaticReaderRecognition,`PhysicalEMActualStaticWindow,
    `H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualCoulombScalar]
  for name in owners do
    unless modules.contains name do throwError m!"MISSING_MODULE {name}"
  let owned := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some index => if owners.contains modules[index.toNat]! then some name else none
    | none => none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.emStaticReaderModeForm,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.emStaticReaderCompensationConfiguration,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_field_generated,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.emStaticReaderModeReader,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.emStaticReaderCompensation,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_modeReader_finiteRiesz,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_currentRestriction_generated,
    ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_currentVertex_pair,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.emActualJointKernel,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.emStaticModeKernel,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.emFullStaticKernel,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.emCompensationStaticKernel,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_jointKernel_expanded,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_static_kernel_slots,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_static_kernel_distribution,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_euler_jointKernel,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_fullKernel_poleRead_config,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_physicalTime_left_continuous,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_physicalTime_right_continuous,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_fullKernel_continuous,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_compKernel_continuous,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.emFullStaticWindow,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.emCompensationStaticWindow,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_fullStaticWindow_config,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_split,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_weighted,
    ``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_zero,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.emActualOriginScalar,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.emCoframeStaticScalar,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_spatial_inverse_sum_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_detector_column,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_detector_tensor_scalar,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_preparedDetector_tensor_scalar,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_outer_scalar_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticAlpha_scalar_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_window_generated]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let consumers := #[
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit.checked_complete_source_reader,
      #[``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_currentRestriction_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit.checked_original_age_window,
      #[``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_split]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit.checked_source_configuration_age,
      #[``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_fullStaticWindow_config]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit.checked_zero_age,
      #[``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_zero]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit.checked_original_raw_scalar,
      #[``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombAudit.checked_single_source_unit,
      #[``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticAlpha_scalar_generated])]
  let all ← actualCoulombClosure env (owned ++ (consumers.map Prod.fst).toList)
  let anchors := #[
    ``LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn.sourceStaticCompositeConfiguration_generated,
    ``LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn.sourceStaticCompositeMatter,
    ``LowEnergy.PreparationVacuumFullFieldRiesz.currentRestriction_original_pair,
    ``LowEnergy.PreparationVacuumFullFieldRiesz.currentVertex_original_pair,
    ``LowEnergy.PreparationVacuumPhysicalPoleHalfResponse.sourcePoleActionEuler_source,
    ``LowEnergy.PreparationVacuumMovingPoleGaussReturn.sourcePoleRead_actual,
    ``LowEnergy.PreparationVacuumRawJointFeedback.physicalTime,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator,
    ``LowEnergy.PreparationVacuumUncutYukawa.uncutOperator,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedWeight,
    ``LowEnergy.PreparationPhysicalCoframePreparedReturn.sourceCoframePreparedStatic,
    ``LowEnergy.PreparationPhysicalCoframePreparedReturn.sourceCoframeComplementOutput,
    ``LowEnergy.PreparationPhysicalCoframePreparedReturn.sourceNativeSimple_prepared,
    ``LowEnergy.PreparationVacuumFullOriginResponse.actual_origin_kernel_read,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_zero,
    ``LowEnergy.PreparationPhysicalGaugePreparedStaticCEM.sourceGaugeStaticCEM_generated,
    ``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualLegNormalization,
    ``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualLegCorrection,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedKernel,
    ``SaturationMonoid.PhysicsCore.Stage10.ActionNormalization.phaseMomentum,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_field_generated,
      #[``LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn.sourceStaticCompositeConfiguration_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_currentRestriction_generated,
      #[``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_field_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_currentVertex_pair,
      #[``LowEnergy.PreparationVacuumFullFieldRiesz.currentVertex_original_pair]),
    (``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_fullKernel_poleRead_config,
      #[``LowEnergy.PreparationVacuumFullFieldRiesz.currentRestriction_original_pair,
        ``LowEnergy.PreparationVacuumMovingPoleGaussReturn.sourcePoleRead_actual]),
    (``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_split,
      #[``LowEnergy.PreparationVacuumPhysicalPoleHalfResponse.sourcePoleActionEuler_source,
        ``LowEnergy.GaussComposite.PhysicalEMStaticReaderRecognition.em_static_reader_currentRestriction_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_weighted,
      #[``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_split]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_detector_tensor_scalar,
      #[``LowEnergy.PreparationVacuumFullOriginResponse.actual_origin_kernel_read,
        ``LowEnergy.PreparationPhysicalCoframePreparedReturn.sourceNativeSimple_prepared]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated,
      #[``LowEnergy.PreparationPhysicalGaugePreparedStaticCEM.sourceGaugeStaticCEM_generated,
        ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_outer_scalar_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticAlpha_scalar_generated,
      #[``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_window_generated,
      #[``LowEnergy.GaussComposite.PhysicalEMActualStaticWindow.em_actual_origin_window_split,
        ``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated])]
  for (mouth, required) in direct ++ consumers do
    let closed ← actualCoulombClosure env [mouth]
    for name in required do
      unless closed.contains name do throwError m!"UNCONSUMED_DIRECT {mouth} {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaqueCount : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in owned ++ (consumers.map Prod.fst).toList do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError m!"UNAUTHORIZED_ROOT_AXIOM {name} {axiomName}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  for moduleName in modules do
    if (moduleName.toString.toLower.splitOn ".").contains "scratch" then
      throwError m!"SCRATCH_IMPORT {moduleName}"
  logInfo m!"EM_ACTUAL_COULOMB_PASS public={mouths.size} owned={owned.length} nodes={all.size} anchors={anchors.size} direct={direct.size} consumers={consumers.size} opaque_all_read={opaqueCount} axioms={axioms} unknown=0 unsafe=0 partial=0"

#audit_actual_coulomb
