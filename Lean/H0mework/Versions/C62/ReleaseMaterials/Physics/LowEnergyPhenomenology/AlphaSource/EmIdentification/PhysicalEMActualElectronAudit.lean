import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualElectronOrdinary
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalNativeEMChargeBridge
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMActualElectronAudit
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumNativeSlowCoupling
open PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin
open PreparationVacuumFullSlowFieldResponse PreparationVacuumStaticSimpleCoupling
open PreparationVacuumChargedSpatialResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalCommonObservableUnits
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalGaugeMomentumCoupling PreparationPhysicalGaugePreparedStaticCEM
open PreparationPhysicalGaugeSpatialChannelExpansion PreparationPhysicalCoframePreparedReturn
open GaussComposite.PhysicalEMActualStaticWindow
open CanonicalGradedSpatialSource
open GaussUnitaryHistory (Index)
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology InnerProductSpace

open GaussComposite.PhysicalEMActualCoulombScalar
open GaussComposite.PhysicalEMActualElectronCoulomb
open GaussComposite.PhysicalEMActualElectronOrdinary
open GaussComposite.PhysicalNativeEMChargeBridge
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open PreparationPhysicalActualPhaseChargeReturn PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn
open FullQuantum FullSpace YangMills.FullPairing

theorem checked_coframeScalar_actual (q : PhysicalResponsePoint)
    (sL eL sR eR : Fin 2) (n : PhysicalMomentum) :
    emCoframeStaticScalar q sL eL sR eR n=
      sourceQuantumChargedRead q sL eL sR eR (sourceCoframePreparedStatic q n) :=
  coframeScalar_actual q sL eL sR eR n

theorem checked_coframeScalar_sameCharge (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (n : PhysicalMomentum) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    emCoframeStaticScalar q sL edge sR edge n=
      sourceQuantumChargedRead q sL edge sR edge
        (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n) :=
  coframeScalar_sameCharge q sL sR edge n hz hw

theorem checked_rawCEM_electron_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticCEM branch qd q dSL 0 dSR 0 sL 0 sR 0 T n=
      sourceActualLegNormalization qd dSL 0 dSR 0*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*
          emActualOriginScalar qd dSL 0 dSR 0 T*
          sourceQuantumChargedRead q sL 0 sR 0
            (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
          sourceActualLegCorrection qd dSL 0 dSR 0
            (sourceActualPreparedKernel qd 0 0 0 T
              (sourceGaugeActualCoulombField q sL 0 sR 0 n))) :=
  rawCEM_electron_generated branch qd q dSL dSR sL sR T n hzd hwd hz hw

theorem checked_coframeScalar_unit_sameCharge (q : PhysicalResponsePoint)
    (sL sR edge : Fin 2) (n : PhysicalMomentum) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceActualLegNormalization q sL edge sR edge*emCoframeStaticScalar q sL edge sR edge n=
      sourceActualUnitLegRead q sL edge sR edge
        (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
        sourceActualLegNormalization q sL edge sR edge*
          sourceActualLegCorrection q sL edge sR edge
            (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n) :=
  coframeScalar_unit_sameCharge q sL sR edge n hz hw

theorem checked_rawCEM_bothElectronLegs_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceActualLegNormalization q sL 0 sR 0*
      sourceGaugeStaticCEM branch qd q dSL 0 dSR 0 sL 0 sR 0 T n=
      sourceActualLegNormalization qd dSL 0 dSR 0*
        (((9023/9000:ℂ)*rootTwo*rootFifteen)*emActualOriginScalar qd dSL 0 dSR 0 T*
          (sourceActualUnitLegRead q sL 0 sR 0
              (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
            sourceActualLegNormalization q sL 0 sR 0*
              sourceActualLegCorrection q sL 0 sR 0
                (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n))-
          sourceActualLegNormalization q sL 0 sR 0*
            sourceActualLegCorrection qd dSL 0 dSR 0
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL 0 sR 0 n))) :=
  rawCEM_bothElectronLegs_generated branch qd q dSL dSR sL sR T n hzd hwd hz hw

theorem checked_rawAlpha_electron_generated (branch : Fin 2) (qd q : PhysicalResponsePoint)
    (dSL dSR sL sR : Fin 2) (T : ℝ) (n : PhysicalMomentum)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    sourceGaugeStaticAlpha branch qd q dSL 0 dSR 0 sL 0 sR 0 T n=
      (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹)*
        (sourceActualLegNormalization qd dSL 0 dSR 0*
          (((9023/9000:ℂ)*rootTwo*rootFifteen)*emActualOriginScalar qd dSL 0 dSR 0 T*
            sourceQuantumChargedRead q sL 0 sR 0
              (sourceCoframeStaticExchange false q n-sourceCoframeStaticExchange true q n)-
            sourceActualLegCorrection qd dSL 0 dSR 0
              (sourceActualPreparedKernel qd 0 0 0 T
                (sourceGaugeActualCoulombField q sL 0 sR 0 n)))) :=
  rawAlpha_electron_generated branch qd q dSL dSR sL sR T n hzd hwd hz hw

theorem checked_actualElectronOrdinary_generated (branch : Fin 2)
    (qd qs : PhysicalResponsePoint) (dSL dSR sL sR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (hzd : qd.z.im≠0) (hwd : qd.w.im≠0) :
    ∀ᶠ e in scaleApproach,
      sourceGaugeCouplingRead branch qd dSL 0 dSR 0 lambda T
        (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
          sourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)=
      sourceActualLegNormalization qd dSL 0 dSR 0*
        (sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
            (sourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)*
          sourceActualPreparedDetector qd 0 0 dSL 0 dSR 0 lambda T
            (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n)-
          sourceActualLegCorrection qd dSL 0 dSR 0
            (sourceActualPreparedKernel qd 0 0 lambda T
              (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
                sourceActualPreparedCurrent qs 0 0 sL 0 sR 0 mu S)))/
        ((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ) :=
  actualElectronOrdinary_generated branch qd qs dSL dSR sL sR lambda mu T S n unit hzd hwd

theorem checked_actual_electron_rest_index (side : Fin 2) :
    sourceChargedRestIndex side 0 = (side, 1) := rfl

theorem checked_same_actual_electron (side : Fin 2) :
    sourceNativeElectronState side = naturalCoordinates (sourceChargedRestriction side 0) :=
  sourceNativeElectronState_source side

theorem checked_actual_em_unit (side : Fin 2) :
    PhysicalEMChargeReadout.emChargeFiber (sourceNativeElectronState side) =
      sourceNativeElectronChargeUnit • sourceNativeElectronState side :=
  em_reader_same_electron_state side

theorem checked_neutral_edge :
    (sourceActualPhaseCharge (1 : Fin 2) : ℂ) ≠ sourceNativeElectronChargeUnit :=
  neutral_edge_not_electron_unit

theorem checked_complete_em_defect : PhysicalEMGaugeRealization.emFullDefect ≠ 0 :=
  full_defect_retained

end LowEnergy.GaussComposite.PhysicalEMActualElectronAudit

open Lean Elab Command
private def actualElectronChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def actualElectronClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (actualElectronChildren info).toList ++ pending
      seen := seen.insert name
  return seen


elab "#audit_actual_electron" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`PhysicalEMActualElectronCoulomb,`H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMActualElectronOrdinary]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb.coframeScalar_actual,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb.coframeScalar_sameCharge,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb.rawCEM_electron_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb.coframeScalar_unit_sameCharge,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb.rawCEM_bothElectronLegs_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronCoulomb.rawAlpha_electron_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronOrdinary.actualElectronOrdinary_generated]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_coframeScalar_actual,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_coframeScalar_sameCharge,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_rawCEM_electron_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_coframeScalar_unit_sameCharge,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_rawCEM_bothElectronLegs_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_rawAlpha_electron_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_actualElectronOrdinary_generated,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_actual_electron_rest_index,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_same_actual_electron,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_actual_em_unit,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_neutral_edge,
    ``LowEnergy.GaussComposite.PhysicalEMActualElectronAudit.checked_complete_em_defect]
  let all ← actualElectronClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestIndex,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceChargedRestriction,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedWeight,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedCurrent,
    ``LowEnergy.PreparationVacuumPhysicalQuantumLockedCharge.sourceQuantumChargedRead,
    ``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualLegCorrection,
    ``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_return,
    ``LowEnergy.PreparationPhysicalCommonCurrentStaticRead.sourceCommonCoulombTensor,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourcePhotonLeftReader,
    ``LowEnergy.PreparationPhysicalNativePhotonFluxReturn.sourceWholePhotonFrequencyResidue,
    ``SaturationMonoid.PhysicsCore.Stage10.ActionNormalization.phaseMomentum,
    ``LowEnergy.PreparationVacuumPhysicalPoleSheet.sourceSpeed]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (mouths[0]!,#[``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualGaussRead_poles]),
    (mouths[1]!,#[``LowEnergy.PreparationPhysicalCoframeChargeExchange.sourceCoframePreparedStatic_sameCharge]),
    (mouths[2]!,#[``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated,mouths[1]!]),
    (mouths[3]!,#[``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualUnitLegRead_return,mouths[1]!]),
    (mouths[4]!,#[``LowEnergy.GaussComposite.PhysicalEMActualCoulombScalar.em_staticCEM_scalar_generated,mouths[3]!]),
    (mouths[5]!,#[mouths[2]!]),
    (mouths[6]!,#[``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedDetector_frequency,``LowEnergy.PreparationPhysicalGaugeMomentumCoupling.sourceGaugeCouplingRead_generated])]
  for (mouth, required) in direct do
    let closed ← actualElectronClosure env [mouth]
    for name in required do
      unless closed.contains name do throwError m!"UNCONSUMED_DIRECT {mouth} {name}"
  for i in [:mouths.size] do
    let closed ← actualElectronClosure env [tests[i]!]
    unless closed.contains mouths[i]! do throwError m!"UNCONSUMED_TEST {tests[i]!} {mouths[i]!}"
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
  for name in owned ++ tests.toList do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError m!"UNAUTHORIZED_ROOT_AXIOM {name} {axiomName}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  for moduleName in modules do
    if (moduleName.toString.toLower.splitOn ".").contains "scratch" then
      throwError m!"SCRATCH_IMPORT {moduleName}"
  if let some path ← liftIO (IO.getEnv "ALPHA_ACTUAL_ELECTRON_AUDIT_OUTPUT") then
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
  logInfo m!"ACTUAL_ELECTRON_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_actual_electron
