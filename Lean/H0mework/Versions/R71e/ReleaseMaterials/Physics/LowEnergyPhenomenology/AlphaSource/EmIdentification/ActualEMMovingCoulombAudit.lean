import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingCoulombPacket

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMMovingCoulombAudit
elab "checked_moving_coulomb_radius_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive).type
theorem checked_moving_coulomb_radius_positive : checked_moving_coulomb_radius_positiveContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive

elab "checked_moving_coulomb_symbol_boundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound).type
theorem checked_moving_coulomb_symbol_bound : checked_moving_coulomb_symbol_boundContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound

elab "checked_moving_coulomb_packet_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable).type
theorem checked_moving_coulomb_packet_integrable : checked_moving_coulomb_packet_integrableContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable

elab "checked_moving_coulomb_packet_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit).type
theorem checked_moving_coulomb_packet_limit : checked_moving_coulomb_packet_limitContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit

elab "checked_moving_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit).type
theorem checked_moving_coulomb_spatial_limit : checked_moving_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit

elab "checked_moving_coulomb_spatial_limit_restContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest).type
theorem checked_moving_coulomb_spatial_limit_rest : checked_moving_coulomb_spatial_limit_restContract := @LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open LowEnergy.GaussComposite.ActualEMCarrierOwn LowEnergy.GaussComposite.ActualEMMovingCoulombPacket
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumFullOriginResponse
open PreparationVacuumFullPoleContinuation PreparationVacuumElectromagneticIdentity

theorem checked_packet_same_fourier (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum)
    (active : 0 < scale ∧ 0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) <
        (movingCoulombRadius d s branch hdz hdw hsz hsw : ℝ)) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw scale k=
      emMovingWholeRead d s branch (scale • k,0) (wholeCoulombIRSymbol scale k) ∧
    actualMomentum (s.momentum+(-1:ℝ) • (scale • k)) s.momentum 0=sourceStaticSpatialMomentum k scale ∧
    actualMomentum (d.momentum+(1:ℝ) • (scale • k)) d.momentum 0= -sourceStaticSpatialMomentum k scale := by
  exact ⟨by simp only [movingCoulombSymbol,if_pos active],em_moving_static_same_fourier d s scale k⟩

theorem checked_zero_scale_symbol (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0) (k : PhysicalMomentum) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw 0 k=0 := by
  rw [movingCoulombSymbol,if_neg (by
    intro h
    exact (lt_irrefl (0:ℝ)) h.1)]

theorem checked_zero_momentum_symbol (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0) (scale : ℝ) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw scale 0=0 := by
  have zero : spatialSquare (0:PhysicalMomentum)=0 := by norm_num [spatialSquare]
  rw [movingCoulombSymbol,if_neg (by
    rintro ⟨_,h,_⟩
    rw [zero] at h
    exact (lt_irrefl (0:ℝ)) h)]

theorem checked_outside_window (d s : ActualEMObservationEnd) (branch : Fin 2)
    (hdz : d.q.z.im≠0) (hdw : d.q.w.im≠0) (hsz : s.q.z.im≠0) (hsw : s.q.w.im≠0)
    (scale : ℝ) (k : PhysicalMomentum)
    (outside : movingCoulombRadius d s branch hdz hdw hsz hsw ≤ scale * Real.sqrt (spatialSquare k)) :
    movingCoulombSymbol d s branch hdz hdw hsz hsw scale k=0 := by
  rw [movingCoulombSymbol,if_neg (by
    rintro ⟨_,_,h⟩
    exact (not_lt.mpr outside) h)]

elab "originalMovingActionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_once_action).type
theorem checked_original_all64_single_hc : originalMovingActionContract :=
  @LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_once_action

theorem checked_original_frequency (frequency : PhysicalMomentum) (j : Fin 3) :
    sourceSpatialMomentum frequency j=(2*Real.pi)*frequency j := rfl
end LowEnergy.GaussComposite.ActualEMMovingCoulombAudit

open Lean Elab Command
private def packageCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def packageCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (packageCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def packageCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := packageCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_moving_coulomb" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMMovingCoulombPacket]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.movingCoulombRadius,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.movingCoulombSymbol,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.movingCoulombPacket,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_moving_coulomb_spatial_limit_rest,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_packet_same_fourier,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_zero_scale_symbol,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_zero_momentum_symbol,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_outside_window,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_original_all64_single_hc,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_original_frequency]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_static_domination,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_source_ir_radius_positive]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_static_domination,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_symbol_actual]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_coulomb_budget_integrable,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_packet_integrable]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_static_uniform,
    ``MeasureTheory.tendsto_integral_filter_of_dominated_convergence]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest,#[
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_origin_rest]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_packet_same_fourier,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_static_same_fourier,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.movingCoulombSymbol]),
    (``LowEnergy.GaussComposite.ActualEMMovingCoulombAudit.checked_original_all64_single_hc,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_moving_whole_once_action,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedWeight,
    ``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualLegCorrection])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emMovingWholeRead,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emUnitTransferCurrent,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emUnitTransferTest,
    ``LowEnergy.PreparationPhysicalActualGaussChargeCurrent.sourceActualPreparedWeight,
    ``LowEnergy.PreparationPhysicalActualLegNormalization.sourceActualLegCorrection,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_MOVING_COULOMB_AUDIT_OUTPUT") then
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
  logInfo m!"MOVING_COULOMB_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_moving_coulomb
#print axioms LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_radius_positive
#print axioms LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_symbol_bound
#print axioms LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_integrable
#print axioms LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_packet_limit
#print axioms LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit
#print axioms LowEnergy.GaussComposite.ActualEMMovingCoulombPacket.moving_coulomb_spatial_limit_rest
