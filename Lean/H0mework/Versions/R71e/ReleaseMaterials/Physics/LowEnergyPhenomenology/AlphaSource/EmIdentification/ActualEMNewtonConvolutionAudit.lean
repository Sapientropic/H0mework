import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource
open PreparationPhysicalChannelRadialJet CanonicalGradedSpatialSource MeasureTheory Filter Set
open scoped Topology SchwartzMap FourierTransform

open ActualEMCarrierOwn
theorem checked_em_inverse_schwartz_apply (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emInverseSchwartz test x = emPacket test x  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply test x

theorem checked_em_spatial_newton_schwartz_integrable (test : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (fun k=>‖test k‖/Real.sqrt (spatialSquare k))  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable test

theorem checked_em_spatial_newton_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun y=>(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y))  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_packet_integrable test x

theorem checked_em_newton_massless_convolution (kappa : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emNewtonPacket kappa 0 test x=
      ∫y : PhysicalMomentum,(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y)  := LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution kappa test x

theorem checked_inverse_packet_integrable (test : 𝓢(PhysicalMomentum,ℂ)) : Integrable (emPacket test) := by
  have paid:=(emInverseSchwartz test).integrable (μ:=volume)
  have same : (emInverseSchwartz test : PhysicalMomentum→ℂ)=emPacket test := by
    funext x
    exact em_inverse_schwartz_apply test x
  rw [←same]
  exact paid

theorem checked_auxiliary_kappa_independent (kappa other : ℂ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    emNewtonPacket kappa 0 test x=emNewtonPacket other 0 test x := by
  rw [em_newton_massless_convolution,em_newton_massless_convolution]

theorem checked_inverse_zero : emInverseSchwartz (0:𝓢(PhysicalMomentum,ℂ))=0 := by
  ext x
  rw [em_inverse_schwartz_apply]
  simp [emPacket]

theorem checked_origin_totalization (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    (4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare (0:PhysicalMomentum)):ℂ))⁻¹*emPacket test (x-0)=0 := by
  simp [spatialSquare]

theorem checked_origin_null_measure : ∀ᵐ y : PhysicalMomentum ∂volume,y≠0 := volume.ae_ne 0

theorem checked_fourpi_not_repeated :
    (4*(Real.pi:ℂ))⁻¹≠((4*(Real.pi:ℂ))^2)⁻¹ := by
  intro same
  have denominator:=inv_injective same
  have real:=congrArg Complex.re denominator
  norm_num [pow_two] at real
  have strong : (1:ℝ)<4*Real.pi := by linarith [Real.pi_gt_three]
  have product : (0:ℝ)<(4*Real.pi)*(4*Real.pi-1) := mul_pos (by linarith) (by linarith)
  nlinarith [product]

theorem checked_original_phase (frequency x : PhysicalMomentum) :
    sourceSpatialPhase frequency x=Complex.exp (Complex.I*((∑j:Fin 3,(2*Real.pi)*frequency j*x j:ℝ):ℂ)) := rfl

theorem checked_nonempty_radial : (𝓝[>] (0:ℝ)).NeBot := inferInstance

end LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit

open Lean Elab Command
private def newtonConvCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def newtonConvCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (newtonConvCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def newtonConvCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := newtonConvCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_actual_em_newton_convolution" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonConvolution]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emInverseSchwartz,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_em_inverse_schwartz_apply,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_em_spatial_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_em_spatial_newton_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_em_newton_massless_convolution,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_inverse_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_auxiliary_kappa_independent,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_inverse_zero,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_origin_totalization,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_origin_null_measure,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_fourpi_not_repeated,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_original_phase,
    ``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_nonempty_radial]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emInverseSchwartz,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emPacket,
    ``PiLp.volume_preserving_toLp]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_schwartz_integrable]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_packet_integrable,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply]),
    (``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_packet_convolution,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable,
    ``MeasureTheory.tendsto_integral_filter_of_dominated_convergence]),
    (``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_inverse_packet_integrable,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply,
    ``SchwartzMap.integrable]),
    (``LowEnergy.GaussComposite.ActualEMNewtonConvolutionAudit.checked_auxiliary_kappa_independent,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution])]
  for (mouth,required) in direct do newtonConvCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_packet_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution]
  for i in [:testProducers.size] do newtonConvCertRequire env tests[i]! #[testProducers[i]!]
  let all ← newtonConvCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emInverseSchwartz,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emPacket,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emNewtonPacket,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.emNewtonMultiplier,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_newton_schwartz_integrable,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_packet_convolution,
    ``LowEnergy.PreparationVacuumStaticSpatialSource.sourceSpatialPhase,
    ``LowEnergy.PreparationVacuumStaticSpatialSource.sourceSpatialMomentum,
    ``PiLp.volume_preserving_toLp]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let payerTargets := #[`LowEnergy.PreparationPhysicalChannelGreen.greenAmplitude,`LowEnergy.PreparationPhysicalChannelGreen.greenDensity,`LowEnergy.PreparationPhysicalChannelGreen.greenDensity_integrable,`LowEnergy.PreparationPhysicalChannelGreen.greenDensity_bound,`LowEnergy.PreparationPhysicalChannelGreen.greenKernel,`LowEnergy.PreparationPhysicalChannelGreen.greenKernel_integrable,`LowEnergy.PreparationPhysicalChannelGreen.greenKernel_limit,`LowEnergy.PreparationPhysicalChannelGreen.greenKernel_zero]
  let mut payerNames : Array Name := #[]
  for target in payerTargets do
    let found := all.toArray.filter fun name => privateToUserName name == target
    unless found.size == 1 do throwError m!"PRIVATE_PAYER_AMBIGUITY {target} {found}"
    unless (owner found[0]!).any (fun name => name == `SourceChannelFundamentalPotential) do
      throwError m!"WRONG_PRIVATE_PAYER {found[0]!}"
    payerNames := payerNames.push found[0]!
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
  if let some path ← liftIO (IO.getEnv "ALPHA_NEWTON_CONVOLUTION_AUDIT_OUTPUT") then
    let project := all.toArray.filter fun name =>
      match owner name with
      | none => false
      | some m => !(#["Mathlib","Init","Lean","Std","Batteries","Aesop","Qq","Plausible","ImportGraph","ProofWidgets"].any (fun h => h.isPrefixOf m.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("private_payers",toJson (payerNames.map Name.toString)),
      ("owned",toJson (owned.map Name.toString)),("public",toJson (mouths.map Name.toString)),
      ("tests",toJson (tests.map Name.toString)),("nodes",toJson all.size),("opaque_read",toJson opaques),
      ("axioms",toJson axioms),("anchors",toJson (anchors.map Name.toString)),
      ("direct",toJson (direct.map fun p => (p.1.toString,p.2.map Name.toString))),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"ACTUAL_EM_NEWTON_CONVOLUTION_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_actual_em_newton_convolution
#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_inverse_schwartz_apply
#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_schwartz_integrable
#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_spatial_newton_packet_integrable
#print axioms LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution
