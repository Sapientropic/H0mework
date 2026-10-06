import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReaderMomentum
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor
import Lean.Elab.Command
import Lean.Util.FoldConsts
open Lean Elab Command
private def usedConstants (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    deps := deps ++ value.getUsedConstants
  match info with
  | .inductInfo value => deps := deps ++ value.ctors.toArray
  | .recInfo value =>
      for rule in value.rules do deps := deps ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return deps

private def completeClosure (env : Environment) (cache : IO.Ref (NameMap (Array Name)))
    (roots : List Name) : IO NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      seen := seen.insert name
      let memo ← cache.get
      let children ← match memo.find? name with
        | some deps => pure deps
        | none => do
          let deps := match env.checked.get.find? name with
            | some info => usedConstants info
            | none => #[]
          cache.modify (fun old => old.insert name deps)
          pure deps
      pending := children.toList ++ pending
  return seen

private def checkClosure (env : Environment) (cache : IO.Ref (NameMap (Array Name))) (roots : List Name) : CommandElabM (Nat × Nat × Nat) := do
  let closure ← liftIO (completeClosure env cache roots)
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut opaqueCount := 0
  let mut axiomCount := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN_NODE {name}"
    if info.isUnsafe then throwError m!"UNSAFE_NODE {name}"
    if info.isPartial then throwError m!"PARTIAL_NODE {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD_VALUE {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if let .axiomInfo _ := info then
      axiomCount := axiomCount + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  let forbidden := #[
    `SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
    `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
    `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
    `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed]
  for name in forbidden do
    if closure.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  return (closure.size, opaqueCount, axiomCount)





set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationFullPoleContinuationAudit
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumGradedTransport
open PreparationVacuumYukawaTransport PreparationVacuumPhysicalHalfAxis
open PreparationVacuumSharedPoleCarrier PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open scoped Topology
local instance : NormedAlgebra ℝ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (H→L[ℂ] H):=NormedAlgebra.restrictScalars ℚ ℂ _

attribute [local irreducible] CanonicalPhysicalSpatial.physicalAction actualC actualA jointGenerator jointResolvent physicalTime


open LowEnergy.PreparationVacuumFullPoleContinuation
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval ContDiff
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumGradedTransport
open PreparationVacuumYukawaTransport PreparationVacuumPhysicalHalfAxis
open PreparationVacuumSharedPoleCarrier PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open scoped Topology
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy FullQuantum.StateGreen
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussQuantumMultiplier
open CanonicalGradedSpatialSource PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActualFieldQuantization PreparationVacuumGaugeSourceInjection
open PreparationVacuumActionFieldLift PreparationVacuumSourceActionJets PreparationVacuumMixedFieldReturn
open SourceQuantumFockGauge SourceQuantumConfigurationHilbert PreparationVacuumFullFieldRiesz
open MeasureTheory
open scoped BigOperators Topology Matrix
open PreparationVacuumActionFieldLift
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumMixedPrincipal
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator

theorem checked_sourcePhysicalSpan_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    physicalSpan p F=physicalSpan k F := LowEnergy.PreparationVacuumFullPoleContinuation.sourcePhysicalSpan_momentum p k F

theorem checked_sourceFiniteSet_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    finiteSourceSet p F=finiteSourceSet k F := LowEnergy.PreparationVacuumFullPoleContinuation.sourceFiniteSet_momentum p k F

theorem checked_sourceRetainer_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    finiteRetainer p F=finiteRetainer k F := LowEnergy.PreparationVacuumFullPoleContinuation.sourceRetainer_momentum p k F

theorem checked_actualA_momentum (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    actualA p F=actualA k F := LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum p k F

theorem checked_actualJointGenerator_momentum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator p F z 0=actualC p F+actualA 0 F-z • 1 := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_momentum p F z

theorem checked_actualJointGenerator_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) :
    Continuous (fun p : PhysicalMomentum=>jointGenerator p F z 0) := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_continuous F z

theorem checked_actualJointResolvent_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    Continuous (fun p : PhysicalMomentum=>jointResolvent p F z 0) := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous F z nonreal

theorem checked_actualJointTime_continuous (F : GaussUnitaryHistory.Index) :
    Continuous (fun pt : PhysicalMomentum×ℝ=>physicalTime pt.1 F pt.2 0) := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_continuous F

theorem checked_actualJointTime_source_price (F : GaussUnitaryHistory.Index) (p : PhysicalMomentum) (t : ℝ) :
    ‖physicalTime p F t 0‖ ≤ actualGrowth 0 F |t| := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_source_price F p t

theorem checked_rawForm_momentum_continuous (reader : Field289) (a b : QuantumTest) :
    Continuous (fun p : PhysicalMomentum=>rawForm reader p a b 0) := LowEnergy.PreparationVacuumFullPoleContinuation.rawForm_momentum_continuous reader a b

theorem checked_rawReader_momentum_continuous (reader : Field289) (F : GaussUnitaryHistory.Index) :
    Continuous (fun p : PhysicalMomentum=>rawReader reader p F 0) := LowEnergy.PreparationVacuumFullPoleContinuation.rawReader_momentum_continuous reader F

theorem checked_actualJointKernel_original (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    fiveKernel (fieldUnit i) pR (pL-pR) q.F q.z q.w t 0=LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel q pL pR t i := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_original q pL pR t i

theorem checked_returnedCurrentTensor_actual (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor q pL pR t i=
      movingOverlap pL*LowEnergy.PreparationVacuumFullPoleContinuation.actualCurrentTensor q pL pR t i*(movingOverlap pR).conjTranspose := LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_actual q pL pR t i

theorem checked_actualJointKernel_continuous (q : PhysicalResponsePoint) (i : Fin 289)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel q x.1 x.2.1 x.2.2 i) := LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous q i nonrealL nonrealR

theorem checked_returnedCurrentTensor_continuous (q : PhysicalResponsePoint) (i : Fin 289)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor q x.1 x.2.1 x.2.2 i) := LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_continuous q i nonrealL nonrealR

theorem checked_returnedCurrentWindow_actual (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow q pL pR l r lambda T i=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        (movingOverlap pL*LowEnergy.PreparationVacuumFullPoleContinuation.actualCurrentTensor q pL pR t i*(movingOverlap pR).conjTranspose) l r := LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_actual q pL pR l r lambda T i

theorem checked_returnedCurrentWindow_tensor (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (l r : RestStateIndex)
    (lambda : ℂ) (T : ℝ) (i : Fin 289) :
    LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow q pL pR l r lambda T i=
      (movingOverlap pL*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCurrent q pL pR a b lambda T i)*(movingOverlap pR).conjTranspose) l r := LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_tensor q pL pR l r lambda T i

theorem checked_returnedCurrentWindow_continuous (q : PhysicalResponsePoint) (l r : RestStateIndex) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow q p.1 p.2 l r lambda T) := LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_continuous q l r lambda T nonrealL nonrealR

theorem checked_returnedCurrentWindow_zero (q : PhysicalResponsePoint) (l r : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow q 0 0 l r lambda T=actualCurrent q 0 0 l r lambda T := LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_zero q l r lambda T

theorem checked_actualAxisWindow_tendsto (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow q l r T) staticApproach (𝓝 (actualCurrent q 0 0 l r 0 T)) := LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto q l r T nonrealL nonrealR

theorem checked_actualAxisField_whole (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) :
    originalJacobi (staticMomentum κ.val)*ᵥ LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField q l r T κ=
      LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow q l r T κ-originalRowLift (staticMomentum κ.val)*ᵥ
        (nullProjection*ᵥ (originalReadback (staticMomentum κ.val)*ᵥ LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow q l r T κ)) := LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_whole q l r T κ

theorem checked_actualAxisField_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField q l r T κ) staticApproach
      (𝓝 (staticResidue (actualCurrent q 0 0 l r 0 T))) := LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_residue q l r T nonrealL nonrealR

theorem checked_actualAxisField_coupled_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField q l r T κ) staticApproach
      (𝓝 (fullNativeOrigin*ᵥ
        (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*actualOriginWeight q 0 0 l r 0 T)+
         Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*actualOriginWeight q 0 0 l r 0 T)))) := LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue q l r T nonrealL nonrealR

end LowEnergy.PreparationFullPoleContinuationAudit
elab (name := H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation.auditCommand) "#audit_moving_pole_gauss_return" : command => do
  let env ← getEnv
  let cache ← liftIO (IO.mkRef ({} : NameMap (Array Name)))
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReaderMomentum,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[``LowEnergy.PreparationVacuumFullPoleContinuation.sourcePhysicalSpan_momentum,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.sourceFiniteSet_momentum,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.sourceRetainer_momentum,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_momentum,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_source_price,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.sourceReaderMomentumForm,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.rawForm_momentum_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.rawReader_momentum_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_original,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualCurrentTensor,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_actual,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_actual,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_tensor,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_continuous,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_zero,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_whole,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_residue,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[``LowEnergy.PreparationFullPoleContinuationAudit.checked_sourcePhysicalSpan_momentum,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_sourceFiniteSet_momentum,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_sourceRetainer_momentum,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualA_momentum,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointGenerator_momentum,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointGenerator_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointResolvent_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointTime_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointTime_source_price,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_rawForm_momentum_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_rawReader_momentum_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointKernel_original,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentTensor_actual,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointKernel_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentTensor_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_actual,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_tensor,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_continuous,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_zero,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisWindow_tendsto,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisField_whole,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisField_residue,
    ``LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisField_coupled_residue]
  let roots := owned ++ tests.toList
  let closure ← liftIO (completeClosure env cache roots)
  let anchors := #[``LowEnergy.PreparationVacuumFullPoleContinuation.sourceReaderMomentumForm,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualCurrentTensor,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField]
  for name in anchors do
    unless closure.contains name do throwError m!"MISSING_SOURCE {name}"
  let consumers := #[(``LowEnergy.PreparationVacuumFullPoleContinuation.sourceFiniteSet_momentum,``LowEnergy.PreparationVacuumFullPoleContinuation.sourcePhysicalSpan_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.sourceRetainer_momentum,``LowEnergy.PreparationVacuumFullPoleContinuation.sourceFiniteSet_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum,``LowEnergy.PreparationVacuumFullPoleContinuation.sourceRetainer_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_momentum,``LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_source_price,``LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.rawForm_momentum_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.sourceReaderMomentumForm),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.rawReader_momentum_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.rawForm_momentum_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_actual,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_original),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.rawReader_momentum_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_actual,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_actual),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_tensor,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_actual),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_continuous,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_zero,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_actual),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_zero),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_residue,``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue,``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_residue),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_actual,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_whole,``LowEnergy.PreparationVacuumStaticPoleResponse.staticNativeField_whole),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_residue,``LowEnergy.PreparationVacuumStaticPoleResponse.staticNativeField_residue),
    (``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue,``LowEnergy.PreparationVacuumStaticPoleResponse.actualCurrent_staticResidue)]
  for (mouth, producer) in consumers do
    let reached ← liftIO (completeClosure env cache [mouth])
    unless reached.contains producer do throwError m!"UNCONSUMED_SOURCE {mouth}: {producer}"
  let (nodes, opaques, axioms) ← checkClosure env cache roots
  if let some path ← liftIO (IO.getEnv "ALPHA_FULL_POLE_CONTINUATION_OUTPUT") then
    let project := closure.toArray.filter fun name =>
      match owner name with
      | none => false
      | some moduleName => !(#["Mathlib", "Init", "Lean", "Std", "Batteries", "Aesop", "Qq", "Plausible", "ImportGraph", "ProofWidgets"].any
          (fun head => head.isPrefixOf moduleName.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)), ("public_roots",toJson mouths.size),
      ("nodes",toJson nodes), ("opaque_all_read",toJson opaques), ("axioms",toJson axioms),
      ("anchors",toJson (anchors.map Name.toString)),
      ("consumers",toJson (consumers.map fun p => (p.1.toString,p.2.toString))),
      ("actual_tests",toJson (tests.map Name.toString)),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"FULL_POLE_CONTINUATION_PASS public={mouths.size} all_owned={owned.length} tests={tests.size} nodes={nodes} opaque_all_read={opaques} axioms={axioms}"

#audit_moving_pole_gauss_return
