import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice
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
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPoleConstraintReturnAudit
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalConstraint114 PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumFieldConstraintResponse
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator

private theorem external_field_return (A : Matrix (Fin 289) (Fin 289) ℂ)
    (U V : Matrix RestStateIndex RestStateIndex ℂ) (J : RestStateIndex→RestStateIndex→Fin 289→ℂ)
    (l r : RestStateIndex) (i : Fin 289) :
    (A*ᵥ(fun j=>(U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>J a b j)*V) l r)) i=
      (U*(show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>(A*ᵥJ a b) i)*V) l r:=by
  simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring


open LowEnergy.PreparationVacuumPoleConstraintReturn
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval ContDiff
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalConstraint114 PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumFieldConstraintResponse
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalConstraint114 PreparationVacuumPhysicalZeroRead
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalModeContact PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift
open Filter MeasureTheory
open scoped Topology BigOperators Matrix Matrix.Norms.Operator
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumPhysicalModeContact PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.Operator

theorem checked_axisCosource_actual (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (κ : staticDomain) (i : Fin 289) :
    LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource q l r T κ i=
      (movingOverlap (sourceAxisLeft 0 κ.val)*
        (show Matrix RestStateIndex RestStateIndex ℂ from fun a b=>actualCosource q (sourceAxisLeft 0 κ.val) 0 a b 0 T i)*
        (movingOverlap 0).conjTranspose) l r := LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_actual q l r T κ i

theorem checked_axisCosource_tendsto (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource q l r T) staticApproach (𝓝 (actualCosource q 0 0 l r 0 T)) := LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_tendsto q l r T nonrealL nonrealR

theorem checked_axisNullCosource_tendsto (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource q l r T) staticApproach (𝓝 (nullProjection*ᵥ actualCosource q 0 0 l r 0 T)) := LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource_tendsto q l r T nonrealL nonrealR

theorem checked_actualOriginWeight_cosource114 (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) :
    actualOriginWeight q 0 0 l r 0 T= -(actualCosource q 0 0 l r 0 T 114) := LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_cosource114 q l r T

theorem checked_actualAxisField_constraint_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • actualAxisField q l r T κ) staticApproach
      (𝓝 (fullNativeOrigin*ᵥ
        (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*(-actualCosource q 0 0 l r 0 T 114))+
         Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*(-actualCosource q 0 0 l r 0 T 114))))) := LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_constraint_residue q l r T nonrealL nonrealR

theorem checked_actualAxisField_compatibility (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) (κ : staticDomain) :
    originalJacobi (staticMomentum κ.val)*ᵥ actualAxisField q l r T κ=actualAxisWindow q l r T κ ↔
      LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource q l r T κ=0 := LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_compatibility q l r T κ

theorem checked_actualOriginWeight_native (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    actualOriginWeight q 0 0 l r 0 T=LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow q l r T-LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow q l r T := LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native q l r T nonrealL nonrealR

theorem checked_originCosource114_actualWard (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    actualCosource q 0 0 l r 0 T 114=LowEnergy.PreparationVacuumPoleConstraintReturn.originWardBoundary q l r T := LowEnergy.PreparationVacuumPoleConstraintReturn.originCosource114_actualWard q l r T nonrealL nonrealR

theorem checked_origin_native_Ward_balance (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow q l r T-LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow q l r T= -LowEnergy.PreparationVacuumPoleConstraintReturn.originWardBoundary q l r T := LowEnergy.PreparationVacuumPoleConstraintReturn.origin_native_Ward_balance q l r T nonrealL nonrealR

theorem checked_actualAxisField_native_residue (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun κ : staticDomain=>(-(κ.val:ℂ)^2) • actualAxisField q l r T κ) staticApproach
      (𝓝 (fullNativeOrigin*ᵥ
        (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*(LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow q l r T-LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow q l r T))+
         Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*(LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow q l r T-LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow q l r T))))) := LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_native_residue q l r T nonrealL nonrealR

theorem checked_sourceDeviationKernel_price (q : PhysicalResponsePoint) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖sourceDeviationKernel q 0 0 t‖ ≤ LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice q := LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationKernel_price q t nonrealL nonrealR

theorem checked_sourceDeviationRead_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖sourcePoleRead q.epsilon q.precision 0 0 l r (sourceDeviationKernel q 0 0 t)‖ ≤ LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice q := LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationRead_price q l r t nonrealL nonrealR

theorem checked_configurationDeviationWindow_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow q l r T‖ ≤ LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice q*|T| := LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow_price q l r T nonrealL nonrealR

theorem checked_actualOriginWeight_native_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖actualOriginWeight q 0 0 l r 0 T-LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow q l r T‖ ≤ LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice q*|T| := LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native_price q l r T nonrealL nonrealR

theorem checked_actualResidue_sourcePoleVector (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) :
    staticResidue (actualCurrent q 0 0 l r 0 T)=actualOriginWeight q 0 0 l r 0 T • LowEnergy.PreparationVacuumPoleConstraintReturn.sourcePoleVector := LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_sourcePoleVector q l r T

theorem checked_actualResidue_native_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖staticResidue (actualCurrent q 0 0 l r 0 T)-LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow q l r T • LowEnergy.PreparationVacuumPoleConstraintReturn.sourcePoleVector‖ ≤
      LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice q*|T| *‖LowEnergy.PreparationVacuumPoleConstraintReturn.sourcePoleVector‖ := LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_native_price q l r T nonrealL nonrealR

end LowEnergy.PreparationPoleConstraintReturnAudit
elab (name := H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn.auditCommand) "#audit_moving_pole_gauss_return" : command => do
  let env ← getEnv
  let cache ← liftIO (IO.mkRef ({} : NameMap (Array Name)))
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_actual,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_tendsto,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource_tendsto,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_cosource114,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_constraint_residue,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_compatibility,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.originWardBoundary,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.originCosource114_actualWard,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.origin_native_Ward_balance,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_native_residue,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationKernel_price,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationRead_price,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow_price,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native_price,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.sourcePoleVector,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_sourcePoleVector,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_native_price]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[``LowEnergy.PreparationPoleConstraintReturnAudit.checked_axisCosource_actual,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_axisCosource_tendsto,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_axisNullCosource_tendsto,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualOriginWeight_cosource114,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualAxisField_constraint_residue,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualAxisField_compatibility,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualOriginWeight_native,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_originCosource114_actualWard,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_origin_native_Ward_balance,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualAxisField_native_residue,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_sourceDeviationKernel_price,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_sourceDeviationRead_price,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_configurationDeviationWindow_price,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualOriginWeight_native_price,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualResidue_sourcePoleVector,
    ``LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualResidue_native_price]
  let roots := owned ++ tests.toList
  let closure ← liftIO (completeClosure env cache roots)
  let anchors := #[``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.originWardBoundary,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice,
    ``LowEnergy.PreparationVacuumPoleConstraintReturn.sourcePoleVector]
  for name in anchors do
    unless closure.contains name do throwError m!"MISSING_SOURCE {name}"
  let consumers := #[(``LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource_tendsto,``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_tendsto),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_constraint_residue,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_cosource114),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.origin_native_Ward_balance,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.origin_native_Ward_balance,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_cosource114),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.origin_native_Ward_balance,``LowEnergy.PreparationVacuumPoleConstraintReturn.originCosource114_actualWard),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_native_residue,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationRead_price,``LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationKernel_price),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow_price,``LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationRead_price),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native_price,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native_price,``LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow_price),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_native_price,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_sourcePoleVector),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_native_price,``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native_price),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_actual,``LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_tensor),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_tendsto,``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_constraint_residue,``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_compatibility,``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_whole),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native,``LowEnergy.PreparationVacuumPhysicalModeContact.sourceActualMode_contact_deviation),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.originCosource114_actualWard,``LowEnergy.PreparationVacuumPhysicalN1WardCollapse.sourceActualCosource114_N1WardBoundary),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_native_residue,``LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue),
    (``LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_sourcePoleVector,``LowEnergy.PreparationVacuumStaticPoleResponse.actualCurrent_staticResidue)]
  for (mouth, producer) in consumers do
    let reached ← liftIO (completeClosure env cache [mouth])
    unless reached.contains producer do throwError m!"UNCONSUMED_SOURCE {mouth}: {producer}"
  let (nodes, opaques, axioms) ← checkClosure env cache roots
  if let some path ← liftIO (IO.getEnv "ALPHA_POLE_CONSTRAINT_RETURN_OUTPUT") then
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
  logInfo m!"POLE_CONSTRAINT_RETURN_PASS public={mouths.size} all_owned={owned.length} tests={tests.size} nodes={nodes} opaque_all_read={opaques} axioms={axioms}"

#audit_moving_pole_gauss_return
