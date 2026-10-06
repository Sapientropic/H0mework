import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation
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
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationSharedPoleCarrierAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair
open Stage10 Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open CanonicalGradedSpatialSource SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open SourceQuantumConfigurationHilbert
open YangMills.FullPairing
open scoped BigOperators Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local irreducible] actualRestStatePreparation sourceMovingPoleValues sourcePoleBase


open LowEnergy.PreparationVacuumSharedPoleCarrier
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval ContDiff
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair
open Stage10 Stage10.CanonicalMatter Stage9DEF Stage9DEF.Compatibility
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open CanonicalGradedSpatialSource SourceQuantumFockGauge GaussCoreHilbert GaussFockLift
open SourceQuantumConfigurationHilbert
open YangMills.FullPairing
open scoped BigOperators Matrix InnerProductSpace
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumRestModeCoupling PreparationVacuumPhysicalFeedback
open CanonicalGradedSpatialSource GaussCoreHilbert
open scoped BigOperators Matrix InnerProductSpace
open GaussQuantumMultiplier
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussFockLabel
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge CanonicalGradedSpatialSource
open NativeHistoryGrade
open GaussGradedCompression GaussUnitaryHistory PreparationVacuumPhysicalHalfAxis
open PreparationVacuumRestModeCoupling PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open SourceQuantumConfigurationHilbert PreparationVacuumMovingPoleGaussReturn
open scoped BigOperators Matrix Topology

theorem checked_movingOverlap_values (momentum : PhysicalMomentum) (state : RestStateIndex) :
    (∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • sourceMovingPoleValues 0 origin)=
      sourceMovingPoleValues momentum state := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_values momentum state

theorem checked_movingOverlap_restCoefficient (momentum : PhysicalMomentum) (state rest : RestStateIndex) :
    sourceMovingRestCoefficient momentum state rest=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state*sourceMovingRestCoefficient 0 origin rest := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_restCoefficient momentum state rest

theorem checked_movingOverlap_preparation (momentum : PhysicalMomentum) (state : RestStateIndex) :
    actualMovingPolePreparation momentum state=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • actualMovingPolePreparation 0 origin := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_preparation momentum state

theorem checked_movingOverlap_primal (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePolePrimalCoordinates momentum state=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • sourcePolePrimalCoordinates 0 origin := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_primal momentum state

theorem checked_movingOverlap_coordinates (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleCoordinates momentum state=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • sourcePoleCoordinates 0 origin := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_coordinates momentum state

theorem checked_movingOverlap_creation (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleCreation momentum state=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • sourcePoleCreation 0 origin := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_creation momentum state

theorem checked_movingOverlap_fiber (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePoleFiber momentum state=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • sourcePoleFiber 0 origin := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_fiber momentum state

theorem checked_movingOverlap_prepared (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) (state : RestStateIndex) :
    sourcePolePrepared epsilon precision momentum state=
      ∑origin : RestStateIndex,LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum origin state • sourcePolePrepared epsilon precision 0 origin := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_prepared epsilon precision momentum state

theorem checked_movingOverlap_left_unitary (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) :
    (LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum).conjTranspose*LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum=1 := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_left_unitary epsilon precision momentum

theorem checked_movingOverlap_right_unitary (epsilon : ℝ) (precision : 0<epsilon) (momentum : PhysicalMomentum) :
    LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum*(LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap momentum).conjTranspose=1 := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_right_unitary epsilon precision momentum

theorem checked_sourceTensor_generated (epsilon : ℝ) (precision : 0<epsilon) (pL pR : PhysicalMomentum) (A : H→L[ℂ] H) :
    LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor epsilon precision pL pR A=
      (LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pL).conjTranspose*LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor epsilon precision 0 0 A*LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pR := LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_generated epsilon precision pL pR A

theorem checked_sourceTensor_same_carrier (epsilon : ℝ) (precision : 0<epsilon) (pL pR : PhysicalMomentum) (A : H→L[ℂ] H) :
    LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pL*LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor epsilon precision pL pR A*(LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pR).conjTranspose=
      LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor epsilon precision 0 0 A := LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier epsilon precision pL pR A

theorem checked_actualModeTensor_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) : LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor q pL pR t=
      -((LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pL).conjTranspose*LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor q.epsilon q.precision 0 0 (sourceModeKernel q pL pR t)*LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pR) := LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_generated q pL pR t nonrealL nonrealR

theorem checked_actualModeTensor_same_carrier (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pL*LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor q pL pR t*(LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap pR).conjTranspose=
      -LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor q.epsilon q.precision 0 0 (sourceModeKernel q pL pR t) := LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_same_carrier q pL pR t nonrealL nonrealR

theorem checked_actualC_affine (F : GaussUnitaryHistory.Index) (p : PhysicalMomentum) :
    actualC p F=actualC 0 F+LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocityLinear F p := LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_affine F p

theorem checked_actualC_continuous (F : GaussUnitaryHistory.Index) : Continuous (fun p : PhysicalMomentum=>actualC p F) := LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous F

theorem checked_actualC_difference_price (F : GaussUnitaryHistory.Index) (p k : PhysicalMomentum) :
    ‖actualC p F-actualC k F‖  ≤  ‖LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocity F‖*‖p-k‖ := LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_difference_price F p k

theorem checked_sourceResolvent_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    Continuous (fun p : PhysicalMomentum=>CanonicalPhysicalResolvent.finiteResolvent p F z) := LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_continuous F z nonreal

theorem checked_sourceResolvent_difference_price (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0)
    (p k : PhysicalMomentum) :
    ‖CanonicalPhysicalResolvent.finiteResolvent p F z-CanonicalPhysicalResolvent.finiteResolvent k F z‖  ≤
      (1/|z.im|)^2*‖LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocity F‖*‖p-k‖ := LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_difference_price F z nonreal p k

theorem checked_sourceTime_continuous (F : GaussUnitaryHistory.Index) :
    Continuous (fun pt : PhysicalMomentum×ℝ=>SourceFiniteUnitary.time (actualC pt.1 F) pt.2) := LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTime_continuous F

theorem checked_sourceModeKernel_continuous (q : PhysicalResponsePoint) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>sourceModeKernel q x.1 x.2.1 x.2.2) := LowEnergy.PreparationVacuumSharedPoleCarrier.sourceModeKernel_continuous q nonrealL nonrealR

theorem checked_actualModeTensor_continuous (q : PhysicalResponsePoint) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun x : PhysicalMomentum×PhysicalMomentum×ℝ=>
      LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap x.1*LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor q x.1 x.2.1 x.2.2*(LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap x.2.1).conjTranspose) := LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_continuous q nonrealL nonrealR

theorem checked_movingOverlap_zero : LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap (0:PhysicalMomentum)=1 := LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_zero

theorem checked_actualModeWindow_continuous (q : PhysicalResponsePoint) (lambda : ℂ) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Continuous (fun p : PhysicalMomentum×PhysicalMomentum=>fun left right : RestStateIndex=>
      ∫t in (0:ℝ)..T,PreparationVacuumGaugeSourceInjection.laplaceWeight lambda t*
        (LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap p.1*LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor q p.1 p.2 t*(LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap p.2).conjTranspose) left right) := LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeWindow_continuous q lambda T nonrealL nonrealR

end LowEnergy.PreparationSharedPoleCarrierAudit
elab (name := H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier.auditCommand) "#audit_moving_pole_gauss_return" : command => do
  let env ← getEnv
  let cache ← liftIO (IO.mkRef ({} : NameMap (Array Name)))
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor,
    `H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_values,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_restCoefficient,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_preparation,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_primal,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_coordinates,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_creation,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_fiber,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_prepared,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_left_unitary,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_right_unitary,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_generated,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_generated,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_same_carrier,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceMomentumLinear,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocityLinear,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_affine,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocity,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_difference_price,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_continuous,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_difference_price,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTime_continuous,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceModeKernel_continuous,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_continuous,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_zero,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeWindow_continuous]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_values,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_restCoefficient,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_preparation,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_primal,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_coordinates,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_creation,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_fiber,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_prepared,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_left_unitary,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_right_unitary,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceTensor_generated,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceTensor_same_carrier,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeTensor_generated,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeTensor_same_carrier,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualC_affine,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualC_continuous,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualC_difference_price,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceResolvent_continuous,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceResolvent_difference_price,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceTime_continuous,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceModeKernel_continuous,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeTensor_continuous,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_zero,
    ``LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeWindow_continuous]
  let roots := owned ++ tests.toList
  let closure ← liftIO (completeClosure env cache roots)
  let anchors := #[``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceMomentumLinear,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocityLinear,
    ``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocity]
  for name in anchors do
    unless closure.contains name do throwError m!"MISSING_SOURCE {name}"
  let consumers := #[(``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_restCoefficient,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_values),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_preparation,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_restCoefficient),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_primal,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_preparation),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_coordinates,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_primal),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_creation,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_coordinates),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_fiber,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_creation),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_prepared,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_fiber),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_left_unitary,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_prepared),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_right_unitary,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_left_unitary),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_generated,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_prepared),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_generated),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier,``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_right_unitary),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_generated,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_generated),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_same_carrier,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_affine,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocityLinear),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_affine),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_difference_price,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_affine),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_difference_price,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_difference_price),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTime_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceModeKernel_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTime_continuous),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceModeKernel_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_continuous),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_same_carrier),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.sourceModeKernel_continuous),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeWindow_continuous,``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_continuous),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_values,``LowEnergy.PreparationVacuumElectromagneticIdentity.sourceMovingPole_complete),
    (``LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_generated,``LowEnergy.PreparationVacuumRestModeCoupling.sourceModeCurrent_generated)]
  for (mouth, producer) in consumers do
    let reached ← liftIO (completeClosure env cache [mouth])
    unless reached.contains producer do throwError m!"UNCONSUMED_SOURCE {mouth}: {producer}"
  let (nodes, opaques, axioms) ← checkClosure env cache roots
  if let some path ← liftIO (IO.getEnv "ALPHA_SHARED_POLE_CARRIER_OUTPUT") then
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
  logInfo m!"SHARED_POLE_CARRIER_PASS public={mouths.size} all_owned={owned.length} tests={tests.size} nodes={nodes} opaque_all_read={opaques} axioms={axioms}"

#audit_moving_pole_gauss_return
