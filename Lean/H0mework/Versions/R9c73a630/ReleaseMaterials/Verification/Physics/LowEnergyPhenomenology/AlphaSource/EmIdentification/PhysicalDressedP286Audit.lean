import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedP286Character
import Lean

set_option autoImplicit false
noncomputable section

namespace LowEnergy.DressedP286Audit

open SaturationMonoid.PhysicsCore SU7MotherLieAlgebra SU7MotherGaugeTheory
open SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction StageNineHolonomicField
open StageNineDynamicBreakingVacuum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussHistoryHilbert
open GaussComposite GaussComposite.SourceGraph NamedColorQtNext
open DressedColourYScalarColumns DressedColourYScalarRows DressedColourY
open GaussComposite.ActualDressedSourcePreparation
open PreparationVacuumSourcePreparedResponse
open PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMDressedPreparedRead
open scoped BigOperators Matrix

theorem checked_original_scalar_column (data : P286LieBlockData) (channel : Fin 2)
    (c : Fin 3) :
    exteriorMotherLieAction 4 (p286LieBlockEmbed data) (signedScalarBasis channel c) =
      -(∑ d : Fin 3, ((data.1 : Matrix (Fin 3) (Fin 3) ℂ) c d) •
        signedScalarBasis channel d) :=
  scalar_signed_column data channel c

theorem checked_actual_scalar_row (a : NativeLie) (channel : Fin 2) (c : Fin 3)
    (phi : ScalarCoordinateCarrier) :
    scalarCoefficient channel c
        (scalarMotherLieAction (p286LieBlockEmbed (nativeData a)) phi) =
      -(∑ d : Fin 3, (nativeData a).1.val d c * scalarCoefficient channel d phi) :=
  scalar_action_row a channel c phi

theorem checked_full_car_joint (a : NativeLie) (channel s : Fin 2)
    (phi : ScalarCoordinateCarrier) :
    jointDressedFiber a true channel s phi =
        -(nativeData a).2.2.1 • fiberCreation channel s phi ∧
      jointDressedFiber a false channel s phi =
        (nativeData a).2.2.1 • fiberAnnihilation channel s phi :=
  ⟨joint_dressed_creation a channel s phi, joint_dressed_annihilation a channel s phi⟩

theorem checked_all_colour (A : SU3BlockLieMatrix) (addition : Bool)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    jointDressedFiber (colorNative A) addition channel s phi = 0 :=
  joint_colour_zero A addition channel s phi

theorem checked_all_weak (A : SpecialUnitaryLieMatrix (Fin 2)) (addition : Bool)
    (channel s : Fin 2) (phi : ScalarCoordinateCarrier) :
    jointDressedFiber (p286CoordinateEquiv (0, A, 0)) addition channel s phi = 0 := by
  apply joint_block_zero
  have original : nativeData (p286CoordinateEquiv (0, A, 0)) = (0, A, 0) :=
    p286CoordinateEquiv.symm_apply_apply _
  rw [original]
  rfl

theorem checked_source_completion (a : NativeLie) (addition : Bool)
    (channel s : Fin 2) (f : Profile) :
    jointDressedCompleted a addition channel s f =
      (if addition then -(nativeData a).2.2.1 else (nativeData a).2.2.1) •
        completedLeg addition channel s f :=
  jointDressedCompleted_return a addition channel s f

theorem checked_actual_em_source (epsilon : ℝ) (precision : 0 < epsilon) :
    jointDressedCompleted sourcePhaseGaugeLie true 1 0
        (sourceProfile epsilon precision) = sourceDressedExcitation epsilon precision ∧
      jointDressedCompleted sourcePhaseGaugeLie true 1 0
        (sourceProfile epsilon precision) ≠ 0 ∧
      ‖sourceDressedUnit epsilon precision‖ = 1 :=
  ⟨joint_phase_actual_creation epsilon precision,
    joint_phase_nonzero epsilon precision, source_dressed_unit_norm epsilon precision⟩

theorem checked_actual_y_source (epsilon : ℝ) (precision : 0 < epsilon) :
    jointDressedCompleted nativeY true 1 0 (sourceProfile epsilon precision) =
        -Complex.I • completedLeg true 1 0 (sourceProfile epsilon precision) ∧
      jointDressedCompleted nativeY true 1 0 (sourceProfile epsilon precision) ≠ 0 :=
  joint_nativeY_actual epsilon precision

end LowEnergy.DressedP286Audit
end

open Lean Elab Command

private def dressedP286Children (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def dressedP286Closure (env : Environment) (roots : List Name) :
    CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (dressedP286Children info).toList ++ pending
      seen := seen.insert name
  return seen

elab "#audit_dressed_p286" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`PhysicalDressedScalarColumns, `PhysicalDressedScalarSkew,
    `PhysicalDressedP286Scalar, `H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalDressedP286Character]
  for name in owners do
    unless modules.contains name do throwError m!"MISSING_MODULE {name}"
  let owned := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some index => if owners.contains modules[index.toNat]! then some name else none
    | none => none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.DressedColourYScalarColumns.scalar_basis_wedge,
    ``LowEnergy.DressedColourYScalarColumns.signedScalarBasis,
    ``LowEnergy.DressedColourYScalarColumns.signed_scalar_basis_wedge,
    ``LowEnergy.DressedColourYScalarColumns.scalar_signed_column,
    ``LowEnergy.DressedColourYScalarRows.scalar_complex_pairing,
    ``LowEnergy.DressedColourYScalarRows.scalar_action_complex_smul,
    ``LowEnergy.DressedColourYScalarRows.scalar_action_complex_skew,
    ``LowEnergy.DressedColourY.scalar_action_row,
    ``LowEnergy.DressedColourY.jointDressedFiber,
    ``LowEnergy.DressedColourY.joint_dressed_creation,
    ``LowEnergy.DressedColourY.joint_dressed_annihilation,
    ``LowEnergy.DressedColourY.joint_fiber_return,
    ``LowEnergy.DressedColourY.jointDressedTest,
    ``LowEnergy.DressedColourY.jointDressedTest_return,
    ``LowEnergy.DressedColourY.jointDressedLetter,
    ``LowEnergy.DressedColourY.jointDressedLetter_return,
    ``LowEnergy.DressedColourY.jointDressedCore,
    ``LowEnergy.DressedColourY.jointDressedCore_return,
    ``LowEnergy.DressedColourY.jointDressedCompleted,
    ``LowEnergy.DressedColourY.jointDressedCompleted_core,
    ``LowEnergy.DressedColourY.jointDressedCompleted_return,
    ``LowEnergy.DressedColourY.joint_block_zero,
    ``LowEnergy.DressedColourY.joint_colour_zero,
    ``LowEnergy.DressedColourY.joint_phase_character,
    ``LowEnergy.DressedColourY.joint_phase_completed,
    ``LowEnergy.DressedColourY.joint_phase_actual_creation,
    ``LowEnergy.DressedColourY.joint_actual_nonzero,
    ``LowEnergy.DressedColourY.joint_nativeY_actual,
    ``LowEnergy.DressedColourY.joint_phase_nonzero]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let consumers := #[
    (``LowEnergy.DressedP286Audit.checked_original_scalar_column,
      #[``LowEnergy.DressedColourYScalarColumns.scalar_signed_column]),
    (``LowEnergy.DressedP286Audit.checked_actual_scalar_row,
      #[``LowEnergy.DressedColourY.scalar_action_row]),
    (``LowEnergy.DressedP286Audit.checked_full_car_joint,
      #[``LowEnergy.DressedColourY.joint_dressed_creation,
        ``LowEnergy.DressedColourY.joint_dressed_annihilation]),
    (``LowEnergy.DressedP286Audit.checked_all_colour,
      #[``LowEnergy.DressedColourY.joint_colour_zero]),
    (``LowEnergy.DressedP286Audit.checked_all_weak,
      #[``LowEnergy.DressedColourY.joint_block_zero]),
    (``LowEnergy.DressedP286Audit.checked_source_completion,
      #[``LowEnergy.DressedColourY.jointDressedCompleted_return]),
    (``LowEnergy.DressedP286Audit.checked_actual_em_source,
      #[``LowEnergy.DressedColourY.joint_phase_actual_creation,
        ``LowEnergy.DressedColourY.joint_phase_nonzero,
        ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.DressedP286Audit.checked_actual_y_source,
      #[``LowEnergy.DressedColourY.joint_nativeY_actual])]
  let all ← dressedP286Closure env (owned ++ (consumers.map Prod.fst).toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``SaturationMonoid.PhysicsCore.StageNineHolonomicField.exteriorMotherLieAction,
    ``SaturationMonoid.PhysicsCore.StageNineHolonomicField.scalarMotherLieAction,
    ``SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew,
    ``LowEnergy.NamedColorQtNext.actual_full_native_column,
    ``LowEnergy.GaussNativeMatter.nativeFull,
    ``LowEnergy.GaussCARHistory.createFiber,
    ``LowEnergy.GaussCARHistory.annihilateFiber,
    ``LowEnergy.GaussComposite.scalarCoefficient,
    ``LowEnergy.GaussComposite.fiberCreation,
    ``LowEnergy.GaussComposite.fiberAnnihilation,
    ``LowEnergy.PreparationPhysicalPhaseGaugeRealization.sourcePhaseGaugeLie,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedExcitation,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.DressedColourYScalarRows.scalar_action_complex_skew,
      #[``SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew]),
    (``LowEnergy.DressedColourY.scalar_action_row,
      #[``LowEnergy.DressedColourYScalarColumns.scalar_signed_column,
        ``LowEnergy.DressedColourYScalarRows.scalar_action_complex_skew]),
    (``LowEnergy.DressedColourY.joint_dressed_creation,
      #[``LowEnergy.DressedColourY.scalar_action_row,
        ``LowEnergy.NamedColorQtNext.actual_full_native_column]),
    (``LowEnergy.DressedColourY.joint_dressed_annihilation,
      #[``LowEnergy.DressedColourY.scalar_action_row,
        ``LowEnergy.NamedColorQtNext.actual_full_native_column]),
    (``LowEnergy.DressedColourY.jointDressedTest_return,
      #[``LowEnergy.DressedColourY.joint_fiber_return]),
    (``LowEnergy.DressedColourY.jointDressedCompleted_return,
      #[``LowEnergy.DressedColourY.jointDressedCore_return]),
    (``LowEnergy.DressedColourY.joint_phase_actual_creation,
      #[``LowEnergy.DressedColourY.joint_phase_completed,
        ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_return]),
    (``LowEnergy.DressedColourY.joint_actual_nonzero,
      #[``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero])]
  for (mouth, required) in direct ++ consumers do
    let closed ← dressedP286Closure env [mouth]
    for name in required do
      unless closed.contains name do throwError m!"UNCONSUMED_DIRECT {mouth} {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
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
      unless allowed.contains axiomName do
        throwError m!"UNAUTHORIZED_ROOT_AXIOM {name} {axiomName}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  for name in modules do
    if (name.toString.toLower.splitOn ".").contains "scratch" then
      throwError m!"SCRATCH_IMPORT {name}"
  logInfo m!"DRESSED_P286_PASS public={mouths.size} owned={owned.length} nodes={all.size} anchors={anchors.size} direct={direct.size} consumers={consumers.size} opaque_all_read={opaqueCount} axioms={axioms} unknown=0 unsafe=0 partial=0"

#audit_dressed_p286
