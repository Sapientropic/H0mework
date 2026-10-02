import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPatches.TerminalRecovery
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.TerminalFormation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms MotherExactPrograms
open MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem every_terminal_request_section (parent : M) (value : RequestValue)
    (formed : formPatchRequests parent = some value) (desired : TerminalRequests (requestProgramme value)) :
    ∃ material : M, formAllRequests material = some ⟨value, desired⟩ := by
  let programme := requestProgramme value
  let programmeFormed := requests_programmes_formed parent value formed
  let coordinates := sourceCoordinates (requestParent parent) programme programmeFormed
  let ledger := ledgerCoordinates (requestParent parent) programme programmeFormed
  let eventCode := terminalAddresses (requestParent parent) programme programmeFormed
  let bodies := fun point => TerminalRequestEncoding.body programme.2.2.1 point (desired point)
  obtain ⟨bodyMaterial, hb⟩ := (MotherArenaHigher.read_surjective rank)
    (TerminalBodyEncoding.reader programme.2.2.1 coordinates ledger eventCode bodies)
  obtain ⟨indexMaterial, hi⟩ := (MotherArenaHigher.read_surjective rank)
    (TerminalRequestEncoding.indexReader programme.2.2.1 coordinates ledger desired)
  let kinds : B → ℕ → ℝ := fun code _ => Function.extend coordinates.occurrence
    (fun point => (TerminalRequestEncoding.kind programme.2.2.1 point (desired point) : ℝ)) (fun _ => 0) code
  obtain ⟨kindMaterial, hk⟩ := (MotherArenaHigher.read_surjective rank) kinds
  refine ⟨(MotherArenaHigher.pack rank) (parent, (MotherArenaHigher.pack rank) (bodyMaterial,
    (MotherArenaHigher.pack rank) (indexMaterial, kindMaterial))), ?_⟩
  unfold formAllRequests
  simp only [MotherArenaHigher.split_pack]
  unfold formAllRequestParts
  apply Option.pbind_eq_some_iff.mpr
  refine ⟨value, formed, ?_⟩
  let checked := TerminalBodyEncoding.checked programme.2.2.1 coordinates ledger eventCode bodies hb
  rw [dif_pos checked]
  apply congrArg (fun requests => some (⟨value, requests⟩ : AllRequestValue))
  funext point
  change terminalPatchOfKind? programme.2.2.1 coordinates ledger indexMaterial point
    (generatedTerminalBodies programme.2.2.1 coordinates ledger eventCode bodyMaterial checked point)
    (Nat.floor ((MotherArenaHigher.read rank) kindMaterial (coordinates.occurrence point) 0)) = desired point
  rw [TerminalBodyEncoding.body_eq programme.2.2.1 coordinates ledger eventCode bodies hb point, hk]
  dsimp only [kinds]
  rw [coordinates.occurrence.injective.extend_apply, Nat.floor_natCast]
  exact TerminalRequestEncoding.recovered programme.2.2.1 coordinates ledger desired hi point

/-- One material retains the complete programme and both original patch
request sections, including whole constructor values and all stored rows. -/
theorem every_complete_patch_requests (parent : M) (value : WriteProgramValue)
    (formed : MotherArenaExact.formWritePrograms parent = some value) (continuing : OriginalPatchRequests value)
    (terminal : TerminalRequests value) :
    ∃ material : M, ∃ inventories : FiniteSection value.2.2.2.2,
      ∃ selections : ∀ context, LedgerTransportedRemainderCoverageAt (inventories context),
        formAllRequests material = some ⟨⟨⟨⟨value, inventories⟩, selections⟩, continuing⟩, terminal⟩ := by
  obtain ⟨requestMaterial, inventories, selections, requestFormed⟩ := every_patch_request_section parent value formed continuing
  obtain ⟨material, result⟩ := every_terminal_request_section requestMaterial
    ⟨⟨⟨value, inventories⟩, selections⟩, continuing⟩ requestFormed terminal
  exact ⟨material, inventories, selections, result⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPatches
