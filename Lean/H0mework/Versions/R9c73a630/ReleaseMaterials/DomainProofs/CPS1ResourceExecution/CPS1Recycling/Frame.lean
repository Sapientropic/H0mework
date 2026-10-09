import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Recycling
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- The coding coordinate and the paid stock are restrictions of this one model occurrence. -/
structure Frame where
  messageTemplate : Bases
  peptide : Peptide
  program : List Reaction
  native : Execution

/-- RNA syntax is retained; cap, modifications, UTR and actual transcription are separate source residuals. -/
def frameFromCoding? (coding : Bases) : Option Frame := do
  let peptide ← CPS1EndogenousTranslation.peptideFromCoding? coding
  if peptide.1 = .M then
    let program := CPS1InitiationTermination.UnifiedBoundary.compile peptide.2
    pure ⟨coding,peptide,program,execute program (CPS1InitiationTermination.NativeComplete.rawFuel peptide.2)⟩
  else none

def sourceFrame (edits : Target.Edits) (water additional : Nat) : Option Frame := do
  let coding ← CPS1Deamination.ContinuedCoding.continuedCoding edits water additional
  frameFromCoding? coding

def Frame.coarseStock (frame : Frame) : Stock := frame.native.stock

def Frame.postSpecies (frame : Frame) : CPS1ResourceExecution.Species :=
  CPS1InitiationTermination.NativeComplete.terminalComplex frame.peptide.2

theorem frame_follows_source_program (coding : Bases) (frame : Frame)
    (generated : frameFromCoding? coding = some frame) :
    frame.messageTemplate = coding ∧
    frame.program = CPS1InitiationTermination.UnifiedBoundary.compile frame.peptide.2 ∧
    frame.native = execute frame.program (CPS1InitiationTermination.NativeComplete.rawFuel frame.peptide.2) ∧
    frame.native.missing = none ∧ frame.postSpecies ∈ frame.coarseStock := by
  unfold frameFromCoding? at generated
  cases decoded : CPS1EndogenousTranslation.peptideFromCoding? coding with
  | none => simp [decoded] at generated
  | some peptide =>
    simp only [decoded] at generated
    change (if peptide.1 = .M then some
      (⟨coding,peptide,CPS1InitiationTermination.UnifiedBoundary.compile peptide.2,
        execute (CPS1InitiationTermination.UnifiedBoundary.compile peptide.2)
          (CPS1InitiationTermination.NativeComplete.rawFuel peptide.2)⟩ : Frame) else none) = some frame at generated
    split at generated
    · simp only [Option.some.injEq] at generated
      subst frame
      have completed := CPS1InitiationTermination.NativeComplete.canonical_raw_complete peptide.2
      have membership : CPS1InitiationTermination.NativeComplete.terminalComplex peptide.2 ∈
          CPS1InitiationTermination.NativeComplete.finalProducts peptide.2 := by
        simp [CPS1InitiationTermination.NativeComplete.finalProducts]
      exact ⟨rfl,rfl,rfl,completed.2.2.1,completed.2.2.2.mem_iff.mpr membership⟩
    · simp at generated

theorem source_coding_generated (edits : Target.Edits) (water additional : Nat) :
    CPS1Deamination.ContinuedCoding.continuedCoding edits water additional =
      some (Target.coding (CPS1Deamination.CodingReadout.paidEdits edits (water+additional))) := by
  rw [CPS1Deamination.ContinuedCoding.continued_coding_actual_stock]
  unfold CPS1Deamination.CodingReadout.actualCoding CPS1Deamination.ExecutionReadout.sourceExecution
  rw [(CPS1Deamination.ExecutionReadout.source_prefix_actual_readout edits (water+additional)).1]
  simp only [Option.map_some,Function.comp_apply]
  rw [CPS1Deamination.CodingReadout.source_prefix_genomic_readout]
  exact congrArg some (CPS1Deamination.CodingReadout.source_coding_embedding _ _ _)

theorem actual_peptide_from_coding (edits : Target.Edits) (water additional : Nat) :
    CPS1EndogenousTranslation.peptideFromCoding?
      (Target.coding (CPS1Deamination.CodingReadout.paidEdits edits (water+additional))) =
      some (CPS1EndogenousTranslation.selectedPeptide edits water additional) := by
  have generated := CPS1EndogenousTranslation.actual_peptide_generated edits water additional
  have factors : CPS1EndogenousTranslation.continuedPeptide edits water additional = (do
      let coding ← CPS1Deamination.ContinuedCoding.continuedCoding edits water additional
      CPS1EndogenousTranslation.peptideFromCoding? coding) := by
    unfold CPS1EndogenousTranslation.continuedPeptide
      CPS1Deamination.ContinuedCoding.continuedStopChain CPS1EndogenousTranslation.peptideFromCoding?
    simp only [bind_assoc]
  rw [factors,source_coding_generated] at generated
  exact generated

theorem source_frame_generated (edits : Target.Edits) (water additional : Nat) :
    sourceFrame edits water additional = some
      (⟨Target.coding (CPS1Deamination.CodingReadout.paidEdits edits (water+additional)),
        CPS1EndogenousTranslation.selectedPeptide edits water additional,
        CPS1InitiationTermination.UnifiedBoundary.compile
          (CPS1EndogenousTranslation.selectedPeptide edits water additional).2,
        execute (CPS1InitiationTermination.UnifiedBoundary.compile
          (CPS1EndogenousTranslation.selectedPeptide edits water additional).2)
          (CPS1InitiationTermination.NativeComplete.rawFuel
            (CPS1EndogenousTranslation.selectedPeptide edits water additional).2)⟩ : Frame) := by
  rw [sourceFrame,source_coding_generated]
  change frameFromCoding? _ = _
  rw [frameFromCoding?,actual_peptide_from_coding]
  change (if (CPS1EndogenousTranslation.selectedPeptide edits water additional).1 = .M
    then _ else none) = _
  rw [if_pos (CPS1InitiationTermination.UnifiedBoundary.source_selected_initiator edits water additional)]
  rfl


end CPS1Recycling
