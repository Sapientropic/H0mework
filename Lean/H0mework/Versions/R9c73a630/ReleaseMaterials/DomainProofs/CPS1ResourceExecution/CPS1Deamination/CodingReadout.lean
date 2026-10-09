import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.ExecutionReadout

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Deamination.CodingReadout
open CPS1ResourceExecution
open ExecutionReadout
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

/-- Same-source coordinate embedding of the actually read local word. -/
def codingFromGenomic (genomic : Bases) : Bases :=
  (Target.referenceCoding.set (Source.codingPosition-1) .thymine).take Target.localStart ++
    ((genomic.drop (Target.targetOffset-42)).take 78 ++
      (Target.referenceCoding.set (Source.codingPosition-1) .thymine).drop (Target.localStart+78))

def actualCoding (edits : Target.Edits) (water : Nat) : Option Bases :=
  (readDNA (sourceExecution edits water).stock).map (codingFromGenomic ∘ CPS1Deamination.Source.plusReadout)

def actualStopChain (edits : Target.Edits) (water : Nat) : Option (List String) := do
  let coding ← actualCoding edits water
  let translated ← Coding.coding? coding
  Coding.translate Coding.code translated

theorem source_coding_embedding (third eighth ninth : Bool) :
    codingFromGenomic (Target.genomic ⟨third,eighth,ninth⟩) = Target.coding ⟨third,eighth,ninth⟩ := by
  cases third <;> cases eighth <;> cases ninth <;> decide +kernel

theorem complete_actual_coding (edits : Target.Edits) (water : Nat)
    (enough : (CPS1Deamination.Source.sourceProgram edits).steps.length ≤ water) :
    actualCoding edits water = some (Target.coding edits) := by
  rcases edits with ⟨third,eighth,ninth⟩
  have readout := (source_complete_actual_readout third eighth ninth water enough).2.2.2.2.2
  unfold actualCoding sourceExecution
  rw [← Option.map_map]
  rw [readout, Option.map_some, source_coding_embedding]

theorem complete_actual_first_stop (edits : Target.Edits) (water : Nat)
    (enough : (CPS1Deamination.Source.sourceProgram edits).steps.length ≤ water) :
    actualStopChain edits water =
      some (if edits.eighth then Source.referenceProtein ++ ["*"] else Source.referenceProtein.take 334 ++ ["*"]) := by
  rw [actualStopChain, complete_actual_coding edits water enough]
  exact Target.complete_first_stop_response edits.third edits.eighth edits.ninth

def paidEdits (edits : Target.Edits) (water : Nat) : Target.Edits :=
  let addresses := ((CPS1Deamination.Source.sourceProgram edits).steps.take water).map
    CPS1Deamination.Source.Step.address
  ⟨addresses.contains 70,addresses.contains Target.targetOffset,addresses.contains 64⟩

def paidEighth (edits : Target.Edits) (water : Nat) : Bool :=
  (paidEdits edits water).eighth

theorem source_steps_length_bound (third eighth ninth : Bool) :
    (CPS1Deamination.Source.sourceProgram ⟨third,eighth,ninth⟩).steps.length ≤ 3 := by
  cases third <;> cases eighth <;> cases ninth <;> decide +kernel

theorem source_prefix_genomic_readout (third eighth ninth : Bool) (water : Nat) :
    CPS1Deamination.Source.plusReadout
      (prefixWord CPS1Deamination.Source.originalMinusAligned
        ((CPS1Deamination.Source.sourceProgram ⟨third,eighth,ninth⟩).steps.take water)) =
      Target.genomic (paidEdits ⟨third,eighth,ninth⟩ water) := by
  cases third <;> cases eighth <;> cases ninth <;>
    cases water with
    | zero => decide +kernel
    | succ water =>
      cases water with
      | zero => decide +kernel
      | succ water =>
        cases water with
        | zero => decide +kernel
        | succ water =>
          have enough : ∀ t e n, (CPS1Deamination.Source.sourceProgram ⟨t,e,n⟩).steps.length ≤ water+3 :=
            fun t e n => (source_steps_length_bound t e n).trans (by omega)
          simp only [paidEdits, List.take_of_length_le (enough _ _ _)]
          decide +kernel

theorem source_prefix_coding_stop (third eighth ninth : Bool) (water : Nat) :
    let program := CPS1Deamination.Source.sourceProgram ⟨third,eighth,ninth⟩
    let genomic := CPS1Deamination.Source.plusReadout
      (prefixWord CPS1Deamination.Source.originalMinusAligned (program.steps.take water))
    let coding := codingFromGenomic genomic
    (do
      let translated ← Coding.coding? coding
      Coding.translate Coding.code translated) =
      some (if paidEighth ⟨third,eighth,ninth⟩ water then
        Source.referenceProtein ++ ["*"] else Source.referenceProtein.take 334 ++ ["*"]) := by
  dsimp only
  rw [source_prefix_genomic_readout, source_coding_embedding]
  have response := Target.complete_first_stop_response
    (paidEdits ⟨third,eighth,ninth⟩ water).third
    (paidEdits ⟨third,eighth,ninth⟩ water).eighth
    (paidEdits ⟨third,eighth,ninth⟩ water).ninth
  change Target.stopChain (paidEdits ⟨third,eighth,ninth⟩ water) = _
  exact response

theorem actual_first_stop_all_capacities (edits : Target.Edits) (water : Nat) :
    actualStopChain edits water =
      some (if paidEighth edits water then Source.referenceProtein ++ ["*"]
        else Source.referenceProtein.take 334 ++ ["*"]) := by
  have readout := (source_prefix_actual_readout edits water).1
  unfold actualStopChain actualCoding sourceExecution
  rw [readout]
  exact source_prefix_coding_stop edits.third edits.eighth edits.ninth water

theorem three_step_prefix_rescue_threshold (water : Nat) :
    paidEighth ⟨true,true,true⟩ water = decide (2 ≤ water) := by
  cases water with
  | zero => decide +kernel
  | succ water =>
    cases water with
    | zero => decide +kernel
    | succ water =>
      have addresses : (CPS1Deamination.Source.sourceProgram ⟨true,true,true⟩).steps.map
          CPS1Deamination.Source.Step.address = [70,65,64] := by decide +kernel
      have offset : Target.targetOffset = 65 := by decide +kernel
      simp only [paidEighth, paidEdits, List.map_take, addresses, offset]
      simp

theorem first_edit_does_not_pay_intended_correction :
    paidEighth ⟨true,true,true⟩ 1 = false ∧
    paidEighth ⟨true,true,true⟩ 2 = true ∧
    paidEighth ⟨true,false,false⟩ 100 = false ∧
    paidEighth ⟨false,true,false⟩ 1 = true := by decide +kernel

end CPS1Deamination.CodingReadout
