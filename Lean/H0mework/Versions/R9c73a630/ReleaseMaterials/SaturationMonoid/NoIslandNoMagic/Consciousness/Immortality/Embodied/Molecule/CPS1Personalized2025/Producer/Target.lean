import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Molecules

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target

structure Edits where
  third : Bool
  eighth : Bool
  ninth : Bool
  deriving DecidableEq, Repr
def selected (edits : Edits) (position : Nat) : Bool :=
  (position == 2 && edits.third) || (position == 7 && edits.eighth) || (position == 8 && edits.ninth)
def referenceCoding : Bases :=
  Source.referenceRna.drop (Source.referenceStart-1) |>.take (Source.referenceEnd-Source.referenceStart+1)
def targetOffset : Nat := Source.variantPosition-1-Source.contextStart
def original : Bases := Source.genomic.set targetOffset .thymine
def guideStart : Nat := (Coding.sites original (Coding.reverseComplement Molecules.spacer)).headD 0
def firstWindow : List Nat := (List.range 10).filter (fun i => Molecules.spacer[i]? == some .adenine)
def positions (edits : Edits) : List Nat :=
  (firstWindow.filter (selected edits)).map (fun i => guideStart+Molecules.spacer.length-1-i)
def genomic (edits : Edits) : Bases :=
  (positions edits).foldl (fun dna i => dna.set i .cytosine) original
def coding (edits : Edits) : Bases :=
  (positions edits).foldl (fun dna i => dna.set (Source.codingPosition-1+i-targetOffset) .cytosine)
    (referenceCoding.set (Source.codingPosition-1) .thymine)
def localStart : Nat := Source.codingPosition-1-42
def localWord (edits : Edits) : Bases := (coding edits).drop localStart |>.take 78
def stopChain (edits : Edits) : Option (List String) := do
  let dna ← Coding.coding? (coding edits)
  Coding.translate Coding.code dna
def anyFirstWindowEdit (edits : Edits) : Bool := edits.third || edits.eighth || edits.ninth

theorem original_reference_and_address :
    Source.referenceAccession = "NM_001875.5" ∧ referenceCoding.length = 4503 ∧
    Source.contextStart = 210591820 ∧ Source.contextEnd = 210591930 ∧ Source.genomic.length = 110 ∧
    Source.variantPosition = 210591886 ∧ Source.codingPosition = 1003 ∧ Source.maternalPosition = 2140 ∧
    targetOffset = 65 ∧ Source.genomic[targetOffset]? = some .cytosine ∧
    (referenceCoding.drop 1002).take 3 = [.cytosine,.adenine,.guanine] ∧
    (referenceCoding.drop 2139).take 3 = [.guanine,.adenine,.adenine] := by decide +kernel

theorem original_spacer_generates_edit_positions :
    Molecules.spacer.length = 20 ∧
    Coding.sites original (Coding.reverseComplement Molecules.spacer) = [53] ∧
    guideStart = 53 ∧ firstWindow = [2,7,8] ∧
    positions ⟨true,true,true⟩ = [70,65,64] ∧
    Coding.reverseComplement (original.drop (guideStart-4) |>.take 4) =
      [.adenine,.guanine,.cytosine,.cytosine] := by decide +kernel

theorem original_local_restrictions_agree (third eighth ninth : Bool) :
    ((genomic ⟨third,eighth,ninth⟩).drop (targetOffset-42) |>.take 78) =
      localWord ⟨third,eighth,ninth⟩ := by
  cases third <;> cases eighth <;> cases ninth <;> decide +kernel

theorem intended_source_correction :
    positions ⟨false,true,false⟩ = [targetOffset] ∧
    genomic ⟨false,true,false⟩ = Source.genomic ∧
    coding ⟨false,true,false⟩ = referenceCoding := by decide +kernel

theorem complete_reference_translation :
    Coding.translate Coding.code referenceCoding = some (Source.referenceProtein ++ ["*"]) := by decide +kernel

theorem complete_first_stop_response (third eighth ninth : Bool) :
    stopChain ⟨third,eighth,ninth⟩ =
      some (if eighth then Source.referenceProtein ++ ["*"] else Source.referenceProtein.take 334 ++ ["*"]) := by
  cases third <;> cases eighth <;> cases ninth <;> decide +kernel

theorem editing_readout_does_not_determine_rescue :
    anyFirstWindowEdit ⟨true,false,false⟩ = anyFirstWindowEdit ⟨false,true,false⟩ ∧
    stopChain ⟨true,false,false⟩ ≠ stopChain ⟨false,true,false⟩ := by
  refine ⟨rfl,?_⟩
  rw [complete_first_stop_response,complete_first_stop_response]
  decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Target
