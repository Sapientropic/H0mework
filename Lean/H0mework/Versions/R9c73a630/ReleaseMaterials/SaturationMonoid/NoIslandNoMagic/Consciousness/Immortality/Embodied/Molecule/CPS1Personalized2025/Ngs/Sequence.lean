import Mathlib.Data.Fintype.Fin
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

namespace Sequence
 def genomicStart : Nat := 36
 def codingStart : Nat := CPS1Personalized2025.Source.codingPosition-1 + genomicStart-Target.targetOffset
 def codingWord (word : Bases) : Bases := Coding.reverseComplement word
 def coding (word : Bases) : Bases := replaceWindow Target.referenceCoding codingStart (codingWord word)
 def genomic (word : Bases) : Bases := replaceWindow CPS1Personalized2025.Source.genomic genomicStart (codingWord word)
 def localTranslation (word : Bases) : Option (List String) := Coding.translate Coding.code (Coding.reverseComplement (word.drop 2 |>.take 18))
 def amino (word : Bases) : String := ((localTranslation word).getD [])[3]!
 def firstStop (word : Bases) : Option (List String) := do
   let dna ← Coding.coding? (coding word)
   Coding.translate Coding.code dna
 def a8 (word : Bases) : Bool := word[Source.a8Column]? == some .guanine
 def anyWindow (word : Bases) : Bool := (List.range 10).any fun i =>
   Source.reference[Source.spacerStart+i]? == some .adenine &&
   word[Source.spacerStart+i]? == some .guanine
 def originalQ (word : Bases) : Bool := amino word == "Q"
 def openFrame (word : Bases) : Bool := amino word != "*"
 theorem original_restrictions_and_guide :
    Coding.reverseComplement (Target.original.drop genomicStart |>.take 40) = Source.reference ∧
    (Source.reference.drop Source.spacerStart |>.take 20) = Molecules.spacer ∧
    Source.a8Column = Source.spacerStart+7 ∧ codingStart = 973 ∧
    ((coding Source.reference).drop 1002 |>.take 3) = [.thymine,.adenine,.guanine] ∧
    localTranslation Source.reference = some ["I","T","A","*","N","H"] := by decide +kernel
 theorem every_original_genomic_coding_restriction (i : Fin 17) :
    ((genomic (Source.row i).word).drop genomicStart |>.take 40) =
      ((coding (Source.row i).word).drop codingStart |>.take 40) := by
   fin_cases i <;> decide +kernel
 theorem complete_local_codons :
    Source.rows.map (fun row => localTranslation row.word) =
      [some ["I","T","A","Q","N","H"],some ["I","T","A","*","N","H"],
       some ["I","T","A","Q","N","H"],some ["I","T","A","*","N","H"],
       some ["I","T","A","*","N","H"],some ["I","T","A","Q","N","H"],
       some ["I","T","A","*","N","H"],some ["I","T","A","H","N","H"],
       some ["I","T","A","Q","N","H"],some ["I","T","A","Q","N","H"],
       some ["I","T","A","Q","N","H"],some ["I","T","A","Y","N","H"],
       some ["I","T","A","Q","N","H"],some ["I","T","A","*","N","H"],
       some ["I","T","A","Q","N","H"],some ["I","T","A","Q","N","H"],
       some ["I","T","A","*","N","H"]] := by decide +kernel
 /-- Full RefSeq-context consequence of replacing exactly the observed 40nt restriction. -/
 theorem complete_context_first_stop (i : Fin 17) :
    firstStop (Source.row i).word = some
      (if openFrame (Source.row i).word then
        (CPS1Personalized2025.Source.referenceProtein.set 334 (amino (Source.row i).word)) ++ ["*"]
       else CPS1Personalized2025.Source.referenceProtein.take 334 ++ ["*"]) := by
   fin_cases i <;> decide +kernel
 theorem original_Q_exactly_restores_reference (i : Fin 17) :
    originalQ (Source.row i).word = true ↔
      firstStop (Source.row i).word = some (CPS1Personalized2025.Source.referenceProtein ++ ["*"]) := by
   fin_cases i <;> decide +kernel
 theorem actual_bystanders_separate_three_consumers :
    a8 (Source.row 0).word = a8 (Source.row 7).word ∧
    originalQ (Source.row 0).word ≠ originalQ (Source.row 7).word ∧
    openFrame (Source.row 11).word = true ∧ a8 (Source.row 11).word = false ∧
    amino (Source.row 7).word = "H" ∧ amino (Source.row 11).word = "Y" := by decide +kernel
end Sequence

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
