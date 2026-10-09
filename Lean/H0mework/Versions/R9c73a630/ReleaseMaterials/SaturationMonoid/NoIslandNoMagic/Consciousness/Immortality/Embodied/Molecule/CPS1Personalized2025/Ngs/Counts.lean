import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Sequence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

namespace Counts
 def count (test : Bases → Bool) : Nat :=
   (Source.rows.filter (fun row => test row.word)).map Allele.reads |>.sum
 def shown : Nat := (Source.rows.map Allele.reads).sum
 def printed : Nat := (Source.rows.map Allele.percentage).sum
 theorem complete_read_partition :
    shown = 2334 ∧ count Sequence.originalQ = 1488 ∧ count Sequence.a8 = 1531 ∧
    count Sequence.openFrame = 1554 ∧ count Sequence.anyWindow = 1803 ∧
    count (fun word => Sequence.amino word == "H") = 43 ∧
    count (fun word => Sequence.amino word == "Y") = 23 ∧
    count (fun word => Sequence.amino word == "*") = 780 ∧
    1488+43+23+780 = shown ∧ printed = 9533 := by decide +kernel
 theorem printed_classes_and_computed_codons :
    count Sequence.originalQ = ((Source.rows.filter (fun row => row.printedClass == "+")).map Allele.reads).sum ∧
    (Source.row 11).printedClass = "x" ∧ Sequence.a8 (Source.row 11).word = false ∧
    Sequence.openFrame (Source.row 11).word = true := by decide +kernel
 theorem all_labels_compatible : ∀ i : Fin 17,
    DisplayCompatible (Source.row i).reads (Source.row i).percentage 2448 := by decide +kernel
 theorem compatible_denominator_unique (n : Nat)
    (registered : DisplayCompatible (Source.row 0).reads (Source.row 0).percentage n) : n = 2448 := by
   change 0 < n ∧ 7041*n ≤ 17240000 ∧ 17240000 ≤ 7043*n at registered
   omega
 theorem conditional_complete_denominator (n : Nat)
    (labels : ∀ i : Fin 17, DisplayCompatible (Source.row i).reads (Source.row i).percentage n) :
    n = 2448 ∧ n-shown = 114 ∧ shown < n := by
   have h := compatible_denominator_unique n (labels 0)
   subst n
   exact ⟨rfl,by decide +kernel,by decide +kernel⟩
 /-- No allele class is assigned to the undisplayed reads. -/
 theorem compatible_unshown_bounds (additional : Nat) (bounded : additional ≤ 114) :
    1488 ≤ count Sequence.originalQ + additional ∧
    count Sequence.originalQ + additional ≤ 1602 := by
   have h : count Sequence.originalQ = 1488 := complete_read_partition.2.1
   omega
end Counts

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
