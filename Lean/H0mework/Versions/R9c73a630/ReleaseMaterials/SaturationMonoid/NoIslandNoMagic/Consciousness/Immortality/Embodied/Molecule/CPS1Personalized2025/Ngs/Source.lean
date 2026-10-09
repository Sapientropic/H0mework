import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs.Reifier

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs

namespace Source
 def rows : List Allele := cps1NgsRows%
 def reference : Bases := cps1NgsBases% "reference"
 def parentSha : String := cps1NgsText% "parent_packet_sha256"
 def pdfSha : String := cps1NgsText% "pdf_sha256"
 def imageSha : String := cps1NgsText% "image_sha256"
 def caption : String := cps1NgsText% "original_caption"
 def cell : String := cps1NgsText% "cell"
 def treatment : String := cps1NgsText% "treatment"
 def selection : String := cps1NgsText% "selection"
 def strand : String := cps1NgsText% "printed_strand"
 def transcript : String := cps1NgsText% "transcript"
 def spacerStart : Nat := cps1NgsNat% "spacer_start_zero_based"
 def a8Column : Nat := cps1NgsNat% "a8_column_zero_based"
 def variantPosition : Nat := cps1NgsNat% "variant_position_one_based"
 def row (i : Fin 17) : Allele := rows[i.val]!
 theorem complete_inventory : rows.length = 17 ∧ (∀ i : Fin 17, (row i).word.length = 40) ∧
    rows.map Allele.reads = [862,432,413,184,88,74,48,43,38,29,25,23,19,17,15,13,11] ∧
    rows.map Allele.percentage = [3521,1765,1687,752,359,302,196,176,155,118,102,94,78,69,61,53,45] := by
   decide +kernel
 theorem same_source_identity :
    parentSha = CPS1Personalized2025.Reifier.packetSha256 ∧ pdfSha = CPS1Personalized2025.Source.sourcePdfSha ∧
    variantPosition = CPS1Personalized2025.Source.variantPosition ∧
    transcript = CPS1Personalized2025.Source.referenceAccession ∧
    cell = "Q335X lentivirus-transduced HuH-7" ∧ treatment = "clinical batch k-abe" ∧
    selection = "sample with highest editing in Figure 2C" ∧ strand = "antisense" := by decide +kernel
end Source

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Ngs
