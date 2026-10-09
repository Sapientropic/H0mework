import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source
def rawGuide : List Char := cps1Raw% "guide"
def rawMrna : List Char := cps1Raw% "mrna"
def editorProtein : List Char := cps1Raw% "reported_editor_protein"
def genomic : Bases := cps1Bases% "context" "dna"
def referenceRna : Bases := cps1Bases% "reference" "dna"
def referenceProtein : List String := cps1Protein%
def referenceStart : Nat := cps1Nat% "reference" "cds_start_one_based"
def referenceEnd : Nat := cps1Nat% "reference" "cds_end_one_based"
def contextStart : Nat := cps1Nat% "context" "start"
def contextEnd : Nat := cps1Nat% "context" "end"
def variantPosition : Nat := cps1Nat% "registration" "variant_position_one_based"
def codingPosition : Nat := cps1Nat% "registration" "coding_position_one_based"
def maternalPosition : Nat := cps1Nat% "registration" "maternal_coding_position_one_based"
def referenceAccession : String := cps1GroupText% "reference" "accession"
def sourcePdfSha : String := cps1Text% "pdf_sha256"
def originalPages : String := cps1Json% "original_pages"
def registration : String := cps1Json% "registration"
def sourceProvenance : String := cps1Text% "capture_role"
def assays : List AssayRow := cps1Assays%
def assayMetric : String := cps1Text% "assay_metric"
def clinical : ClinicalRegistration := cps1Clinical%
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source
