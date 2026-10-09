import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.Raw
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Kernel.Coding

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Molecules
open Lean Elab Term

private def residueExpr (r : Residue) : TermElabM Expr := do
  let kind := match r.nucleoside with
    | .adenosine => ``Nucleoside.adenosine | .cytidine => ``Nucleoside.cytidine
    | .guanosine => ``Nucleoside.guanosine | .uridine => ``Nucleoside.uridine
    | .n1Methylpseudouridine => ``Nucleoside.n1Methylpseudouridine
  Meta.mkAppM ``Residue.mk #[Lean.mkConst kind,toExpr r.ribose2OMethyl]
elab "cps1Rna%" index:num : term => do
  let some rna := Rna.parse (if index.getNat == 0 then Source.rawGuide else Source.rawMrna)
    | throwError "Original RNA notation"
  Meta.mkAppM ``RegisteredRna.mk #[← Meta.mkListLit (Lean.mkConst ``Residue) (← rna.residues.mapM residueExpr),
    toExpr rna.sulfurAfter]
def guide : RegisteredRna := cps1Rna% 0
def mrna : RegisteredRna := cps1Rna% 1
def template : Bases := Rna.template mrna
def spacer : Bases := (Rna.template guide).take 20

elab "cps1Coding%" : term => do
  let some dna := Coding.coding? template | throwError "Original first-AUG/first-stop frame"
  Reifier.bases (DNM1Splicing2026.Sequence.render dna)
def editorCoding : Bases := cps1Coding%

theorem complete_original_chemical_words :
    Rna.parse Source.rawGuide = some guide ∧ Rna.parse Source.rawMrna = some mrna := by decide +kernel
theorem original_chemical_inventory :
    guide.residues.length = 100 ∧ Rna.methylCount guide = 47 ∧
    guide.residues.length - Rna.methylCount guide = 53 ∧
    guide.sulfurAfter = [1,2,3,97,98,99] ∧ mrna.residues.length = 5113 ∧
    Rna.pseudoCount mrna = 782 ∧ Rna.methylCount mrna = 0 ∧ mrna.sulfurAfter = [] := by decide +kernel
theorem original_first_frame_generated :
    Coding.firstStart template = some 151 ∧
    Coding.firstFrameStop (template.drop 151) = some 1605 ∧
    Coding.coding? template = some editorCoding ∧ editorCoding.length = 4818 := by decide +kernel
theorem complete_editor_translation :
    Coding.translate Coding.code editorCoding = some (Source.editorProtein.map String.singleton) ∧
    Source.editorProtein.length = 1606 ∧ Source.editorProtein.getLast? = some '*' := by decide +kernel

theorem original_chemistry_survives_template_projection :
    Rna.template (Rna.eraseModifications guide) = Rna.template guide ∧
    Rna.eraseModifications guide ≠ guide ∧
    Rna.template (Rna.eraseModifications mrna) = Rna.template mrna ∧
    Rna.eraseModifications mrna ≠ mrna := by
  refine ⟨Rna.template_forgets_modifications guide,?_,Rna.template_forgets_modifications mrna,?_⟩
  · decide +kernel
  · decide +kernel

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Molecules
