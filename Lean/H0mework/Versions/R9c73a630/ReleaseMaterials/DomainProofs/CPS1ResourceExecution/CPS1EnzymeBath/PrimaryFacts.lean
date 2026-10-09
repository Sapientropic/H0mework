import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Primary
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AtomicDynamics.Charged

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1EnzymeBath.Primary

def atomCount (atoms : List Atom) (element : Element) : Nat :=
  (atoms.filter (fun atom => atom.element = element)).length

def templateCharge (kind : TemplateKind) : Int := ((template kind).atoms.map Atom.charge).sum

def endpointsPresent (kind : TemplateKind) : Bool :=
  (template kind).bonds.all (fun bond =>
    ((template kind).atoms.any (fun atom => atom.ordinal = bond.left)) &&
      ((template kind).atoms.any (fun atom => atom.ordinal = bond.right)))

theorem original_formula (kind : TemplateKind) (element : Element) :
    atomCount (template kind).atoms element =
      CPS1LocalChemicalExecution.PeptideMaterial.moleculeAtoms kind.molecule element := by
  cases kind <;> cases element <;> decide +kernel

theorem original_charge (kind : TemplateKind) :
    templateCharge kind = kind.molecule.charge := by
  cases kind <;> decide +kernel

theorem original_ordinals (kind : TemplateKind) :
    (template kind).atoms.map Atom.ordinal = List.range (template kind).atoms.length := by
  cases kind <;> decide +kernel

theorem original_ordinals_unique (kind : TemplateKind) :
    ((template kind).atoms.map Atom.ordinal).Nodup := by
  rw [original_ordinals]
  exact List.nodup_range

theorem original_bond_endpoints (kind : TemplateKind) : endpointsPresent kind = true := by
  cases kind <;> decide +kernel

theorem original_electron_count (kind : TemplateKind) :
    ∀ atom ∈ (template kind).atoms,
      atom.charge ≤ (CPS1AtomicDynamics.Charged.atomicNumber atom.element : Int) := by
  cases kind <;> decide +kernel

theorem hydrogen_valence (kind : TemplateKind) :
    ∀ atom ∈ (template kind).atoms, atom.element = .H →
      atom.charge = 0 ∧
      ((template kind).bonds.filter (fun bond => bond.left = atom.ordinal ∨ bond.right = atom.ordinal)).length = 1 ∧
      ((template kind).bonds.filter (fun bond => bond.left = atom.ordinal ∨ bond.right = atom.ordinal)).all
        (fun bond => bond.order = 1) = true := by
  cases kind <;> decide +kernel

theorem expanded_hydrogen_source (kind : TemplateKind) :
    (template kind).atoms.all (fun atom =>
      match atom.origin with
      | .source _ => true
      | .expandedHydrogen parent _ => atom.element = .H && atom.charge = 0 &&
          ((template kind).atoms.any (fun original => original.ordinal = parent))) = true := by
  cases kind <;> decide +kernel

theorem nag_source_stereo : (nag.atoms[2]?).map Atom.stereo = some "CHI_TETRAHEDRAL_CW:S" := by decide +kernel

end CPS1EnzymeBath.Primary
