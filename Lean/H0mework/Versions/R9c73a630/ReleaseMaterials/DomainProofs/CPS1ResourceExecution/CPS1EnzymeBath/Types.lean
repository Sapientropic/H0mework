import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.PeptideMaterial

set_option autoImplicit false

namespace CPS1EnzymeBath.Primary
abbrev Element := CPS1LocalChemicalExecution.PeptideMaterial.Element

inductive TemplateKind
  | nag | potassium | magnesium | atp | adp | carbamoylPhosphate
  deriving DecidableEq,Repr

def TemplateKind.molecule : TemplateKind → CPS1LocalChemicalExecution.Chemistry.Molecule
  | .nag => .nag | .potassium => .potassium | .magnesium => .magnesium
  | .atp => .atp | .adp => .adp | .carbamoylPhosphate => .carbamoylPhosphate

inductive AtomOrigin
  | source (ordinal : Nat)
  | expandedHydrogen (parent ordinal : Nat)
  deriving DecidableEq,Repr

structure Atom where
  ordinal : Nat
  element : Element
  charge : Int
  aromatic : Bool
  stereo : String
  sourceParity : Nat
  origin : AtomOrigin
  deriving DecidableEq

structure Bond where
  left : Nat
  right : Nat
  order : Nat
  aromatic : Bool
  stereo : String
  sourceStereo : Nat
  expandedHydrogen : Bool
  deriving DecidableEq

structure Template where
  atoms : List Atom
  bonds : List Bond
  deriving DecidableEq

end CPS1EnzymeBath.Primary
