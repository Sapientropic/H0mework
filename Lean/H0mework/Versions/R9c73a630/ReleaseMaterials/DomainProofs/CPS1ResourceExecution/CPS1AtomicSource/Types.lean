import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LocalChemicalExecution.PeptideMaterial

set_option autoImplicit false
namespace CPS1AtomicSource.Primary
open CPS1ResourceExecution CPS1LocalChemicalExecution

inductive TerminalLeave | none | amino | carboxyl deriving DecidableEq, Repr

structure Atom where
  name : String
  element : PeptideMaterial.Element
  charge : Int
  aromatic : Bool
  stereo : String
  leaving : Bool
  backbone : Bool
  nTerminal : Bool
  cTerminal : Bool
  deriving DecidableEq, Repr

/-- Terminal classification is a restriction of the original CCD flags. -/
def Atom.terminalLeave (atom : Atom) : TerminalLeave :=
  if !atom.leaving then .none else if atom.nTerminal then .amino
  else if atom.cTerminal then .carboxyl else .none

structure Bond where
  left : String
  right : String
  order : String
  aromatic : Bool
  stereo : String
  deriving DecidableEq, Repr

structure Template where
  atoms : List Atom
  bonds : List Bond
  deriving DecidableEq, Repr

end CPS1AtomicSource.Primary
