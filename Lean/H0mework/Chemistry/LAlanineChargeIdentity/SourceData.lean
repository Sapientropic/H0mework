import H0mework.Chemistry.LAlanineChargeIdentity.RuntimeParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.SourceData

open LAlanine40K2025.Force.Interface

/-- The original upper-triangular 98-AO incidence, in its ledger row order. -/
abbrev FieldRow := Fin 4851

def matrixRead (rows : Array (Array Int)) : Matrix Atom Atom Int :=
  fun i j => (rows[i.val]!)[j.val]!

def vectorRead (values : Array Int) : Atom → Int := fun i => values[i.val]!

def selectedRead (values : Array FieldRow) : Atom → FieldRow := fun i => values[i.val]!

def fieldRead (blocks : Array (Array (Array Int))) : Matrix FieldRow Atom Int :=
  fun row atom => ((blocks[row.val / 128]!)[row.val % 128]!)[atom.val]!

def residualRead (blocks : Array (Array Int)) : FieldRow → Int :=
  fun row => (blocks[row.val / 128]!)[row.val % 128]!

noncomputable def parentFieldInteger (row : FieldRow) : Int :=
  ((Runtime.chargeParentLedger.aoPairBlocks[row.val / 64]!)[row.val % 64]!)[6]!

noncomputable def parentCharge (atom : Atom) : Int :=
  ((Runtime.chargeParentResult.nuclear.targetNuclei[atom.val]!).2 : Int)

noncomputable def parentAttraction (atom : Atom) : Int :=
  (Runtime.chargeParentLedger.electronNuclearAtoms[atom.val]!)[2]!

end LAlanine40K2025.ChargeIdentity.SourceData
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
