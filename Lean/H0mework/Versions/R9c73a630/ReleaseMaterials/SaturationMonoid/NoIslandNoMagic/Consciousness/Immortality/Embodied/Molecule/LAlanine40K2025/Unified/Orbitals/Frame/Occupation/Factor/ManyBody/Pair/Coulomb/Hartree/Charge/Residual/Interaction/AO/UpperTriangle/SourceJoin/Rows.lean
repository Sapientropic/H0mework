import H0mework.Versions.AB.Chemistry.LAlanineRefinementSource.FiniteData
import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceSourceBoundReentry

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open BasinRefinement.SourceFiniteData
noncomputable section

def targetAORow (address : Nat) : Array Int :=
  ((Reentry.Source.stepReadout.nuclear.targetLedger.aoPairBlocks[address / 64]!)[address % 64]!)

def targetLeft (address : Nat) : Basis :=
  Fin.ofNat 98 ((targetAORow address)[0]!.toNat)

def targetRight (address : Nat) : Basis :=
  Fin.ofNat 98 ((targetAORow address)[1]!.toNat)

def pairIndex (address : Nat) : Nat :=
  (targetLeft address).val * (197 - (targetLeft address).val) / 2 +
    ((targetRight address).val - (targetLeft address).val)

abbrev targetRowCertified (address : Nat) : Prop :=
  0 ≤ (targetAORow address)[0]! ∧
  0 ≤ (targetAORow address)[1]! ∧
  (targetAORow address)[0]!.toNat < 98 ∧
  (targetAORow address)[1]!.toNat < 98 ∧
  (targetLeft address).val ≤ (targetRight address).val ∧
  pairIndex address = address ∧
  (targetAORow address)[2]! =
    (if targetLeft address = targetRight address then 1 else 2) ∧
  |densityMatrix (targetLeft address) (targetRight address) -
    ((targetAORow address)[3]! : ℚ) / 10^12| <
      (1 : ℚ) / (2 * 10^12)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
