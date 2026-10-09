import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Nuclear
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.State
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
variable {frame : CPS1Recycling.Frame}

abbrev OccupiedConfiguration (source : CPS1ElectronicSource.State frame) :=
  Matrix (CPS1MolecularFrame.ActualIndex source) (ElectronIndex source.geometry) ℂ

abbrev EnergyConfiguration (source : CPS1ElectronicSource.State frame) :=
  NuclearConfiguration source × OccupiedConfiguration source

def rawNuclearIntegralAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q : CPS1MolecularFrame.PrimitiveIndex source) (jetP jetQ : Fin 3 → Nat) (spin : Bool) (nuclear : Point) : ℂ :=
  if p.2 = spin ∧ q.2 = spin then CPS1MolecularFrame.primitiveNuclearIntegral
    (positions p.1.1) (positions q.1.1) p.1.2.val q.1.2.val nuclear jetP jetQ else 0

def rawPairIntegralAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (p q r s : CPS1MolecularFrame.PrimitiveIndex source) (spin secondSpin : Bool) : ℂ :=
  if p.2 = spin ∧ q.2 = spin ∧ r.2 = secondSpin ∧ s.2 = secondSpin then
    CPS1MolecularFrame.primitivePairIntegral (positions p.1.1) (positions q.1.1)
      (positions r.1.1) (positions s.1.1) p.1.2.val q.1.2.val r.1.2.val s.1.2.val 0 0 0 0 else 0

def nuclearIntegralAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j : CPS1MolecularFrame.ActualIndex source) (nuclear : Point) : ℂ :=
  ∑ spin : Bool, ∑ p, ∑ q,
    (star (CPS1MolecularFrame.basisCoefficient source p i)*CPS1MolecularFrame.basisCoefficient source q j)*
      rawNuclearIntegralAt source positions p q 0 0 spin nuclear

def pairIntegralAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j k l : CPS1MolecularFrame.ActualIndex source) (spin secondSpin : Bool) : ℂ :=
  ∑ p, ∑ q, ∑ r, ∑ s,
    (star (CPS1MolecularFrame.basisCoefficient source p i)*CPS1MolecularFrame.basisCoefficient source q j*
      star (CPS1MolecularFrame.basisCoefficient source r k)*CPS1MolecularFrame.basisCoefficient source s l)*
      rawPairIntegralAt source positions p q r s spin secondSpin

def twoBodyAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j k l : CPS1MolecularFrame.ActualIndex source) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, pairIntegralAt source positions i k j l spin secondSpin

def kineticAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j : CPS1MolecularFrame.ActualIndex source) : ℂ :=
  ((1/(2*source.geometry.electronInertia) : ℝ) : ℂ)*
    ∑ axis : Fin 3, inner ℂ (basisJetAt source positions i (raise 0 axis))
      (basisJetAt source positions j (raise 0 axis))

def attractionAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (i j : CPS1MolecularFrame.ActualIndex source) : ℂ :=
  (List.ofFn (fun nuclear : CPS1MolecularFrame.NuclearIndex source =>
    -((CPS1MolecularFrame.nucleus source nuclear).particle.charge : ℂ)*
      nuclearIntegralAt source positions i j (positions nuclear))).sum

def coreAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  fun i j => kineticAt source positions i j+attractionAt source positions i j

def densityAt (source : CPS1ElectronicSource.State frame) (occupied : OccupiedConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  occupied*occupied.conjTranspose

def electronicEnergyAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) : ℝ :=
  (Matrix.trace (coreAt source positions*densityAt source occupied)).re+(1/2)*
    (∑ i, ∑ j, ∑ k, ∑ l, densityAt source occupied k i*densityAt source occupied l j*
      (twoBodyAt source positions i j k l-twoBodyAt source positions i j l k)).re

def energyAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) : ℝ :=
  nuclearEnergyAt source positions (energySourceMomenta source)+electronicEnergyAt source positions occupied

def energyWithMomenta (source : CPS1ElectronicSource.State frame) (positions momenta : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) : ℝ :=
  nuclearEnergyAt source positions momenta+electronicEnergyAt source positions occupied

def physicalFockAt (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) :
    Matrix (CPS1MolecularFrame.ActualIndex source) (CPS1MolecularFrame.ActualIndex source) ℂ :=
  fun i k => coreAt source positions i k+∑ j, ∑ l, densityAt source occupied l j*
    (twoBodyAt source positions i j k l-twoBodyAt source positions i j l k)

def energyDifferential (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) : EnergyConfiguration source →L[ℝ] ℝ :=
  fderiv ℝ (fun current : EnergyConfiguration source => energyAt source current.1 current.2) (positions,occupied)

def nuclearDifferential (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) : NuclearConfiguration source →L[ℝ] ℝ :=
  (energyDifferential source positions occupied).comp (ContinuousLinearMap.inl ℝ _ _)

def occupiedDifferential (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : OccupiedConfiguration source) : OccupiedConfiguration source →L[ℝ] ℝ :=
  (energyDifferential source positions occupied).comp (ContinuousLinearMap.inr ℝ _ _)

end
end CPS1Deformation
