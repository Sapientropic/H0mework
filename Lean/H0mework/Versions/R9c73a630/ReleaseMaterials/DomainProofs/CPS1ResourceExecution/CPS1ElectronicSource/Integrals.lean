import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Domains
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Orbitals

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

def nuclearIntegral (centre : Point) (n : Nat) (i j : Fin n) (nucleus : Point) : ℂ :=
  ∫ x : Point, (SourceCoulomb.kernel (x-nucleus) : ℂ) *
    star (spatialValue centre n i 0 x) * spatialValue centre n j 0 x

def pairIntegral (centre : Point) (n : Nat) (i j k l : Fin n) : ℂ :=
  ∫ z : Point × Point, (SourceCoulomb.kernel (z.1-z.2) : ℂ) *
    star (spatialValue centre n i 0 z.1) * spatialValue centre n j 0 z.1 *
    star (spatialValue centre n k 0 z.2) * spatialValue centre n l 0 z.2
    ∂(volume : Measure Point).prod volume

def kinetic (geometry : Geometry frame) (i j : SpatialIndex geometry) : ℂ :=
  ((1/(2*geometry.electronInertia) : ℝ) : ℂ) *
    ∑ axis : Fin 3, inner ℂ
      (spatialField 0 (spatialModes frame geometry.originJoint) i (raise 0 axis))
      (spatialField 0 (spatialModes frame geometry.originJoint) j (raise 0 axis))

def attraction (geometry : Geometry frame) (i j : SpatialIndex geometry) : ℂ :=
  (geometry.nuclei.map (fun nucleus => -(nucleus.particle.charge : ℂ) *
    nuclearIntegral 0 (spatialModes frame geometry.originJoint) i j (Geometry.nucleusPosition nucleus))).sum

def core (geometry : Geometry frame) : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ :=
  fun i j => if i.2 = j.2 then kinetic geometry i.1 j.1 + attraction geometry i.1 j.1 else 0

def twoBody (geometry : Geometry frame) (i j k l : SpinIndex geometry) : ℂ :=
  if i.2 = k.2 ∧ j.2 = l.2 then
    pairIntegral 0 (spatialModes frame geometry.originJoint) i.1 k.1 j.1 l.1 else 0

def fock (geometry : Geometry frame) (density : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ) :
    Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ :=
  fun i k => core geometry i k + ∑ j, ∑ l,
    density l j * (twoBody geometry i j k l-twoBody geometry i j l k)

def electronicEnergy (geometry : Geometry frame)
    (density : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ) : ℝ :=
  (Matrix.trace (core geometry * density)).re +
    (1/2) * (∑ i, ∑ j, ∑ k, ∑ l, density k i * density l j *
      (twoBody geometry i j k l-twoBody geometry i j l k)).re

def totalEnergy (geometry : Geometry frame)
    (density : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ) : ℝ :=
  geometry.nuclearEnergy + electronicEnergy geometry density

theorem actual_energy_replacement (geometry : Geometry frame)
    (density : Matrix (SpinIndex geometry) (SpinIndex geometry) ℂ) :
    totalEnergy geometry density-geometry.classicalEnergy =
      electronicEnergy geometry density-geometry.classicalElectronicEnergy := by
  unfold totalEnergy Geometry.classicalElectronicEnergy
  ring

end
end CPS1ElectronicSource
