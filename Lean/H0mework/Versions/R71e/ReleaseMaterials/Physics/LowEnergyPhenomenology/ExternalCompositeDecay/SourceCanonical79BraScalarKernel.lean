import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraCurrentData
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNumerators0
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNumerators1
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNumerators2
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraNumerators3
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79ImaginaryDenominators
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValueKernel
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateBraPairBasis
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix

def scalarBranch (dual : Bool) : ℂ →+* ℂ :=
  if dual then starRingEnd ℂ else RingHom.id ℂ

def scalarInverse (dual : Bool) (i j : Fin 79) : ℂ :=
  if dual then axialInverse Complex.I 0 j i else axialInverse Complex.I 0 i j

def scalarRow (dual : Bool) (i : Fin 79) : ℂ :=
  ∑j : Fin 79,((-1/2 : ℂ)*scalarInverse dual i j)*scalarBranch dual (primalCurrentPoint i j)

lemma scalar_star_nat (n : ℕ) : (starRingEnd ℂ) (n : ℂ) = n := map_natCast _ _
lemma scalar_star_ofNat (n : ℕ) [n.AtLeastTwo] :
    (starRingEnd ℂ) (ofNat(n) : ℂ) = ofNat(n) := map_ofNat _ _

end LowEnergy.ActualCanonical79Imaginary
