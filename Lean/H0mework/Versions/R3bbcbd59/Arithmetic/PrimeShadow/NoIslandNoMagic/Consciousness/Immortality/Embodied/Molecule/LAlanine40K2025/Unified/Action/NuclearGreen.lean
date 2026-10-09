import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.PointSources
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.NuclearCurrent
import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.PreciseWholeSpace

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.PreciseNuclear
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource Stage10.StaticGreen Stage9C.Material.SpinPair
open Stage9DEF Stage10.ChargedPreparation
open MeasureTheory BasinRefinement SourceGaussianModel WholeBandBasin.Family.All.Nuclear
open scoped SchwartzMap
noncomputable section

def sourcePosition (lengthUnit : ℝ) (atom : Fin 13) : Point := lengthUnit • PreciseTarget.centre atom

theorem position_same_full_target (lengthUnit : ℝ) (atom : Fin 13) (index : Fin 3) :
    sourcePosition lengthUnit atom index = lengthUnit*(Reentry.Source.stepReadout.nuclear.target.position atom index : ℝ) := rfl

def nativeCoupling (time lengthUnit : ℝ) (test : Point → ℝ) : ℝ :=
  ∑ atom : Fin 13, test (sourcePosition lengthUnit atom)*
    (Positive.amountDual (nuclearChargeNat atom) (spatialSlice time (sourcePosition lengthUnit atom))
      (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection
        (Positive.amountMatter (nuclearChargeNat atom) (spatialSlice time (sourcePosition lengthUnit atom))))).re

theorem original_coupling (time lengthUnit : ℝ) (test : Point → ℝ) :
    nativeCoupling time lengthUnit test = ∑ atom : Fin 13, (4*spinScale*nuclearCharge atom)*test (sourcePosition lengthUnit atom) := by
  simp only [nativeCoupling, Positive.amount_current]
  apply Finset.sum_congr rfl
  intro atom _
  simp [nuclearCharge]
  ring

def potential (lengthUnit : ℝ) : Point → ℝ :=
  pointSourcePotential (sourcePosition lengthUnit) (fun atom => 4*spinScale*nuclearCharge atom)

theorem potential_native (time lengthUnit : ℝ) (point : Point) :
    potential lengthUnit point = -nativeCoupling time lengthUnit (fun centre => green (point-centre)) := by
  rw [original_coupling]
  rfl

theorem original_weak_gauss (time lengthUnit : ℝ) (test : 𝓢(Point, ℝ)) :
    (∫ point : Point, potential lengthUnit point*sourceEuler test point)+nativeCoupling time lengthUnit test = 0 := by
  rw [original_coupling]
  exact pointSource_original_weak_gauss _ _ test

theorem potential_test_integrable (lengthUnit : ℝ) (test : 𝓢(Point, ℝ)) :
    Integrable (fun point => potential lengthUnit point*test point) := pointSource_test_integrable _ _ test

end
end LAlanine40K2025.UnifiedAction.PreciseNuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
