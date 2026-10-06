import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Positive
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.Sections
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.SourceData

/-! The original nuclear census couples to positive current from the same U source.
Point sources act on test potentials; they are not declared pointwise matter fields. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.NuclearCurrent
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open Stage9DEF Stage9C.Material.SpinPair Stage10.ChargedPreparation
open BasinRefinement SourceGaussianModel WholeBandBasin.Family.All.Nuclear
noncomputable section

/-- The spatial conversion remains explicit until the common U/molecular units are generated. -/
def sourcePosition (lengthUnit : ℝ) (atom : Fin 13) : Point :=
  fun axis => lengthUnit*nuclearPosition atom axis

def sourcePoint (time lengthUnit : ℝ) (atom : Fin 13) : BasePoint :=
  spatialSlice time (sourcePosition lengthUnit atom)

def nativeCoupling (time lengthUnit : ℝ) (test : Point → ℝ) : ℝ :=
  ∑ atom : Fin 13, test (sourcePosition lengthUnit atom) *
    (Positive.amountDual (nuclearChargeNat atom) (sourcePoint time lengthUnit atom)
      (Compatibility.currentAction 0 Stage10.HyperchargeResponse.chargeDirection
        (Positive.amountMatter (nuclearChargeNat atom) (sourcePoint time lengthUnit atom)))).re

def nuclearPairing (lengthUnit : ℝ) (test : Point → ℝ) : ℝ :=
  ∑ atom : Fin 13, nuclearCharge atom*test (sourcePosition lengthUnit atom)

theorem original_nuclear_coupling (time lengthUnit : ℝ) (test : Point → ℝ) :
    nativeCoupling time lengthUnit test = 4*spinScale*nuclearPairing lengthUnit test := by
  simp only [nativeCoupling, Positive.amount_current, nuclearPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro atom _
  simp [nuclearCharge]
  ring

theorem original_total_positive_charge (lengthUnit : ℝ) :
    nuclearPairing lengthUnit (fun _ => 1) = 48 := by
  simpa [nuclearPairing] using total_nuclear_charge

theorem original_native_total (time lengthUnit : ℝ) :
    nativeCoupling time lengthUnit (fun _ => 1) = 192*spinScale := by
  rw [original_nuclear_coupling, original_total_positive_charge]
  ring


theorem native_total_positive (time lengthUnit : ℝ) :
    0 < nativeCoupling time lengthUnit (fun _ => 1) := by
  rw [original_native_total]
  exact mul_pos (by norm_num) spinScale_pos

end
end LAlanine40K2025.UnifiedAction.NuclearCurrent
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
