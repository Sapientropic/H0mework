import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.ThirdSpectrum
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondEnergyStage
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.QuadraticConsumer

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

def paidNetInt (slot : Fin 2) : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  if slot=0 then literalFirstNetInt else fromTable stagedSecondNetTable pairFin pairFin

def paidCenterInt (slot : Fin 2) : Int :=
  if slot=0 then 5082*scale/10^9 else 2405*scale/10^9

def paidDeltaInt (slot : Fin 2) : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  sub (paidNetInt slot) thirdNetInt

def paidCenteredInt (slot : Fin 2) : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => (paidDeltaInt slot).re i j - (if i=j then paidCenterInt slot else 0),
   (paidDeltaInt slot).im⟩

def paidCenteredSquareInt (slot : Fin 2) : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
    (((paidCenteredInt slot).re i j)^2+((paidCenteredInt slot).im i j)^2)

theorem paid_centered_square_lt (slot : Fin 2) :
    paidCenteredSquareInt slot < (scale/10^7)^2 := by
  fin_cases slot <;> decide +kernel

def paidB (slot : Fin 2) : Basis := if slot=0 then 1 else 2
theorem paid_ordered (slot : Fin 2) : (0 : Basis) < paidB slot := by
  fin_cases slot <;> decide

theorem paid_net_original (slot : Fin 2) :
    paidNetInt slot = sourceOrdinaryNetInt (0 : Basis) (paidB slot) (paid_ordered slot) := by
  fin_cases slot
  · exact literal_first_net_original.trans source_first_net_program_same.symm
  · exact staged_second_net_original

noncomputable def paidCenter (slot : Fin 2) : ℝ :=
  if slot=0 then 5082/10^9 else 2405/10^9

theorem paid_centered_value (slot : Fin 2) :
    value (paidCenteredInt slot) = value (paidDeltaInt slot) -
      paidCenter slot • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  fin_cases slot <;> ext i j <;> by_cases h : i=j
  all_goals simp [paidCenteredInt,paidCenterInt,paidCenter,value,raw,scale,h]
  all_goals ring

theorem paid_centered_norm (slot : Fin 2) :
    ‖value (paidDeltaInt slot) -
      paidCenter slot • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (1/10^7 : ℝ) := by
  rw [← paid_centered_value]
  have square :
      (∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2,
        (((paidCenteredInt slot).re i j)^2+((paidCenteredInt slot).im i j)^2)) ≤
        (scale/10^7)^2 := by
    simpa only [paidCenteredSquareInt] using le_of_lt (paid_centered_square_lt slot)
  have h := integer_operator_norm_bound (paidCenteredInt slot) (scale/10^7)
    (by norm_num [scale]) square
  convert h using 1
  norm_num [scale]

theorem paid_source_pair_mass (slot : Fin 2) : (1/50 : ℚ) <
    (pairQ ((0 : Basis),paidB slot) ((0 : Basis),paidB slot)).1+
    (pairQ (paidB slot,(0 : Basis)) (paidB slot,(0 : Basis))).1 := by
  fin_cases slot <;> decide +kernel

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
