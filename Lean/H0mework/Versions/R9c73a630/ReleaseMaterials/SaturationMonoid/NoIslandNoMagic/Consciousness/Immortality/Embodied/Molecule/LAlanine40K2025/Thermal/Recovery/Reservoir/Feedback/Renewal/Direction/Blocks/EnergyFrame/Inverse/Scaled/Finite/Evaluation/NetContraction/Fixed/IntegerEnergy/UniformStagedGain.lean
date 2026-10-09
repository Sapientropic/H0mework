import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.Table
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators
noncomputable section

def stagedOrdinaryGainNumeratorInt (a b : Basis) (ordered : a < b) : Int := Id.run do
  let rootPlus := fromTable (toTable (sourceOrdinaryRootInt a b ordered) nativeFin nativeFin) nativeFin nativeFin
  let rootMinus := fromTable (toTable (sourceOrdinaryComplementInt a b ordered) nativeFin nativeFin) nativeFin nativeFin
  let free := fromTable (toTable (sourceOrdinaryFreeInt a b ordered) nativeFin nativeFin) nativeFin nativeFin
  let rotatedPlus := fromTable (toTable (rotateInt free rootPlus) nativeFin nativeFin) nativeFin nativeFin
  let rotatedMinus := fromTable (toTable (rotateInt free rootMinus) nativeFin nativeFin) nativeFin nativeFin
  let rolePlus := roleBlocksInt (bodyLiftIdentityInt rotatedPlus) (donorLiftIdentityInt sourceDonorRootRotatedInt)
  let roleMinus := roleBlocksInt (bodyLiftIdentityInt rotatedMinus) (donorLiftIdentityInt sourceDonorComplementRotatedInt)
  let pointer := fromTable (toTable (intFourBlocks rolePlus (intNeg roleMinus) roleMinus rolePlus) pointerFin pointerFin) pointerFin pointerFin
  let supply := fromTable (toTable (quantize (ordinarySupplyQ a b ordered)) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin
  let columns := fromTable (toTable (multiply (submatrix pointer id Sum.inl) (submatrix supply id ordinaryInjection)) pointerFin nativeFin) pointerFin nativeFin
  let received := fromTable (toTable (quantize (ordinaryReceivedQ a b ordered)) nativeFin nativeFin) nativeFin nativeFin
  let entrance := fromTable (toTable (multiply columns received) pointerFin nativeFin) pointerFin nativeFin
  let supplyPulse := fromTable (toTable (quantize (ordinaryPointerSupplyQ a b ordered)) pointerFin pointerFin) pointerFin pointerFin
  let loadPulse := fromTable (toTable (quantize (ordinaryPointerLoadQ a b ordered)) pointerFin pointerFin) pointerFin pointerFin
  let weakPulse := fromTable (toTable (quantize (ordinaryPointerWeakQ a b ordered)) pointerFin pointerFin) pointerFin pointerFin
  let supply1 := fromTable (toTable (multiply supplyPulse entrance) pointerFin nativeFin) pointerFin nativeFin
  let supply2 := fromTable (toTable (multiply supplyPulse supply1) pointerFin nativeFin) pointerFin nativeFin
  let nine := fromTable (toTable (multiply loadPulse supply2) pointerFin nativeFin) pointerFin nativeFin
  let weak := fromTable (toTable (multiply weakPulse nine) pointerFin nativeFin) pointerFin nativeFin
  let eleven := fromTable (toTable (multiply loadPulse weak) pointerFin nativeFin) pointerFin nativeFin
  let nineSelected := fromTable (toTable (submatrix nine id chargedInjection) pointerFin pairFin) pointerFin pairFin
  let elevenSelected := fromTable (toTable (submatrix eleven id chargedInjection) pointerFin pairFin) pointerFin pairFin
  let pc := fromTable (toTable (quantize (ordinaryPCPointerQ a b)) pointerFin pointerFin) pointerFin pointerFin
  let nineWeighted := fromTable (toTable (multiply (adjoint nineSelected) pc) pairFin pointerFin) pairFin pointerFin
  let elevenWeighted := fromTable (toTable (multiply (adjoint elevenSelected) pc) pairFin pointerFin) pairFin pointerFin
  let nineEnergy := fromTable (toTable (multiply nineWeighted nineSelected) pairFin pairFin) pairFin pairFin
  let elevenEnergy := fromTable (toTable (multiply elevenWeighted elevenSelected) pairFin pairFin) pairFin pairFin
  let net := fromTable (toTable (sub elevenEnergy nineEnergy) pairFin pairFin) pairFin pairFin
  let body := fromTable (toTable (quantize (qkron (ordinaryPairBlockQ a b) environmentQ)) pairFin pairFin) pairFin pairFin
  let energy := multiply net body
  return ∑ i : Fin 2 × Fin 2, energy.re i i

theorem staged_ordinary_gain_original (a b : Basis) (ordered : a < b) :
    stagedOrdinaryGainNumeratorInt a b ordered=
      sourceOrdinaryGainNumeratorInt a b ordered := by
  simp only [stagedOrdinaryGainNumeratorInt,from_to_table]
  rfl

def stagedOrdinaryGainIntQ (a b : Basis) (ordered : a < b) : ℚ :=
  (stagedOrdinaryGainNumeratorInt a b ordered : ℚ)/(scale : ℚ)

theorem staged_ordinary_gain_same (a b : Basis) (ordered : a < b) :
    stagedOrdinaryGainIntQ a b ordered=sourceOrdinaryGainIntQ a b ordered := by
  rw [stagedOrdinaryGainIntQ,staged_ordinary_gain_original]
  rfl

theorem staged_ordinary_gain_actual_error (a b : Basis) (ordered : a < b) :
    |(stagedOrdinaryGainIntQ a b ordered : ℝ)-
      (smallGainQ (s(a,b)) : ℝ)| ≤ (3/10^7 : ℝ) := by
  rw [staged_ordinary_gain_same]
  exact source_ordinary_integer_gain_error a b ordered

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
