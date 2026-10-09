import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.StagedActions
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate

def sourceFirstLoadCoreInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (ordinaryLoadFullQ (0 : Basis) (1 : Basis) (by decide))

def sourceFirstPhaseLoadCoreInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (qscale phaseQ (ordinaryLoadFullQ (0 : Basis) (1 : Basis) (by decide)))

def sourceFirstPhaseSupplyCoreInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (qscale phaseQ (ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide)))

def sourceFirstPhaseWeakCoreInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (qscale phaseQ (ordinaryWeakFullQ (0 : Basis) (1 : Basis) (by decide)))

def sourceFirstZeroCoreInt : MatrixInt OrdinaryFull OrdinaryFull := ⟨0,0⟩

private theorem matrix_int_ext {α β : Type*} {A B : MatrixInt α β}
    (hRe : A.re=B.re) (hIm : A.im=B.im) : A=B := by
  cases A
  cases B
  cases hRe
  cases hIm
  rfl

theorem source_first_load_pulse_blocks : sourceFirstLoadPulseInt =
    intFourBlocks sourceFirstLoadCoreInt sourceFirstZeroCoreInt
      sourceFirstZeroCoreInt sourceFirstPhaseLoadCoreInt := by
  apply matrix_int_ext <;> funext i j
  all_goals rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp [sourceFirstLoadPulseInt,sourceFirstLoadCoreInt,
    sourceFirstPhaseLoadCoreInt,sourceFirstZeroCoreInt,ordinaryPointerLoadQ,
    ordinaryPointerPulseQ,intFourBlocks,Matrix.fromBlocks,quantize,qscale,
    quantizeScalar,roundRatio,scale]

theorem source_first_supply_pulse_blocks : sourceFirstSupplyPulseInt =
    intFourBlocks sourceFirstLoadCoreInt sourceFirstZeroCoreInt
      sourceFirstZeroCoreInt sourceFirstPhaseSupplyCoreInt := by
  apply matrix_int_ext <;> funext i j
  all_goals rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp [sourceFirstSupplyPulseInt,sourceFirstLoadCoreInt,
    sourceFirstPhaseSupplyCoreInt,sourceFirstZeroCoreInt,ordinaryPointerSupplyQ,
    ordinaryPointerPulseQ,intFourBlocks,Matrix.fromBlocks,quantize,qscale,
    quantizeScalar,roundRatio,scale]

theorem source_first_weak_pulse_blocks : sourceFirstWeakPulseInt =
    intFourBlocks sourceFirstLoadCoreInt sourceFirstZeroCoreInt
      sourceFirstZeroCoreInt sourceFirstPhaseWeakCoreInt := by
  apply matrix_int_ext <;> funext i j
  all_goals rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp [sourceFirstWeakPulseInt,sourceFirstLoadCoreInt,
    sourceFirstPhaseWeakCoreInt,sourceFirstZeroCoreInt,ordinaryPointerWeakQ,
    ordinaryPointerPulseQ,intFourBlocks,Matrix.fromBlocks,quantize,qscale,
    quantizeScalar,roundRatio,scale]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
