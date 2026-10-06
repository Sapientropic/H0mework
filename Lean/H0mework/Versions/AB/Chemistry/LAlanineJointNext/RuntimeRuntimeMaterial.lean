import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerElectronic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open Propagation.Interface
noncomputable section

structure JointResult where
  nuclear : Inertia.Interface.InertialStepReadout
  held : Matrix Basis Basis ℂ
  realized : Matrix Basis Basis ℂ
  inheritedResidual : Matrix Basis Basis ℂ
  newNumericalResidual : Matrix Basis Basis ℂ
  totalRealizationResidual : Matrix Basis Basis ℂ
  clock : ℚ

def jointSourceResult : JointResult where
  nuclear := Source.stepReadout.nuclear
  held := Producer.exactTarget
  realized := Source.targetRealized
  inheritedResidual := Producer.inheritedResidual
  newNumericalResidual := Producer.newNumericalResidual
  totalRealizationResidual := Producer.totalRealizationResidual
  clock := jointParentTime + Source.stepReadout.nuclear.duration

theorem jointSourceResult_clock : jointSourceResult.clock = Interface.targetClock := rfl

theorem jointSourceResult_body :
    jointSourceResult.nuclear.target = Source.stepReadout.nuclear.target ∧
    jointSourceResult.nuclear.targetLedger = Source.stepReadout.nuclear.targetLedger ∧
    jointSourceResult.nuclear.current = jointParentFrame ∧
    jointSourceResult.nuclear.masses = jointParentMasses := ⟨rfl, rfl, rfl, rfl⟩

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
