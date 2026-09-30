import H0mework.Chemistry.LAlanineReentry.ProducerCoefficients
import H0mework.Chemistry.LAlanineReentry.RuntimeRuntimeParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open Propagation.Interface
noncomputable section

abbrev ReentryResult := JointNext.Runtime.JointResult
abbrev ReentryHistory := Inertia.Interface.InertialStepReadout × JointNext.Runtime.JointResult ×
  (Inertia.Interface.InertialStepReadout × HeldForce.Runtime.HeldForceResult) × String

elab "reifyReentryParentNuclearResiduals" : term => do
  let packet ← SourceParsing.verifiedPacket
  let nuclear ← Inertia.SourceParsing.field packet "nuclear"
  let residuals ← Inertia.SourceParsing.field nuclear "parent_nuclear_residuals"
  pure (Lean.toExpr residuals.compress)

set_option maxRecDepth 2048 in
/-- The whole source residual object is retained, including engine-binding rows not used by a scalar reader. -/
def reentryParentNuclearResidualsText : String := reifyReentryParentNuclearResiduals

def reentrySourceHistory : ReentryHistory :=
  (reentryParentPacket, reentryParentResult, reentryParentHistory, reentryParentNuclearResidualsText)

def reentrySourceResult : ReentryResult where
  nuclear := Source.stepReadout.nuclear
  held := Continuation.exactTarget Source.hamiltonian Producer.sourceHamiltonian_hermitian Source.crossMatrix
  realized := Source.targetRealized
  inheritedResidual := Continuation.inheritedResidual Source.hamiltonian Producer.sourceHamiltonian_hermitian Source.crossMatrix
  newNumericalResidual := Source.targetRealized -
    Continuation.numericalInputTarget Source.hamiltonian Producer.sourceHamiltonian_hermitian Source.crossMatrix
  totalRealizationResidual := Source.targetRealized -
    Continuation.exactTarget Source.hamiltonian Producer.sourceHamiltonian_hermitian Source.crossMatrix
  clock := reentryParentTime + Source.stepReadout.nuclear.duration

theorem reentrySourceResult_clock : reentrySourceResult.clock = Continuation.targetClock := rfl

theorem reentrySourceResult_body :
    reentrySourceResult.nuclear.target = Source.stepReadout.nuclear.target ∧
    reentrySourceResult.nuclear.targetLedger = Source.stepReadout.nuclear.targetLedger ∧
    reentrySourceResult.nuclear.current = reentryParentFrame ∧
    reentrySourceResult.nuclear.masses = reentryParentMasses := ⟨rfl, rfl, rfl, rfl⟩

theorem reentrySourceHistory_actual :
    reentrySourceHistory.1 = JointNext.Source.stepReadout.nuclear ∧
    reentrySourceHistory.2.1 = JointNext.Runtime.jointSourceResult ∧
    reentrySourceHistory.2.2.1 = (JointNext.Runtime.jointParentHistory, JointNext.Runtime.jointParentResult) ∧
    reentrySourceHistory.2.2.2 = reentryParentNuclearResidualsText := ⟨rfl, rfl, rfl, rfl⟩

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
