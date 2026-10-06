import H0mework.Versions.AB.Chemistry.LAlanineJointNext.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.SourceReification

open Lean Elab Term
open Propagation.Interface Inertia.SourceParsing SourceParsing

def symmetricRead (rows : Array (Array Int)) (i j : Basis) : Int :=
  ElectronicFrame.SourceParsing.matrixRead rows (min i j) (max i j)

def antisymmetricRead (rows : Array (Array Int)) (i j : Basis) : Int :=
  if i = j then 0 else if i < j then ElectronicFrame.SourceParsing.matrixRead rows i j
  else -ElectronicFrame.SourceParsing.matrixRead rows j i

theorem symmetricRead_swap (rows : Array (Array Int)) (i j : Basis) :
    symmetricRead rows i j = symmetricRead rows j i := by simp only [symmetricRead, min_comm, max_comm]

theorem antisymmetricRead_swap (rows : Array (Array Int)) (i j : Basis) :
    antisymmetricRead rows i j = -antisymmetricRead rows j i := by
  by_cases same : i = j
  · subst j; simp [antisymmetricRead]
  · rcases lt_or_gt_of_ne same with less | more
    · simp [antisymmetricRead, same, Ne.symm same, less, not_lt.mpr (le_of_lt less)]
    · simp [antisymmetricRead, same, Ne.symm same, more, not_lt.mpr (le_of_lt more)]

def matrixExpr (electronic : Json) (key : String) (symmetry : Int) : TermElabM Expr := do
  let rows ← matrixRows electronic key
  for i in [:98] do
    for j in [:98] do
      if symmetry == 1 then
        unless (rows[i]!)[j]! == (rows[j]!)[i]! do throwError "Non-Hermitian source matrix: {key}"
      if symmetry == -1 then
        unless (rows[i]!)[j]! == -(rows[j]!)[i]! do throwError "Non-skew source imaginary matrix: {key}"
  Meta.mkAppM (if symmetry == 1 then ``symmetricRead else if symmetry == -1 then ``antisymmetricRead
    else ``ElectronicFrame.SourceParsing.matrixRead) #[toExpr rows]

def nuclearExpr (nuclear : Json) : TermElabM Expr := do
  let frames ← decode (Array Json) (← field nuclear "frames")
  let current := frames[0]!
  let target := frames[1]!
  let currentLedger ← field nuclear "current_energy_ledger"
  let targetLedger ← field nuclear "target_energy_ledger"
  let (currentNuclei, currentPositions) ← nuclearRows (← field currentLedger "nuclei")
  let (targetNuclei, targetPositions) ← nuclearRows (← field targetLedger "nuclei")
  let currentForce ← field current "force"
  let targetForce ← field target "force"
  let refinement ← field nuclear "native_refinement"
  Meta.mkAppM ``Inertia.Interface.InertialStepReadout.mk
    #[mkConst ``Runtime.jointParentMasses, mkConst ``Interface.duration,
      mkConst ``Runtime.jointParentFrame, ← frame target,
      ← coordinates (← field refinement "position_residual_bohr"),
      ← coordinates (← field refinement "momentum_residual_au"),
      mkConst ``Runtime.jointParentEnergyLedger, ← Energy.Source.reifyMolecularEnergyLedger targetLedger,
      currentNuclei, targetNuclei, currentPositions, targetPositions,
      ← gradientComponents currentForce, ← gradientComponents targetForce,
      ← integerCoordinateExpr (← field currentForce "component_rounding_residual_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field targetForce "component_rounding_residual_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field currentForce "gradient_picohartree_per_bohr"),
      ← integerCoordinateExpr (← field targetForce "gradient_picohartree_per_bohr")]

end LAlanine40K2025.JointNext.SourceReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
