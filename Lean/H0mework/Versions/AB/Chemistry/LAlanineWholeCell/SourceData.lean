import H0mework.Versions.AB.Chemistry.LAlanineWholeCell.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSource

open Lean Elab Term Command SourceSignedEvaluator SourceRectangle SourceFields
open Inertia.SourceParsing

elab "generateWholeCellFieldInputs" : command => liftTermElabM do
  let packet ← verifiedPacket
  let fields ← sourceArray (← field packet "fields") 65
  let boxes ← fields.mapM fun current => do
    (← sourceArray (← field current "coordinate_integer_box") 3).mapM sourceInterval
  let reductions ← fields.mapM fun current => do
    (← sourceArray (← field current "range_reduction_by_group") 94).mapM sourceReduction
  let reports ← fields.mapM fun current => do
    (← sourceArray (← field current "density_integer_intervals") 10).mapM sourceInterval
  let leaves ← sourceArray (← field packet "leaves") 4
  let calls ← leaves.mapM fun leaf => do decode (Array Nat) (← field leaf "field_indices")
  declareSource `rawBoxes (toExpr boxes)
  declareSource `rawReductions (toExpr reductions)
  declareSource `rawDensity (toExpr reports)
  declareSource `rawFieldCalls (toExpr calls)

generateWholeCellFieldInputs

abbrev Field := Fin 65

noncomputable section

def box (f : Field) : Rectangle := fun axis => integerInterval ((rawBoxes[f.val]!)[axis.val]!)
def reductions (f : Field) (g : Group) : Nat × Nat := (rawReductions[f.val]!)[g.val]!
def reportedDensity (f : Field) (j : LowJet) : Pair := integerInterval ((rawDensity[f.val]!)[j.val]!)

theorem source_calls_registered : ∀ q : WholeCellPartition.Quarter, ∀ call : Fin 17,
    (rawFieldCalls[q.val]!)[call.val]! < 65 := by decide +kernel

def fieldCall (q : WholeCellPartition.Quarter) (call : Fin 17) : Field :=
  ⟨(rawFieldCalls[q.val]!)[call.val]!, source_calls_registered q call⟩

theorem first_box_unchanged : box 0 = SourceRectangle.actualBox 0 := by
  funext axis
  fin_cases axis <;> decide +kernel

theorem first_reductions_unchanged : reductions 0 = SourceRectangle.groupSteps 0 := by
  funext group
  fin_cases group <;> decide +kernel

theorem first_density_unchanged (j : LowJet) :
    reportedDensity 0 j = SourceRectangle.reportedDensity 0 (fullJet j) := by
  fin_cases j <;> decide +kernel

theorem same_first_call : ∀ q : WholeCellPartition.Quarter, fieldCall q 0 = 0 := by decide +kernel

end
end LAlanine40K2025.BasinRefinement.WholeCellSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
