import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell2.FieldsCall160Field

/-! One actual rectangle carries two registered source restrictions and the full D3 field calculation. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.Source

open SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceFields WholeBandSource
open WholeBandMatrix IntervalParameterMap ContinuousGradient
noncomputable section

structure InitialFieldMaterial where
  calls : Fin 2 → FullBandCall
  box : Rectangle
  reductions : SourceRectangle.Group → Nat × Nat
  cache : WholeBandCache.Material
  ao : LowJet → Basis → Pair
  density : Matrix Basis Basis ℚ
  rows : Rows
  computed : FieldBox
  reported : Fin 2 → FieldBox
  actualGradient : Point → Point
  actualHessian : Point → Fin 3 → Fin 3 → ℝ

def material : InitialFieldMaterial where
  calls := ![128,160]
  box := callBox 128
  reductions := callReductions 128
  cache := Call128.material
  ao := Call128.sourceAO
  density := densityMatrix
  rows := Call128.matrixRows
  computed := calculatedField Call128.matrixRows
  reported := fun i => recordedCallField (![128,160] i)
  actualGradient := sourceGradient
  actualHessian := sourceHessian

theorem same_original_restrictions (i : Fin 2) :
    callBox (material.calls i) = material.box ∧
    callReductions (material.calls i) = material.reductions ∧
    callReportedDensity (material.calls i) = callReportedDensity 128 := by
  fin_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem call_addresses_injective : Function.Injective material.calls := by decide +kernel

def boxWitness : Point := fun axis => (material.box axis).1

theorem boxWitness_inside : InRectangle material.box boxWitness := by
  have bounds : ∀ axis : Fin 3, (material.box axis).1 ≤ (material.box axis).2 := by
    intro axis
    fin_cases axis <;> decide +kernel
  intro axis
  constructor
  · exact le_rfl
  · change ((material.box axis).1 : ℝ) ≤ ((material.box axis).2 : ℝ)
    exact_mod_cast bounds axis

theorem box_nonempty : ∃ x, InRectangle material.box x := ⟨boxWitness, boxWitness_inside⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell2.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
