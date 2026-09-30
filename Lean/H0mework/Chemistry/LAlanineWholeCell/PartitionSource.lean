import H0mework.Chemistry.LAlanineRefinementGeometry.Parsing
import H0mework.Chemistry.LAlanineContinuousSource.CellBounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellPartition

open Lean Elab Term SourceGaussianModel SourceFiniteData
open Inertia.SourceParsing

elab "sourceHalfFlowLiteral" : term => do
  let packet ← Geometry.Parsing.verifiedPacket
  let protocol ← field packet "protocol"
  let value ← decode String (← field protocol "half_flow_parameter_hex")
  pure (toExpr (← Geometry.Parsing.positiveHexDyadic value))

def rawHalfFlow : Int × Nat := sourceHalfFlowLiteral

abbrev Quarter := Fin 4
abbrev Cut := Fin 5

noncomputable section

def halfFlowQ : ℚ := ratRead rawHalfFlow
def fullLowerQ (axis : Fin 3) : ℚ :=
  if axis = 2 then -halfFlowQ else SourceCellGeometry.cellLowerQ axis
def fullUpperQ (axis : Fin 3) : ℚ :=
  if axis = 2 then halfFlowQ else SourceCellGeometry.cellUpperQ axis

def midpointQ (lo hi : ℚ) : ℚ := (lo + hi) / 2
def middleQ : ℚ := midpointQ (fullLowerQ 2) (fullUpperQ 2)
def cutQ : Cut → ℚ :=
  ![fullLowerQ 2, midpointQ (fullLowerQ 2) middleQ, middleQ,
    midpointQ middleQ (fullUpperQ 2), fullUpperQ 2]
def lowerCut (q : Quarter) : Cut := ⟨q.val, by omega⟩
def upperCut (q : Quarter) : Cut := ⟨q.val + 1, by omega⟩
def quarterLowerQ (q : Quarter) (axis : Fin 3) : ℚ :=
  if axis = 2 then cutQ (lowerCut q) else fullLowerQ axis
def quarterUpperQ (q : Quarter) (axis : Fin 3) : ℚ :=
  if axis = 2 then cutQ (upperCut q) else fullUpperQ axis

def fullLower : Point := fun axis => (fullLowerQ axis : ℝ)
def fullUpper : Point := fun axis => (fullUpperQ axis : ℝ)
def quarterLower (q : Quarter) : Point := fun axis => (quarterLowerQ q axis : ℝ)
def quarterUpper (q : Quarter) : Point := fun axis => (quarterUpperQ q axis : ℝ)
def fullDomain : Set Point := Set.Icc fullLower fullUpper
def quarterDomain (q : Quarter) : Set Point := Set.Icc (quarterLower q) (quarterUpper q)

theorem halfFlow_exact : halfFlowQ = (1 / 2 : ℚ) := by decide +kernel
theorem cuts_exact : cutQ = ![-(1 / 2), -(1 / 4), 0, 1 / 4, 1 / 2] := by
  funext i
  fin_cases i <;> decide +kernel

theorem alpha_v_preserved (axis : Fin 3) (h : axis ≠ 2) :
    fullLowerQ axis = SourceCellGeometry.cellLowerQ axis ∧
      fullUpperQ axis = SourceCellGeometry.cellUpperQ axis := by
  simp [fullLowerQ, fullUpperQ, h]

theorem full_ordered : ∀ axis : Fin 3, fullLowerQ axis < fullUpperQ axis := by decide +kernel
theorem quarter_ordered : ∀ q : Quarter, ∀ axis : Fin 3,
    quarterLowerQ q axis < quarterUpperQ q axis := by decide +kernel

end
end LAlanine40K2025.BasinRefinement.WholeCellPartition
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
