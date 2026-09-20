import H0mework.Physics.Matter.SU7MotherMatterNormalizerNoGo
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RepresentationTheory.Basic

/-!
# An actual exterior-power SU(7) matter representation candidate

Stage 7 cannot repair the failed adjoint/P508 interpretation by renaming its
slots.  This module changes the representation itself.  Starting from the
actual fundamental matrix action of `Matrix.specialUnitaryGroup`, it applies
the functorial `exteriorPower.map` construction and forms

`Λ⁶ V ⊕ Λ² V ⊕ Λ⁴ V`.

The three summands have dimensions `7`, `21`, and `35`; their degree signature
`(6,2,4)` is not invariant under SU(7) exterior conjugation `k ↦ 7-k`.
This is the small exterior-spinor candidate historically written
`7̅ ⊕ 21 ⊕ 3̅5`.

The module proves the representation law from actual matrix multiplication,
not from a stored compatibility Boolean.  It also records the standard finite
exterior anomaly-index calculation as a candidate-selection invariant.  That
index calculation is not yet the promised restriction-level anomaly trace;
the latter must be recomputed from the actual exterior basis in the next
module before any physical matter credential is created.
-/

namespace SaturationMonoid.PhysicsCore.SU7ExteriorMatterRepresentation

open Matrix
open SU7MotherLieAlgebra

open scoped TensorProduct

noncomputable section

abbrev SU7MotherGroup := Matrix.specialUnitaryGroup SU7MotherIndex ℂ
abbrev SU7FundamentalCarrier := SU7MotherIndex → ℂ

/-- The actual seven-dimensional SU(7) matrix action. -/
def su7FundamentalRepresentation :
    Representation ℂ SU7MotherGroup SU7FundamentalCarrier where
  toFun groupElement :=
    Matrix.mulVecLin
      (groupElement : Matrix SU7MotherIndex SU7MotherIndex ℂ)
  map_one' := by
    apply LinearMap.ext
    intro vector
    simp
  map_mul' first second := by
    apply LinearMap.ext
    intro vector
    change
      (((first : SU7MotherGroup) :
          Matrix SU7MotherIndex SU7MotherIndex ℂ) *
        ((second : SU7MotherGroup) :
          Matrix SU7MotherIndex SU7MotherIndex ℂ)) *ᵥ vector =
      (first : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ
        ((second : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector)
    rw [Matrix.mulVec_mulVec]

/-- Every exterior power is an actual SU(7) representation by functoriality
of `exteriorPower.map`. -/
def su7ExteriorPowerRepresentation (degree : ℕ) :
    Representation ℂ SU7MotherGroup
      (⋀[ℂ]^degree SU7FundamentalCarrier) where
  toFun groupElement :=
    exteriorPower.map degree (su7FundamentalRepresentation groupElement)
  map_one' := by
    simp [Module.End.one_eq_id]
  map_mul' first second := by
    simp [Module.End.mul_eq_comp, exteriorPower.map_comp]

/-- Carrier of the new exterior-spinor matter candidate.  Products are used
as the finite direct sum of vector spaces. -/
abbrev SU7ExteriorSpinorMatterCarrier :=
  (⋀[ℂ]^6 SU7FundamentalCarrier) ×
    ((⋀[ℂ]^2 SU7FundamentalCarrier) ×
      (⋀[ℂ]^4 SU7FundamentalCarrier))

/-- Actual SU(7) action on `Λ⁶ V ⊕ Λ² V ⊕ Λ⁴ V`. -/
def su7ExteriorSpinorMatterRepresentation :
    Representation ℂ SU7MotherGroup SU7ExteriorSpinorMatterCarrier :=
  (su7ExteriorPowerRepresentation 6).prod
    ((su7ExteriorPowerRepresentation 2).prod
      (su7ExteriorPowerRepresentation 4))

theorem su7FundamentalCarrier_finrank :
    Module.finrank ℂ SU7FundamentalCarrier = 7 := by
  rw [Module.finrank_pi]
  exact su7MotherIndex_card

theorem su7ExteriorPower_finrank (degree : ℕ) :
    Module.finrank ℂ (⋀[ℂ]^degree SU7FundamentalCarrier) =
      Nat.choose 7 degree := by
  rw [exteriorPower.finrank_eq, su7FundamentalCarrier_finrank]

/-- The actual carrier has `7+21+35=63` complex components; canonical `17`
is not an input. -/
theorem su7ExteriorSpinorMatterCarrier_finrank :
    Module.finrank ℂ SU7ExteriorSpinorMatterCarrier = 63 := by
  rw [Module.finrank_prod, Module.finrank_prod,
    su7ExteriorPower_finrank, su7ExteriorPower_finrank,
    su7ExteriorPower_finrank]
  norm_num [Nat.choose]

def exteriorSpinorDegree : Fin 3 → ℕ
  | 0 => 6
  | 1 => 2
  | 2 => 4

def conjugateExteriorDegree (degree : ℕ) : ℕ :=
  7 - degree

/-- Signature-level chirality: degree `6` occurs, while its conjugate degree
`1` does not.  No chirality Boolean is stored in the representation datum. -/
theorem exteriorSpinorSignature_chiral :
    (∃ index : Fin 3, exteriorSpinorDegree index = 6) ∧
      ¬ (∃ index : Fin 3,
        exteriorSpinorDegree index = conjugateExteriorDegree 6) := by
  constructor
  · exact ⟨0, rfl⟩
  · rintro ⟨index, hindex⟩
    fin_cases index <;>
      norm_num [exteriorSpinorDegree, conjugateExteriorDegree] at hindex

/-- SU(7)'s standard cubic anomaly index for exterior powers, specialized to
rank seven.  This finite index is kept separate from the downstream actual
P286 trace calculation. -/
def su7ExteriorCubicAnomalyIndex : ℕ → ℤ
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => -2
  | 5 => -3
  | 6 => -1
  | _ => 0

def exteriorSpinorCandidateAnomalyIndex : ℤ :=
  ∑ index : Fin 3,
    su7ExteriorCubicAnomalyIndex (exteriorSpinorDegree index)

theorem exteriorSpinorCandidateAnomalyIndex_eq_zero :
    exteriorSpinorCandidateAnomalyIndex = 0 := by
  norm_num [exteriorSpinorCandidateAnomalyIndex, exteriorSpinorDegree,
    su7ExteriorCubicAnomalyIndex, Fin.sum_univ_three]

end
end SaturationMonoid.PhysicsCore.SU7ExteriorMatterRepresentation
