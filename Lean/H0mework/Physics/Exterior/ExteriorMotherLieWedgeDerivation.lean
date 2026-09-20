import H0mework.Physics.Exterior.ExteriorMotherLieRepresentation
import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

/-!
# Stage-9 exterior mother Lie wedge derivation

The actual slot-derived exterior action obeys the graded-product Leibniz law.
The proof below works on decomposable exterior inputs, splits the combined
slot sum into its left and right blocks, and then extends by the universal
property of each exterior power.

This is an infinitesimal statement.  It does not reuse finite SU(7)
equivariance as a substitute for differentiation, and it accepts no Ward,
stationarity, residual, source, receipt, or target-equality premise.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineExteriorMotherLieWedgeDerivation

open StageNineExteriorMotherLieRepresentation
open StageNineHolonomicField
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- Exterior multiplication of two decomposable inputs is the decomposable
input obtained by appending their slot families. -/
private theorem exteriorWedge_ιMulti
    (firstDegree secondDegree : ℕ)
    (first : Fin firstDegree → SU7FundamentalCarrier)
    (second : Fin secondDegree → SU7FundamentalCarrier) :
    exteriorWedge firstDegree secondDegree
        ((exteriorPower.ιMulti ℂ firstDegree) first)
        ((exteriorPower.ιMulti ℂ secondDegree) second) =
      (exteriorPower.ιMulti ℂ (firstDegree + secondDegree))
        (Fin.append first second) := by
  apply Subtype.ext
  change
    ExteriorAlgebra.ιMulti ℂ firstDegree first *
        ExteriorAlgebra.ιMulti ℂ secondDegree second =
      ExteriorAlgebra.ιMulti ℂ (firstDegree + secondDegree)
        (Fin.append first second)
  exact ExteriorAlgebra.ιMulti_mul_ιMulti first second

/-- Updating a slot in the left block of an appended family updates only the
left family. -/
private theorem update_append_castAdd
    (firstDegree secondDegree : ℕ)
    (first : Fin firstDegree → SU7FundamentalCarrier)
    (second : Fin secondDegree → SU7FundamentalCarrier)
    (position : Fin firstDegree)
    (value : SU7FundamentalCarrier) :
    Function.update (Fin.append first second)
        (Fin.castAdd secondDegree position) value =
      Fin.append (Function.update first position value) second := by
  funext candidate
  induction candidate using Fin.addCases with
  | left candidate =>
      by_cases same : candidate = position <;> simp [same]
  | right candidate =>
      have indexNe :
          Fin.castAdd secondDegree position ≠
            Fin.natAdd firstDegree candidate := by
        intro equality
        have valueEquality := congrArg Fin.val equality
        simp only [Fin.val_castAdd, Fin.val_natAdd] at valueEquality
        omega
      simp [indexNe.symm]

/-- Updating a slot in the right block of an appended family updates only the
right family. -/
private theorem update_append_natAdd
    (firstDegree secondDegree : ℕ)
    (first : Fin firstDegree → SU7FundamentalCarrier)
    (second : Fin secondDegree → SU7FundamentalCarrier)
    (position : Fin secondDegree)
    (value : SU7FundamentalCarrier) :
    Function.update (Fin.append first second)
        (Fin.natAdd firstDegree position) value =
      Fin.append first (Function.update second position value) := by
  funext candidate
  induction candidate using Fin.addCases with
  | left candidate =>
      have indexNe :
          Fin.natAdd firstDegree position ≠
            Fin.castAdd secondDegree candidate := by
        intro equality
        have valueEquality := congrArg Fin.val equality
        simp only [Fin.val_natAdd, Fin.val_castAdd] at valueEquality
        omega
      simp [indexNe.symm]
  | right candidate =>
      by_cases same : candidate = position <;> simp [same]

/-- The slot-derived action satisfies the wedge Leibniz law on two
decomposable exterior inputs. -/
private theorem exteriorSlotDerivedAction_exteriorWedge_ιMulti
    (firstDegree secondDegree : ℕ)
    (action : Module.End ℂ SU7FundamentalCarrier)
    (first : Fin firstDegree → SU7FundamentalCarrier)
    (second : Fin secondDegree → SU7FundamentalCarrier) :
    exteriorSlotDerivedAction (firstDegree + secondDegree) action
        (exteriorWedge firstDegree secondDegree
          ((exteriorPower.ιMulti ℂ firstDegree) first)
          ((exteriorPower.ιMulti ℂ secondDegree) second)) =
      exteriorWedge firstDegree secondDegree
          (exteriorSlotDerivedAction firstDegree action
            ((exteriorPower.ιMulti ℂ firstDegree) first))
          ((exteriorPower.ιMulti ℂ secondDegree) second) +
        exteriorWedge firstDegree secondDegree
          ((exteriorPower.ιMulti ℂ firstDegree) first)
          (exteriorSlotDerivedAction secondDegree action
            ((exteriorPower.ιMulti ℂ secondDegree) second)) := by
  rw [exteriorWedge_ιMulti,
    exteriorSlotDerivedAction_apply_ιMulti,
    exteriorSlotDerivedAction_apply_ιMulti,
    exteriorSlotDerivedAction_apply_ιMulti]
  simp only [map_sum, LinearMap.sum_apply]
  simp_rw [exteriorWedge_ιMulti]
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro position _
    rw [Fin.append_left, update_append_castAdd]
  · apply Finset.sum_congr rfl
    intro position _
    rw [Fin.append_right, update_append_natAdd]

/-- Every actual slot-derived exterior action is a derivation of the exterior
wedge. -/
theorem exteriorSlotDerivedAction_exteriorWedge
    (firstDegree secondDegree : ℕ)
    (action : Module.End ℂ SU7FundamentalCarrier)
    (first : ⋀[ℂ]^firstDegree SU7FundamentalCarrier)
    (second : ⋀[ℂ]^secondDegree SU7FundamentalCarrier) :
    exteriorSlotDerivedAction (firstDegree + secondDegree) action
        (exteriorWedge firstDegree secondDegree first second) =
      exteriorWedge firstDegree secondDegree
          (exteriorSlotDerivedAction firstDegree action first) second +
        exteriorWedge firstDegree secondDegree first
          (exteriorSlotDerivedAction secondDegree action second) := by
  let leftFirst :
      (⋀[ℂ]^firstDegree SU7FundamentalCarrier) →ₗ[ℂ]
        ⋀[ℂ]^(firstDegree + secondDegree) SU7FundamentalCarrier :=
    (exteriorSlotDerivedAction (firstDegree + secondDegree) action).comp
      ((exteriorWedge firstDegree secondDegree).flip second)
  let rightFirst :
      (⋀[ℂ]^firstDegree SU7FundamentalCarrier) →ₗ[ℂ]
        ⋀[ℂ]^(firstDegree + secondDegree) SU7FundamentalCarrier :=
    ((exteriorWedge firstDegree secondDegree).flip second).comp
        (exteriorSlotDerivedAction firstDegree action) +
      (exteriorWedge firstDegree secondDegree).flip
        (exteriorSlotDerivedAction secondDegree action second)
  have firstMapsEqual : leftFirst = rightFirst := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro firstFamily
    let leftSecond :
        (⋀[ℂ]^secondDegree SU7FundamentalCarrier) →ₗ[ℂ]
          ⋀[ℂ]^(firstDegree + secondDegree) SU7FundamentalCarrier :=
      (exteriorSlotDerivedAction (firstDegree + secondDegree) action).comp
        (exteriorWedge firstDegree secondDegree
          ((exteriorPower.ιMulti ℂ firstDegree) firstFamily))
    let rightSecond :
        (⋀[ℂ]^secondDegree SU7FundamentalCarrier) →ₗ[ℂ]
          ⋀[ℂ]^(firstDegree + secondDegree) SU7FundamentalCarrier :=
      exteriorWedge firstDegree secondDegree
          (exteriorSlotDerivedAction firstDegree action
            ((exteriorPower.ιMulti ℂ firstDegree) firstFamily)) +
        (exteriorWedge firstDegree secondDegree
          ((exteriorPower.ιMulti ℂ firstDegree) firstFamily)).comp
            (exteriorSlotDerivedAction secondDegree action)
    have secondMapsEqual : leftSecond = rightSecond := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro secondFamily
      exact exteriorSlotDerivedAction_exteriorWedge_ιMulti
        firstDegree secondDegree action firstFamily secondFamily
    exact LinearMap.congr_fun secondMapsEqual second
  exact LinearMap.congr_fun firstMapsEqual first

/-- The declared mother Lie action is therefore a derivation of the actual
exterior wedge. -/
theorem exteriorMotherLieAction_exteriorWedge
    (firstDegree secondDegree : ℕ)
    (matrix : SU7MotherLieMatrix)
    (first : ⋀[ℂ]^firstDegree SU7FundamentalCarrier)
    (second : ⋀[ℂ]^secondDegree SU7FundamentalCarrier) :
    exteriorMotherLieAction (firstDegree + secondDegree) matrix
        (exteriorWedge firstDegree secondDegree first second) =
      exteriorWedge firstDegree secondDegree
          (exteriorMotherLieAction firstDegree matrix first) second +
        exteriorWedge firstDegree secondDegree first
          (exteriorMotherLieAction secondDegree matrix second) := by
  simpa only [exteriorMotherLieAction_eq_slotDerivedAction] using
    exteriorSlotDerivedAction_exteriorWedge firstDegree secondDegree
      (fundamentalMotherLieAction matrix) first second

/-- Infinitesimal equivariance of the actual exterior Yukawa mass map.  Both
the degree-two matter input and the independent degree-four scalar input
contribute to the degree-six response. -/
theorem exteriorYukawaMassMap_motherLieAction
    (matrix : SU7MotherLieMatrix)
    (scalar : ExteriorBreakingScalarCarrier)
    (matter : ExteriorDegreeTwoMatterCarrier) :
    exteriorMotherLieAction 6 matrix
        (exteriorYukawaMassMap scalar matter) =
      exteriorYukawaMassMap scalar
          (exteriorMotherLieAction 2 matrix matter) +
        exteriorYukawaMassMap
          (exteriorMotherLieAction 4 matrix scalar) matter := by
  simpa [exteriorYukawaMassMap] using
    exteriorMotherLieAction_exteriorWedge 2 4 matrix matter scalar

end

end SaturationMonoid.PhysicsCore.StageNineExteriorMotherLieWedgeDerivation
