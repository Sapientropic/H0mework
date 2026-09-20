import H0mework.Physics.GaugeAction.P286GaugeConnectionVariation

/-!
# Stage-9 exterior mother Lie representation

This module begins the algebraic lift from the actual skew-adjoint SU(7)
mother matrix to its declared derived exterior actions.  The fundamental
commutator law is proved directly from matrix multiplication; it is not
accepted through a `LieModule` instance or a finite-group equivariance
certificate.

The exterior-power commutator is derived below from the slot action.  The
pairing-skew law remains a downstream goal of this module.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineExteriorMotherLieRepresentation

open Matrix
open StageNineHolonomicField
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open StageNineP286GaugeConnectionVariation

noncomputable section

set_option autoImplicit false

/-- The actual fundamental mother action carries the matrix commutator to
the commutator of endomorphisms. -/
theorem fundamentalMotherLieAction_bracket
    (first second : SU7MotherLieMatrix) :
    fundamentalMotherLieAction (suLieBracket first second) =
      fundamentalMotherLieAction first ∘ₗ
          fundamentalMotherLieAction second -
        fundamentalMotherLieAction second ∘ₗ
          fundamentalMotherLieAction first := by
  apply LinearMap.ext
  intro vector
  unfold fundamentalMotherLieAction suLieBracket
  change
    (((first : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (second : Matrix SU7MotherIndex SU7MotherIndex ℂ) -
        (second : Matrix SU7MotherIndex SU7MotherIndex ℂ) *
          (first : Matrix SU7MotherIndex SU7MotherIndex ℂ)) *ᵥ vector) =
      (first : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ
          ((second : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector) -
        (second : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ
          ((first : Matrix SU7MotherIndex SU7MotherIndex ℂ) *ᵥ vector)
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Apply a fundamental endomorphism in one exterior slot and sum over all
slots.  Alternation is proved from the actual exterior injection: the two
terms that can survive on a repeated input cancel by a slot swap. -/
private def exteriorSlotDerivedAlternating
    (degree : ℕ)
    (action : Module.End ℂ SU7FundamentalCarrier) :
    SU7FundamentalCarrier [⋀^Fin degree]→ₗ[ℂ]
      ⋀[ℂ]^degree SU7FundamentalCarrier where
  toFun vectors :=
    ∑ position : Fin degree,
      (exteriorPower.ιMulti ℂ degree)
        (Function.update vectors position (action (vectors position)))
  map_update_add' := by
    intro _ vectors coordinate first second
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro position _
    by_cases equality : position = coordinate
    · subst position
      simp only [map_add, Function.update_self,
        (exteriorPower.ιMulti ℂ degree).map_update_add]
      apply congrArg₂ (· + ·)
      · apply congrArg (exteriorPower.ιMulti ℂ degree)
        funext candidate
        by_cases same : candidate = coordinate <;> simp [same]
      · apply congrArg (exteriorPower.ιMulti ℂ degree)
        funext candidate
        by_cases same : candidate = coordinate <;> simp [same]
    · simp only [Function.update_of_ne equality]
      let baseVectors :=
        Function.update vectors position (action (vectors position))
      calc
        _ = (exteriorPower.ιMulti ℂ degree)
              (Function.update baseVectors coordinate (first + second)) := by
          apply congrArg (exteriorPower.ιMulti ℂ degree)
          funext candidate
          by_cases atPosition : candidate = position <;>
            by_cases atCoordinate : candidate = coordinate <;>
              simp [baseVectors, atPosition, atCoordinate, equality,
                Ne.symm equality]
        _ = (exteriorPower.ιMulti ℂ degree)
                (Function.update baseVectors coordinate first) +
              (exteriorPower.ιMulti ℂ degree)
                (Function.update baseVectors coordinate second) :=
          (exteriorPower.ιMulti ℂ degree).map_update_add
            baseVectors coordinate first second
        _ = _ := by
          apply congrArg₂ (· + ·)
          · apply congrArg (exteriorPower.ιMulti ℂ degree)
            funext candidate
            by_cases atPosition : candidate = position <;>
              by_cases atCoordinate : candidate = coordinate <;>
                simp [baseVectors, atPosition, atCoordinate, equality,
                  Ne.symm equality]
          · apply congrArg (exteriorPower.ιMulti ℂ degree)
            funext candidate
            by_cases atPosition : candidate = position <;>
              by_cases atCoordinate : candidate = coordinate <;>
                simp [baseVectors, atPosition, atCoordinate, equality,
                  Ne.symm equality]
  map_update_smul' := by
    intro _ vectors coordinate scalar vector
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro position _
    by_cases equality : position = coordinate
    · subst position
      simp only [map_smul, Function.update_self,
        (exteriorPower.ιMulti ℂ degree).map_update_smul]
      apply congrArg (fun value => scalar • value)
      apply congrArg (exteriorPower.ιMulti ℂ degree)
      funext candidate
      by_cases same : candidate = coordinate <;> simp [same]
    · simp only [Function.update_of_ne equality]
      let baseVectors :=
        Function.update vectors position (action (vectors position))
      calc
        _ = (exteriorPower.ιMulti ℂ degree)
              (Function.update baseVectors coordinate (scalar • vector)) := by
          apply congrArg (exteriorPower.ιMulti ℂ degree)
          funext candidate
          by_cases atPosition : candidate = position <;>
            by_cases atCoordinate : candidate = coordinate <;>
              simp [baseVectors, atPosition, atCoordinate, equality,
                Ne.symm equality]
        _ = scalar •
              (exteriorPower.ιMulti ℂ degree)
                (Function.update baseVectors coordinate vector) :=
          (exteriorPower.ιMulti ℂ degree).map_update_smul
            baseVectors coordinate scalar vector
        _ = _ := by
          apply congrArg (fun value => scalar • value)
          apply congrArg (exteriorPower.ιMulti ℂ degree)
          funext candidate
          by_cases atPosition : candidate = position <;>
            by_cases atCoordinate : candidate = coordinate <;>
              simp [baseVectors, atPosition, atCoordinate, equality,
                Ne.symm equality]
  map_eq_zero_of_eq' := by
    intro vectors first second valuesEqual positionsDifferent
    classical
    rw [← Finset.sum_add_sum_compl {first, second},
      Finset.sum_pair positionsDifferent, Finset.sum_eq_zero, add_zero]
    · have swapped :
          Function.update vectors second (action (vectors second)) =
            Function.update vectors first (action (vectors first)) ∘
              Equiv.swap first second := by
        funext position
        rcases eq_or_ne position first with rfl | notFirst
        · simp [valuesEqual, positionsDifferent, positionsDifferent.symm]
        · rcases eq_or_ne position second with rfl | notSecond
          · simp [valuesEqual]
          · simp [notFirst, notSecond, Equiv.swap_apply_of_ne_of_ne,
              valuesEqual]
      rw [swapped]
      exact
        (exteriorPower.ιMulti ℂ degree).map_add_swap _
          positionsDifferent
    · simp only [Finset.mem_compl, Finset.mem_insert,
        Finset.mem_singleton, not_or, and_imp]
      intro position notFirst notSecond
      apply
        (exteriorPower.ιMulti ℂ degree).map_eq_zero_of_eq
          (Function.update vectors position (action (vectors position)))
          (i := first) (j := second) ?_ positionsDifferent
      simp [notFirst, notSecond, valuesEqual, Ne.symm]

/-- The slot-derived action induced by a fundamental endomorphism on the
actual exterior power. -/
noncomputable def exteriorSlotDerivedAction
    (degree : ℕ)
    (action : Module.End ℂ SU7FundamentalCarrier) :
    Module.End ℂ (⋀[ℂ]^degree SU7FundamentalCarrier) :=
  exteriorPower.alternatingMapLinearEquiv
    (exteriorSlotDerivedAlternating degree action)

@[simp]
theorem exteriorSlotDerivedAction_apply_ιMulti
    (degree : ℕ)
    (action : Module.End ℂ SU7FundamentalCarrier)
    (vectors : Fin degree → SU7FundamentalCarrier) :
    exteriorSlotDerivedAction degree action
        ((exteriorPower.ιMulti ℂ degree) vectors) =
      ∑ position : Fin degree,
        (exteriorPower.ιMulti ℂ degree)
          (Function.update vectors position (action (vectors position))) := by
  simp [exteriorSlotDerivedAction, exteriorSlotDerivedAlternating]

/-- The declared exterior action evaluates on the canonical exterior basis
by its source slot sum. -/
theorem exteriorMotherLieAction_basis_slot
    (degree : ℕ)
    (matrix : SU7MotherLieMatrix)
    (index : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree matrix (su7ExteriorBasis degree index) =
      exteriorBasisLieAction degree matrix index := by
  simp [exteriorMotherLieAction, Finsupp.single_apply]

/-- The source basis input wedges to the corresponding canonical exterior
basis vector. -/
theorem exteriorBasisInput_wedge_eq_basis_slot
    (degree : ℕ)
    (index : ExteriorBasisIndex degree) :
    (exteriorPower.ιMulti ℂ degree) (exteriorBasisInput degree index) =
      su7ExteriorBasis degree index := by
  rw [su7ExteriorBasis, exteriorPower.basis_apply]
  rfl

/-- The declared mother action is exactly the slot-derived action of the
actual fundamental mother endomorphism. -/
theorem exteriorMotherLieAction_eq_slotDerivedAction
    (degree : ℕ)
    (matrix : SU7MotherLieMatrix) :
    exteriorMotherLieAction degree matrix =
      exteriorSlotDerivedAction degree
        (fundamentalMotherLieAction matrix) := by
  apply (su7ExteriorBasis degree).ext
  intro index
  rw [exteriorMotherLieAction_basis_slot,
    ← exteriorBasisInput_wedge_eq_basis_slot,
    exteriorSlotDerivedAction_apply_ιMulti]
  unfold exteriorBasisLieAction
  apply Finset.sum_congr rfl
  intro position _
  change
    (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree matrix index position) =
      (exteriorPower.ιMulti ℂ degree)
        (Function.update (exteriorBasisInput degree index) position
          (fundamentalMotherLieAction matrix
            (exteriorBasisInput degree index position)))
  exact exteriorBasisLieActionTerm_eq_update
    degree matrix index position

/-- One ordered pair of slot writes occurring in a composite derived
action: `innerAction` writes first, then `outerAction` writes. -/
private def exteriorDoubleSlotTerm
    (degree : ℕ)
    (outerAction innerAction : Module.End ℂ SU7FundamentalCarrier)
    (vectors : Fin degree → SU7FundamentalCarrier)
    (innerPosition outerPosition : Fin degree) :
    ⋀[ℂ]^degree SU7FundamentalCarrier :=
  let afterInner :=
    Function.update vectors innerPosition
      (innerAction (vectors innerPosition))
  (exteriorPower.ιMulti ℂ degree)
    (Function.update afterInner outerPosition
      (outerAction (afterInner outerPosition)))

/-- Composite slot actions expand to the ordered double slot sum. -/
private theorem exteriorSlotDerivedAction_comp_apply_ιMulti
    (degree : ℕ)
    (outerAction innerAction : Module.End ℂ SU7FundamentalCarrier)
    (vectors : Fin degree → SU7FundamentalCarrier) :
    (exteriorSlotDerivedAction degree outerAction ∘ₗ
        exteriorSlotDerivedAction degree innerAction)
        ((exteriorPower.ιMulti ℂ degree) vectors) =
      ∑ innerPosition : Fin degree,
        ∑ outerPosition : Fin degree,
          exteriorDoubleSlotTerm degree outerAction innerAction vectors
            innerPosition outerPosition := by
  rw [LinearMap.comp_apply, exteriorSlotDerivedAction_apply_ιMulti,
    map_sum]
  apply Finset.sum_congr rfl
  intro innerPosition _
  rw [exteriorSlotDerivedAction_apply_ιMulti]
  rfl

/-- Writes in two distinct slots commute after exchanging their order and
their slot labels. -/
private theorem exteriorDoubleSlotTerm_comm_of_ne
    (degree : ℕ)
    (first second : Module.End ℂ SU7FundamentalCarrier)
    (vectors : Fin degree → SU7FundamentalCarrier)
    (innerPosition outerPosition : Fin degree)
    (positionsDifferent : innerPosition ≠ outerPosition) :
    exteriorDoubleSlotTerm degree first second vectors
        innerPosition outerPosition =
      exteriorDoubleSlotTerm degree second first vectors
        outerPosition innerPosition := by
  unfold exteriorDoubleSlotTerm
  apply congrArg (exteriorPower.ιMulti ℂ degree)
  funext candidate
  by_cases atInner : candidate = innerPosition <;>
    by_cases atOuter : candidate = outerPosition <;>
      simp [atInner, atOuter, positionsDifferent, Ne.symm positionsDifferent]

/-- On one slot, subtracting the reverse ordered write is exactly the
slot write of the commutator endomorphism. -/
private theorem exteriorDoubleSlotTerm_diagonal_sub
    (degree : ℕ)
    (first second : Module.End ℂ SU7FundamentalCarrier)
    (vectors : Fin degree → SU7FundamentalCarrier)
    (position : Fin degree) :
    exteriorDoubleSlotTerm degree first second vectors position position -
        exteriorDoubleSlotTerm degree second first vectors position position =
      (exteriorPower.ιMulti ℂ degree)
        (Function.update vectors position
          ((first ∘ₗ second - second ∘ₗ first) (vectors position))) := by
  simp [exteriorDoubleSlotTerm]

/-- Slot derivation carries the commutator of fundamental endomorphisms to
the commutator of their actual exterior-power endomorphisms. -/
theorem exteriorSlotDerivedAction_commutator
    (degree : ℕ)
    (first second : Module.End ℂ SU7FundamentalCarrier) :
    exteriorSlotDerivedAction degree
        (first ∘ₗ second - second ∘ₗ first) =
      exteriorSlotDerivedAction degree first ∘ₗ
          exteriorSlotDerivedAction degree second -
      exteriorSlotDerivedAction degree second ∘ₗ
          exteriorSlotDerivedAction degree first := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro vectors
  change
    exteriorSlotDerivedAction degree
        (first ∘ₗ second - second ∘ₗ first)
        ((exteriorPower.ιMulti ℂ degree) vectors) =
      (exteriorSlotDerivedAction degree first ∘ₗ
          exteriorSlotDerivedAction degree second -
        exteriorSlotDerivedAction degree second ∘ₗ
          exteriorSlotDerivedAction degree first)
        ((exteriorPower.ιMulti ℂ degree) vectors)
  rw [exteriorSlotDerivedAction_apply_ιMulti, LinearMap.sub_apply,
    exteriorSlotDerivedAction_comp_apply_ιMulti,
    exteriorSlotDerivedAction_comp_apply_ιMulti]
  have swapSecond :
      (∑ innerPosition : Fin degree,
          ∑ outerPosition : Fin degree,
            exteriorDoubleSlotTerm degree second first vectors
              innerPosition outerPosition) =
        ∑ innerPosition : Fin degree,
          ∑ outerPosition : Fin degree,
            exteriorDoubleSlotTerm degree second first vectors
              outerPosition innerPosition := by
    rw [Finset.sum_comm]
  rw [swapSecond, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro innerPosition _
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single innerPosition]
  · exact
      (exteriorDoubleSlotTerm_diagonal_sub degree first second vectors
        innerPosition).symm
  · intro outerPosition _ positionsDifferent
    rw [exteriorDoubleSlotTerm_comm_of_ne degree first second vectors
        innerPosition outerPosition (Ne.symm positionsDifferent),
      sub_self]
  · simp

/-- The actual mother Lie bracket is represented by the commutator on every
declared exterior degree.  The proof is produced from the fundamental matrix
action and the slot construction; no exterior `LieModule` receipt is used. -/
theorem exteriorMotherLieAction_bracket
    (degree : ℕ)
    (first second : SU7MotherLieMatrix) :
    exteriorMotherLieAction degree (suLieBracket first second) =
      exteriorMotherLieAction degree first ∘ₗ
          exteriorMotherLieAction degree second -
        exteriorMotherLieAction degree second ∘ₗ
          exteriorMotherLieAction degree first := by
  simp only [exteriorMotherLieAction_eq_slotDerivedAction]
  rw [fundamentalMotherLieAction_bracket]
  exact exteriorSlotDerivedAction_commutator degree
    (fundamentalMotherLieAction first)
    (fundamentalMotherLieAction second)

end

end SaturationMonoid.PhysicsCore.StageNineExteriorMotherLieRepresentation
