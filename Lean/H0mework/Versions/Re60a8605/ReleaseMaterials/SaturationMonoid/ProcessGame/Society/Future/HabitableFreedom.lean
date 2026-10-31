import Mathlib.Data.Fintype.Basic
import H0mework.Foundation.Agency.Game

/-!
# Finite habitable future freedom

Future freedom is the finite set of codes whose exact continuation fibre is
inhabited.  The construction receives neither a completed future table nor a
coverage certificate: it filters the whole finite code carrier directly by
`Nonempty (Habitable code)`.

Actionability is a second filter.  It records that an inhabited code is not
idle, so a current-only continuation cannot be confused with an available
action.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Future

universe u v

/-- The exact inhabited part of one finite common code carrier. -/
noncomputable def FutureFreedomCodes {Code : Type u} [Fintype Code]
    (Habitable : Code → Type v) : Finset Code := by
  classical
  exact Finset.univ.filter fun code => Nonempty (Habitable code)

/-- Membership is exactly inhabitation; no separately supplied coverage
judgement intervenes. -/
theorem mem_FutureFreedomCodes_iff {Code : Type u} [Fintype Code]
    (Habitable : Code → Type v) (code : Code) :
    code ∈ FutureFreedomCodes Habitable ↔ Nonempty (Habitable code) := by
  classical
  simp [FutureFreedomCodes]

/-- Inhabited future codes with a genuinely non-idle continuation. -/
noncomputable def ActionableFutureCodes {Code : Type u} [Fintype Code]
    (Habitable : Code → Type v) (Idle : Code → Prop) : Finset Code := by
  classical
  exact (FutureFreedomCodes Habitable).filter fun code => ¬ Idle code

/-- Actionability is inhabitation plus the independent non-idle condition. -/
theorem mem_ActionableFutureCodes_iff {Code : Type u} [Fintype Code]
    (Habitable : Code → Type v) (Idle : Code → Prop) (code : Code) :
    code ∈ ActionableFutureCodes Habitable Idle ↔
      Nonempty (Habitable code) ∧ ¬ Idle code := by
  classical
  simp [ActionableFutureCodes, mem_FutureFreedomCodes_iff]

/-- Every actionable code is inhabited. -/
theorem ActionableFutureCodes_subset_FutureFreedomCodes
    {Code : Type u} [Fintype Code]
    (Habitable : Code → Type v) (Idle : Code → Prop) :
    ActionableFutureCodes Habitable Idle ⊆ FutureFreedomCodes Habitable := by
  intro code member
  exact (mem_FutureFreedomCodes_iff Habitable code).mpr
    ((mem_ActionableFutureCodes_iff Habitable Idle code).mp member).1

/-- If the sole inhabited code is idle, inhabited freedom remains nonempty
while actionable freedom is empty. -/
theorem singleton_idle_separates_inhabited_from_actionable
    {Code : Type u} [Fintype Code]
    (Habitable : Code → Type v) (Idle : Code → Prop) (idle : Code)
    (codes : FutureFreedomCodes Habitable = {idle})
    (isIdle : Idle idle) :
    (FutureFreedomCodes Habitable).Nonempty ∧
      ActionableFutureCodes Habitable Idle = ∅ := by
  constructor
  · rw [codes]
    exact ⟨idle, by simp⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro code member
    have inhabited :=
      (ActionableFutureCodes_subset_FutureFreedomCodes Habitable Idle) member
    rw [codes] at inhabited
    have codeEq : code = idle := Finset.mem_singleton.mp inhabited
    exact ((mem_ActionableFutureCodes_iff Habitable Idle code).mp member).2
      (codeEq ▸ isIdle)

end Future
end Society
end ProcessGame
end SaturationMonoid
