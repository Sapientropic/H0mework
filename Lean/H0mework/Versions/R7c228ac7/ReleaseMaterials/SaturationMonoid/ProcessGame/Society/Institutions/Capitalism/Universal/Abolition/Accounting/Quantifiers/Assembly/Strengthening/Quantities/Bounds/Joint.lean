import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Resolve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Address : Type u}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- An independent bound at each address need not be a jointly possible
profile. The joint image keeps the originating paid script. -/
def ideal (source : C) (read : Script → Address → EReal) (address : Address) : EReal :=
  lower source (fun script => read script address)

theorem the_joint_ideal_is_paid_or_every_completion_has_an_exact_gap
    (source : C) (read : Script → Address → EReal) :
    (∃ script, Settled source script ∧ read script = ideal source read) ∨
    (∀ script, Settled source script →
      ∃ address, ideal source read address < read script address) := by
  classical
  by_cases reached : ideal source read ∈ values source read
  · exact .inl ((observed_iff_settled source read _).mp reached)
  right
  intro script paid
  by_contra! all
  have eq : read script = ideal source read := by
    funext address
    exact le_antisymm (all address) (lower_le source _ script paid.toFeasible)
  exact reached ⟨script, paid.toFeasible, eq⟩

structure Tradeoff (source : C) (read : Script → Address → EReal) (left right : Script) where
  leftPaid : Settled source left
  rightPaid : Settled source right
  leftBurden : Address
  rightBurden : Address
  leftHigher : read right leftBurden < read left leftBurden
  rightHigher : read left rightBurden < read right rightBurden

/-- Two plans may be compared without giving anyone authority to scalarize
their original burdens. A strict crossing names both affected addresses. -/
theorem compare_paid (source : C) (read : Script → Address → EReal)
    (left right : Script) (leftPaid : Settled source left) (rightPaid : Settled source right) :
    (∀ address, read left address ≤ read right address) ∨
    (∀ address, read right address ≤ read left address) ∨
    Nonempty (Tradeoff source read left right) := by
  classical
  by_cases leftLe : ∀ address, read left address ≤ read right address
  · exact .inl leftLe
  by_cases rightLe : ∀ address, read right address ≤ read left address
  · exact .inr (.inl rightLe)
  obtain ⟨leftBurden, leftGt⟩ := not_forall.mp leftLe
  obtain ⟨rightBurden, rightGt⟩ := not_forall.mp rightLe
  exact .inr (.inr ⟨⟨leftPaid, rightPaid, leftBurden, rightBurden,
    lt_of_not_ge leftGt, lt_of_not_ge rightGt⟩⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds
