import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Law
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.AdmissionShape
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Transport

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

/-- The existing whole ledger with its actual reparation coordinates.
A layer remembers the embedding installed at its birth, even under later finance. -/
inductive Stack (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community) :
    WorldRelationNetwork → WorldRelationNetwork → Type _
  | base (N : WorldRelationNetwork) : Stack seed community N N
  | add {N M J : WorldRelationNetwork} (prior : Stack seed community N M)
      (origin : Occurrence seed community) (balance : Balance) (view : Shape (law origin) M J) :
      Stack seed community N J

namespace Stack

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {N J : WorldRelationNetwork}

def support : {J : WorldRelationNetwork} → Stack seed community N J → N.Support → J.Support
  | _, .base _, support => support
  | _, .add prior _ balance view, baseSupport => view.support (support prior baseSupport) (.live balance)

def balances : {J : WorldRelationNetwork} → Stack seed community N J → List (Occurrence seed community × Balance)
  | _, .base _ => []
  | _, .add prior origin balance _ => balances prior ++ [(origin, balance)]

def append (prior : Stack seed community N J) (origin : Occurrence seed community) :
    Stack seed community N (ExtendedNetwork J (law origin)) :=
  .add prior origin (opening origin) (Shape.install J (law origin))

def read (atBase : N.Support) : {J : WorldRelationNetwork} → (stack : Stack seed community N J) →
    OpenResponsibilityAt J (stack.support atBase) →
      OpenResponsibilityAt N atBase ⊕ (Occurrence seed community × Balance)
  | _, .base _, entry => .inl entry
  | _, .add prior origin balance view, entry =>
    match (view.rows (prior.support atBase) (.live balance)).symm entry with
    | .inl old => read atBase prior old
    | .inr _ => .inr (origin, balance)

theorem read_old {M : WorldRelationNetwork} (prior : Stack seed community N M)
    (origin : Occurrence seed community) (balance : Balance) (view : Shape (law origin) M J)
    (atBase : N.Support) (row : OpenResponsibilityAt M (prior.support atBase)) :
    read atBase (.add prior origin balance view) (view.original (r := .live balance) row) =
      read atBase prior row := by
  simp only [read, Shape.original, Equiv.symm_apply_apply]

theorem read_fresh {M : WorldRelationNetwork} (prior : Stack seed community N M)
    (origin : Occurrence seed community) (balance : Balance) (view : Shape (law origin) M J)
    (atBase : N.Support) :
    read atBase (.add prior origin balance view) (view.repair (prior.support atBase) (.live balance)) =
      .inr (origin, balance) := by
  simp only [read, Shape.repair, Equiv.symm_apply_apply]

theorem every_balance_has_an_actual_open_row (stack : Stack seed community N J)
    (atBase : N.Support) (balance : Occurrence seed community × Balance)
    (present : balance ∈ stack.balances) :
    ∃ row : OpenResponsibilityAt J (stack.support atBase), read atBase stack row = .inr balance := by
  induction stack with
  | base => exact (List.not_mem_nil present).elim
  | add prior origin phase view ih =>
    rw [balances, List.mem_append, List.mem_singleton] at present
    rcases present with old | rfl
    · obtain ⟨row, exactRow⟩ := ih old
      exact ⟨view.original (r := .live phase) row, (read_old prior origin phase view atBase row).trans exactRow⟩
    · exact ⟨view.repair (prior.support atBase) (.live phase), read_fresh prior origin phase view atBase⟩

theorem finite (stack : Stack seed community N J) (atBase : N.Support)
    (baseFinite : Finite (OpenResponsibilityAt N atBase)) :
    Finite (OpenResponsibilityAt J (stack.support atBase)) := by
  induction stack with
  | base => exact baseFinite
  | add prior origin phase view ih => exact view.finiteRows (prior.support atBase) (.live phase) ih

theorem fibres (stack : Stack seed community N J) (baseFibres : ∀ s k, Subsingleton (N.OpenAt s k)) :
    ∀ s k, Subsingleton (J.OpenAt s k) := by
  induction stack with
  | base => exact baseFibres
  | add _ _ _ view ih => exact view.openFibres ih

end Stack

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
