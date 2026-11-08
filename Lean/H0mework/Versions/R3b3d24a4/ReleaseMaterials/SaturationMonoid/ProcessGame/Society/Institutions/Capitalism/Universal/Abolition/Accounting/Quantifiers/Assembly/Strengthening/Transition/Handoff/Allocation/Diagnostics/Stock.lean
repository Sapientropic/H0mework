import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics.Tags
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Stock
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Inspect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open Reserve

variable {n : ℕ} {Row Address Item : Type*} [DecidableEq Address]

inductive StockCut (Item : Type*) where
  | material (item : Item) (commit : ℚ)
  | terminal (items : ℕ) (finish : ℚ)

/-- A stock row identifies its address and its literal material or terminal
cut. Opening and retention refer to the whole shared held stock. -/
structure StockSite (Address Item : Type*) where
  address : Address
  cut : StockCut Item
  gate : Gate

def stockLabels (key : Address) (count : ℕ) (finish : ℚ) :
    List (Step Row Address Item) → List (StockSite Address Item)
  | [] => [⟨key, .terminal count finish, .stock⟩, ⟨key, .terminal count finish, .openingRow⟩]
  | step :: rest =>
      let cut := StockCut.material step.item step.clock
      ⟨key, cut, .stock⟩ :: ⟨key, cut, .openingRow⟩ :: ⟨key, cut, .grossDebit⟩ ::
        ⟨key, cut, .postDebitRow⟩ :: stockLabels key count finish rest

theorem stockLabels_aligned (rows : List Row) (address : Row → Address) (key : Address)
    (count : ℕ) (finish : ℚ) (pay : Item → Row → Affine n)
    (steps : List (Step Row Address Item)) (remaining : Row → Affine n) (stock : Affine n) :
    (stockLabels key count finish steps).length =
      (stockConstraintsFor rows address key pay steps remaining stock).length := by
  induction steps generalizing remaining stock with
  | nil => rfl
  | cons step rest ih =>
      simp only [stockLabels, stockConstraintsFor, List.length_cons]
      rw [← ih (fun row => (remaining row).sub (pay step.item row))
        ((stock.add (Affine.literal (step.credit key))).sub (Affine.literal (step.debit key)))]

def stockTagged (rows : List Row) (address : Row → Address) (key : Address) (count : ℕ) (finish : ℚ)
    (pay : Item → Row → Affine n) (steps : List (Step Row Address Item))
    (remaining : Row → Affine n) (stock : ℚ) : List (Tagged (StockSite Address Item) n) :=
  attach (stockLabels key count finish steps) (stockConstraints rows address key pay steps remaining stock)

theorem stockTagged_exact (rows : List Row) (address : Row → Address) (key : Address)
    (count : ℕ) (finish : ℚ) (pay : Item → Row → Affine n)
    (steps : List (Step Row Address Item)) (remaining : Row → Affine n) (stock : ℚ) :
    numeric (stockTagged rows address key count finish pay steps remaining stock) =
      stockConstraints rows address key pay steps remaining stock :=
  attach_exact _ _ (stockLabels_aligned rows address key count finish pay steps remaining _)

theorem stockTagged_labels (rows : List Row) (address : Row → Address) (key : Address)
    (count : ℕ) (finish : ℚ) (pay : Item → Row → Affine n)
    (steps : List (Step Row Address Item)) (remaining : Row → Affine n) (stock : ℚ) :
    (stockTagged rows address key count finish pay steps remaining stock).map Tagged.label =
      stockLabels key count finish steps :=
  attach_labels _ _ (stockLabels_aligned rows address key count finish pay steps remaining _)

omit [DecidableEq Address] in
theorem stockLabels_original {key : Address} {count : ℕ} {finish : ℚ}
    {steps : List (Step Row Address Item)} {site : StockSite Address Item}
    (present : site ∈ stockLabels key count finish steps) :
    site.address = key ∧
      (site.cut = .terminal count finish ∨
        ∃ step ∈ steps, site.cut = .material step.item step.clock) := by
  induction steps with
  | nil =>
      simp only [stockLabels, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      all_goals exact ⟨rfl, .inl rfl⟩
  | cons step rest ih =>
      simp only [stockLabels, List.mem_cons] at present
      rcases present with rfl | rfl | rfl | rfl | present
      · exact ⟨rfl, .inr ⟨step, List.mem_cons_self, rfl⟩⟩
      · exact ⟨rfl, .inr ⟨step, List.mem_cons_self, rfl⟩⟩
      · exact ⟨rfl, .inr ⟨step, List.mem_cons_self, rfl⟩⟩
      · exact ⟨rfl, .inr ⟨step, List.mem_cons_self, rfl⟩⟩
      · obtain ⟨same, terminal | ⟨item, found, cut⟩⟩ := ih present
        · exact ⟨same, .inl terminal⟩
        · exact ⟨same, .inr ⟨item, List.mem_cons_of_mem _ found, cut⟩⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Diagnostics
