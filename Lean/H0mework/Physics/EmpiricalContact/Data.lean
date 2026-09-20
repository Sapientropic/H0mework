import H0mework.Physics.Bell.Preparation

/-! T2 input: the released first-100000-trial count table, not a verdict.
The raw-to-count correspondence belongs to the independent custody/recompute
evidence. This module neither reads the archive nor changes a frozen model. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical

def lockHash : String :=
  "f644d2c18e314f7ddc8733ddf4361fb8c72ac1315dc09ae36fe4e4b73cb13286"

def releasedResultHash : String :=
  "1b8e10da7818528afc945e36e6874fa02d325628d791be5727ee607d8bda253d"

/-- Rows 00,01,10,11; columns ++,+-,-+,--; no readout sign change. -/
def counts : Fin 4 → Fin 4 → ℕ :=
  !![9683, 3006, 3027, 9506;
     3001, 9407, 9224, 3246;
     8904, 2787, 3553, 9644;
     9072, 2694, 3248, 9998]

structure ReleasedContact where
  lockHash : String
  resultHash : String
  table : Fin 4 → Fin 4 → ℕ

def releasedContact : ReleasedContact := ⟨lockHash, releasedResultHash, counts⟩

def highCountAt (table : Fin 4 → Fin 4 → ℕ) : ℕ :=
  table 0 0 + table 0 3 + table 1 0 + table 1 3 +
  table 2 1 + table 2 2 + table 3 0 + table 3 3

def lowCountAt (table : Fin 4 → Fin 4 → ℕ) : ℕ :=
  table 0 1 + table 0 2 + table 1 1 + table 1 2 +
  table 2 0 + table 2 3 + table 3 1 + table 3 2

def highCount : ℕ := highCountAt releasedContact.table
def lowCount : ℕ := lowCountAt releasedContact.table

theorem highCount_value : highCount = 50846 := by decide
theorem lowCount_value : lowCount = 49154 := by decide
theorem complete_count : highCount + lowCount = 100000 := by
  rw [highCount_value, lowCount_value]

end SaturationMonoid.PhysicsCore.Stage10.Empirical
