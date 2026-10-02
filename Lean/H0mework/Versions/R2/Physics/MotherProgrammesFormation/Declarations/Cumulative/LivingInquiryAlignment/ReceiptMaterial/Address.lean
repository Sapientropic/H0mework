import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Tower
import Mathlib.SetTheory.ZFC.Ordinal

/-! Complete carrier addresses in one already defined rank stage.

The target type occurs only in coverage. An ordinal representation with a
fixed rank marker makes all of its elements enter the same Stage through
the existing covers_at_rank theorem. This does not supply a Stage material
reader or identify an ordinal with an original physical visit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptAddress

open MotherReceiptArena
open scoped Classical
noncomputable section
universe u

def bound (A : Type u) : Ordinal.{u} := Ordinal.type (@WellOrderingRel A)

def index {A : Type u} (value : A) : Ordinal.{u} :=
  Ordinal.typein (@WellOrderingRel A) value

theorem index_lt_bound {A : Type u} (value : A) : index value < bound A :=
  Ordinal.typein_lt_type (@WellOrderingRel A) value

theorem index_injective (A : Type u) : Function.Injective (@index A) :=
  Ordinal.typein_injective (@WellOrderingRel A)

/-- The marker has strictly larger rank than every variable code. -/
def marked {A : Type u} (value : A) : ZFSet.{u} :=
  {(bound A).toZFSet, (index value).toZFSet}

theorem marked_rank {A : Type u} (value : A) :
    (marked value).rank = Order.succ (bound A) := by
  rw [marked, ZFSet.rank_pair, Ordinal.rank_toZFSet, Ordinal.rank_toZFSet]
  exact max_eq_left (Order.succ_le_succ (index_lt_bound value).le)

theorem marked_injective (A : Type u) : Function.Injective (@marked A) := by
  intro first last same
  have member : (index first).toZFSet ∈ marked first := ZFSet.mem_pair.mpr (.inr rfl)
  rw [same] at member
  rcases ZFSet.mem_pair.mp member with atMarker | atIndex
  · exact False.elim ((index_lt_bound first).ne (Ordinal.toZFSet_injective atMarker))
  · exact index_injective A (Ordinal.toZFSet_injective atIndex)

theorem stageValue_cast {first last : Ordinal.{u}} (same : first = last)
    (value : Stage first) :
    stageValue last (Eq.mp (congrArg Stage same) value) = stageValue first value := by
  cases same
  rfl

/-- A coverage witness selected from the target-independent tower. -/
def address {A : Type u} (value : A) : Stage (Order.succ (bound A)) :=
  Eq.mp (congrArg Stage (marked_rank value)) (covers_at_rank (marked value)).choose

theorem address_value {A : Type u} (value : A) :
    stageValue (Order.succ (bound A)) (address value) = marked value := by
  exact (stageValue_cast (marked_rank value) _).trans
    (covers_at_rank (marked value)).choose_spec

def carrierAddress (A : Type u) : A ↪ Stage (Order.succ (bound A)) where
  toFun := address
  inj' := by
    intro first last same
    apply marked_injective A
    exact (address_value first).symm.trans
      ((congrArg (stageValue (Order.succ (bound A))) same).trans (address_value last))

theorem every_carrier (A : Type u) :
    ∃ rank : Ordinal.{u}, Nonempty (A ↪ Stage rank) :=
  ⟨Order.succ (bound A), ⟨carrierAddress A⟩⟩


end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptAddress
