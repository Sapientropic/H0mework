import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.CumulativeArenaTower
import Mathlib.SetTheory.ZFC.Ordinal
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.OriginalRoot

/-! Complete carrier addresses in one already defined rank stage.

The target type occurs only in coverage. An ordinal representation with a
fixed rank marker makes all of its elements enter the same Stage through
the existing covers_at_rank theorem. This does not supply a Stage material
reader or identify an ordinal with an original physical visit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAddressCoverage

open MotherCumulativeArena
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

def bound (A : Type) : Ordinal.{0} := Ordinal.type (@WellOrderingRel A)

def index {A : Type} (value : A) : Ordinal.{0} :=
  Ordinal.typein (@WellOrderingRel A) value

theorem index_lt_bound {A : Type} (value : A) : index value < bound A :=
  Ordinal.typein_lt_type (@WellOrderingRel A) value

theorem index_injective (A : Type) : Function.Injective (@index A) :=
  Ordinal.typein_injective (@WellOrderingRel A)

/-- The marker has strictly larger rank than every variable code. -/
def marked {A : Type} (value : A) : ZFSet.{0} :=
  {(bound A).toZFSet, (index value).toZFSet}

theorem marked_rank {A : Type} (value : A) :
    (marked value).rank = Order.succ (bound A) := by
  rw [marked, ZFSet.rank_pair, Ordinal.rank_toZFSet, Ordinal.rank_toZFSet]
  exact max_eq_left (Order.succ_le_succ (index_lt_bound value).le)

theorem marked_injective (A : Type) : Function.Injective (@marked A) := by
  intro first last same
  have member : (index first).toZFSet ∈ marked first := ZFSet.mem_pair.mpr (.inr rfl)
  rw [same] at member
  rcases ZFSet.mem_pair.mp member with atMarker | atIndex
  · exact False.elim ((index_lt_bound first).ne (Ordinal.toZFSet_injective atMarker))
  · exact index_injective A (Ordinal.toZFSet_injective atIndex)

theorem stageValue_cast {first last : Ordinal.{0}} (same : first = last)
    (value : Stage first) :
    stageValue last (Eq.mp (congrArg Stage same) value) = stageValue first value := by
  cases same
  rfl

/-- A coverage witness selected from the target-independent tower. -/
def address {A : Type} (value : A) : Stage (Order.succ (bound A)) :=
  Eq.mp (congrArg Stage (marked_rank value)) (covers_at_rank (marked value)).choose

theorem address_value {A : Type} (value : A) :
    stageValue (Order.succ (bound A)) (address value) = marked value := by
  exact (stageValue_cast (marked_rank value) _).trans
    (covers_at_rank (marked value)).choose_spec

def carrierAddress (A : Type) : A ↪ Stage (Order.succ (bound A)) where
  toFun := address
  inj' := by
    intro first last same
    apply marked_injective A
    exact (address_value first).symm.trans
      ((congrArg (stageValue (Order.succ (bound A))) same).trans (address_value last))

theorem every_carrier (A : Type) :
    ∃ rank : Ordinal.{0}, Nonempty (A ↪ Stage rank) :=
  ⟨Order.succ (bound A), ⟨carrierAddress A⟩⟩

/-- All four existing factory address operands are placed in one carrier. -/
abbrev RootAddressTotal {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) :=
  MotherJointWrite.SourceWriteTotal root.source.restructuringSource.compiler.ledgerCompiler ⊕
    MotherProjectionOrigin.Total root.source.projectionLaw ⊕
    (Σ index, MotherRestructuringOrigin.sortsOf
      root.source.restructuringSource.compiler.restructuringLaw.vocabulary.base index) ⊕
    MotherRestructuringOrigin.FamilyTotal
      (MotherRestructuringOrigin.familiesOf
        root.source.restructuringSource.compiler.restructuringLaw.vocabulary)

theorem original_root_addresses_one_stage
    {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) :
    ∃ rank : Ordinal.{0}, Nonempty (RootAddressTotal root ↪ Stage rank) :=
  every_carrier (RootAddressTotal root)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAddressCoverage
