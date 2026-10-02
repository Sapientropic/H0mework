import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Tower
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Observed

/-! Actual finite mother programmes on the complete keys of a rank arena.

The key carrier comes from the existing tower candidate and retains its
original tagged keys, including distinct keys with equal stageValue.
Each finite law feeds actual singleton observations to the original
MotherPointwiseLaws.finiteLaw. The completed reader extends exactly that
raw range. Rank is a construction index, not a physical visit; this module
does not install the tower or its reader into the original runtime.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptSource

open Set Filter UniformSpace MotherStreamLaws MotherFamilyOccurrence Stage9C.Revision
open scoped Topology Uniformity UniformConvergence Classical
noncomputable section
universe u

abbrev Key (rank : Ordinal.{u}) : Type u := ULift.{u, 0} Unit ⊕ MotherReceiptArena.Stage rank
abbrev Address (rank : Ordinal.{u}) := Key rank

def observe (rank : Ordinal.{u}) (address input : Key rank) : ℝ :=
  if input = address then 1 else 0

theorem observations_injective (rank : Ordinal.{u}) :
    Function.Injective (fun input : Key rank => fun address => observe rank address input) := by
  intro first last same
  by_contra different
  have sampled := congrFun same first
  have firstRead : observe rank first first = 1 := if_pos rfl
  have lastRead : observe rank first last = 0 := if_neg (fun equal => different equal.symm)
  exact one_ne_zero (firstRead.symm.trans (sampled.trans lastRead))



abbrev Programme (rank : Ordinal.{u}) := MotherReceiptObserved.Programme (Address rank)

def finiteLaw (rank : Ordinal.{u}) : Programme rank → Key rank → Stream :=
  MotherReceiptObserved.finiteLaw (observe rank)

theorem finiteLaw_dense (rank : Ordinal.{u}) : DenseRange (finiteLaw rank) :=
  MotherReceiptObserved.finiteLaw_dense (observe rank) (observations_injective rank)

abbrev Raw (rank : Ordinal.{u}) := MotherReceiptObserved.Raw (observe rank)
abbrev Formed (rank : Ordinal.{u}) := MotherReceiptObserved.Formed (observe rank)

def read (rank : Ordinal.{u}) : Formed rank → Key rank → Stream :=
  MotherReceiptObserved.read (observe rank)

theorem read_coe (rank : Ordinal.{u}) (raw : Raw rank) :
    read rank (raw : Formed rank) = raw.val :=
  MotherReceiptObserved.read_coe (observe rank) raw

theorem read_uniformEmbedding (rank : Ordinal.{u}) : IsUniformEmbedding (read rank) :=
  MotherReceiptObserved.read_uniformEmbedding (observe rank)

/-- The original finite mother evaluator covers the whole fixed arena law space. -/
theorem read_surjective (rank : Ordinal.{u}) : Function.Surjective (read rank) :=
  MotherReceiptObserved.read_surjective (observe rank) (observations_injective rank)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptSource
