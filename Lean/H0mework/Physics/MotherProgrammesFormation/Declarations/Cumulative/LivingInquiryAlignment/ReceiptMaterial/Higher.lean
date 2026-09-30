import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Source
import H0mework.Physics.MotherLaws.RestrictionConsumer

/-! The complete arena law is the input carrier for the same original finite
mother evaluator. Both levels retain their full observations before completion. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptHigher
open MotherStreamLaws MotherClosedRestrictions
open scoped Classical
noncomputable section
universe u v

abbrev Base (rank : Ordinal.{u}) := MotherReceiptSource.Formed rank
abbrev Address (rank : Ordinal.{u}) := MotherReceiptSource.Key rank × Nat

def observe (rank : Ordinal.{u}) (address : Address rank) (base : Base rank) : ℝ :=
  MotherReceiptSource.read rank base address.1 address.2

theorem observations_injective (rank : Ordinal.{u}) :
    Function.Injective (fun base : Base rank => fun address => observe rank address base) := by
  intro first last same
  apply (MotherReceiptSource.read_uniformEmbedding rank).injective
  funext key coordinate
  exact congrFun same (key, coordinate)

abbrev Programme (rank : Ordinal.{u}) := MotherReceiptObserved.Programme (Address rank)
def finiteLaw (rank : Ordinal.{u}) : Programme rank → Base rank → Stream :=
  MotherReceiptObserved.finiteLaw (observe rank)
abbrev Raw (rank : Ordinal.{u}) := MotherReceiptObserved.Raw (observe rank)
abbrev Material (rank : Ordinal.{u}) := MotherReceiptObserved.Formed (observe rank)

def read (rank : Ordinal.{u}) : Material rank → Base rank → Stream :=
  MotherReceiptObserved.read (observe rank)

theorem read_uniformEmbedding (rank : Ordinal.{u}) : IsUniformEmbedding (read rank) :=
  MotherReceiptObserved.read_uniformEmbedding (observe rank)

theorem read_surjective (rank : Ordinal.{u}) : Function.Surjective (read rank) :=
  MotherReceiptObserved.read_surjective (observe rank) (observations_injective rank)

def baseReadEquiv (rank : Ordinal.{u}) : Base rank ≃ (MotherReceiptSource.Key rank → Stream) :=
  Equiv.ofBijective (MotherReceiptSource.read rank)
    ⟨(MotherReceiptSource.read_uniformEmbedding rank).injective, MotherReceiptSource.read_surjective rank⟩

def readEquiv (rank : Ordinal.{u}) : Material rank ≃ (Base rank → Stream) :=
  Equiv.ofBijective (read rank) ⟨(read_uniformEmbedding rank).injective, read_surjective rank⟩

def point (rank : Ordinal.{u}) (key : MotherReceiptSource.Key rank) : Base rank :=
  (baseReadEquiv rank).symm (fun argument => fun _ => if argument = key then 1 else 0)

theorem point_read (rank : Ordinal.{u}) (key argument : MotherReceiptSource.Key rank) :
    MotherReceiptSource.read rank (point rank key) argument = fun _ => if argument = key then 1 else 0 :=
  congrFun ((baseReadEquiv rank).apply_symm_apply _) argument

theorem point_injective (rank : Ordinal.{u}) : Function.Injective (point rank) := by
  intro first last same
  by_contra different
  have sample := congrFun (congrFun (congrArg (MotherReceiptSource.read rank) same) first) 0
  simp only [point_read, if_neg different] at sample
  exact one_ne_zero sample

private theorem pair_first_last (stream : Stream) : pairStream (firstStream stream) (lastStream stream) = stream := by
  funext index
  have reassembled := Equiv.natSumNatEquivNat.apply_symm_apply index
  cases split : Equiv.natSumNatEquivNat.symm index with
  | inl coordinate =>
      rw [split] at reassembled
      simp only [pairStream, split, Sum.elim_inl, firstStream, reassembled]
  | inr coordinate =>
      rw [split] at reassembled
      simp only [pairStream, split, Sum.elim_inr, lastStream, reassembled]

private def lawPairEquiv {Law : Type u} {Input : Type v} (readLaw : Law ≃ (Input → Stream)) : Law × Law ≃ Law where
  toFun := fun values => readLaw.symm (fun input => pairStream (readLaw values.1 input) (readLaw values.2 input))
  invFun := fun value =>
    (readLaw.symm (fun input => firstStream (readLaw value input)),
      readLaw.symm (fun input => lastStream (readLaw value input)))
  left_inv := by
    intro values
    apply Prod.ext
    · apply readLaw.injective
      simp only [Equiv.apply_symm_apply, first_pair]
    · apply readLaw.injective
      simp only [Equiv.apply_symm_apply, last_pair]
  right_inv := by
    intro value
    apply readLaw.injective
    simp only [Equiv.apply_symm_apply, pair_first_last]

def pairEquiv (rank : Ordinal.{u}) : Base rank × Base rank ≃ Base rank := lawPairEquiv (baseReadEquiv rank)
def packEquiv (rank : Ordinal.{u}) : Material rank × Material rank ≃ Material rank := lawPairEquiv (readEquiv rank)

def pair (rank : Ordinal.{u}) : Base rank × Base rank → Base rank := pairEquiv rank
def unpair (rank : Ordinal.{u}) : Base rank → Base rank × Base rank := (pairEquiv rank).symm
def pack (rank : Ordinal.{u}) : Material rank × Material rank → Material rank := packEquiv rank
def split (rank : Ordinal.{u}) : Material rank → Material rank × Material rank := (packEquiv rank).symm

theorem unpair_pair (rank : Ordinal.{u}) (values : Base rank × Base rank) : unpair rank (pair rank values) = values :=
  (pairEquiv rank).symm_apply_apply values
theorem pair_unpair (rank : Ordinal.{u}) (value : Base rank) : pair rank (unpair rank value) = value :=
  (pairEquiv rank).apply_symm_apply value
theorem split_pack (rank : Ordinal.{u}) (values : Material rank × Material rank) : split rank (pack rank values) = values :=
  (packEquiv rank).symm_apply_apply values

def family (rank : Ordinal.{u}) (material : Material rank) (base : Base rank) : Material rank :=
  (readEquiv rank).symm (fun argument => read rank material (pair rank (base, argument)))

theorem family_read (rank : Ordinal.{u}) (material : Material rank) (base : Base rank) :
    read rank (family rank material base) = fun argument => read rank material (pair rank (base, argument)) :=
  (readEquiv rank).apply_symm_apply _

def familyEquiv (rank : Ordinal.{u}) : Material rank ≃ (Base rank → Material rank) where
  toFun := family rank
  invFun := fun values => (readEquiv rank).symm
    (fun argument => read rank (values (unpair rank argument).1) (unpair rank argument).2)
  left_inv := by
    intro material
    apply (read_uniformEmbedding rank).injective
    change readEquiv rank ((readEquiv rank).symm _) = _
    rw [Equiv.apply_symm_apply]
    funext argument
    rw [family_read]
    exact congrArg (read rank material) (pair_unpair rank argument)
  right_inv := by
    intro values
    funext base
    apply (read_uniformEmbedding rank).injective
    rw [family_read]
    change (fun argument => readEquiv rank ((readEquiv rank).symm _) (pair rank (base, argument))) = _
    rw [Equiv.apply_symm_apply]
    funext argument
    rw [unpair_pair]

theorem family_bijective (rank : Ordinal.{u}) : Function.Bijective (family rank) := (familyEquiv rank).bijective

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptHigher
