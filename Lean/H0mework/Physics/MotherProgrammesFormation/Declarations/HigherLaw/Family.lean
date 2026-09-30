import H0mework.Physics.MotherProgrammesFormation.Declarations.HigherLaw.Formation
import H0mework.Physics.MotherLaws.RestrictionConsumer

/-! The same completed higher law forms whole families of higher laws.
The factory pairs actual lower-law evaluations and curries its actual readout;
it does not accept a target family or enlarge the completed carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHigherLawFamily

open MotherStreamLaws MotherClosedRestrictions

noncomputable section

abbrev Base := MotherHigherLawFormation.Base
abbrev Formed := MotherHigherLawFormation.Formed

def pair (values : Base × Base) : Base :=
  (MotherPhysicalLaws.lawRead_surjective (fun input =>
    pairStream (MotherPhysicalLaws.lawRead values.1 input)
      (MotherPhysicalLaws.lawRead values.2 input))).choose

theorem pair_read (values : Base × Base) :
    MotherPhysicalLaws.lawRead (pair values) = fun input =>
      pairStream (MotherPhysicalLaws.lawRead values.1 input)
        (MotherPhysicalLaws.lawRead values.2 input) :=
  (MotherPhysicalLaws.lawRead_surjective _).choose_spec

theorem pair_injective : Function.Injective pair := by
  intro first last same
  have samples := congrArg MotherPhysicalLaws.lawRead same
  rw [pair_read, pair_read] at samples
  apply Prod.ext
  · apply MotherPhysicalLaws.lawRead_uniformEmbedding.injective
    funext input
    have sampled := congrArg firstStream (congrFun samples input)
    simpa only [first_pair] using sampled
  · apply MotherPhysicalLaws.lawRead_uniformEmbedding.injective
    funext input
    have sampled := congrArg lastStream (congrFun samples input)
    simpa only [last_pair] using sampled

def unpair (value : Base) : Base × Base :=
  ((MotherPhysicalLaws.lawRead_surjective
      (fun input => firstStream (MotherPhysicalLaws.lawRead value input))).choose,
    (MotherPhysicalLaws.lawRead_surjective
      (fun input => lastStream (MotherPhysicalLaws.lawRead value input))).choose)

theorem pair_unpair (value : Base) : pair (unpair value) = value := by
  apply MotherPhysicalLaws.lawRead_uniformEmbedding.injective
  rw [pair_read]
  have first := (MotherPhysicalLaws.lawRead_surjective
    (fun input => firstStream (MotherPhysicalLaws.lawRead value input))).choose_spec
  have last := (MotherPhysicalLaws.lawRead_surjective
    (fun input => lastStream (MotherPhysicalLaws.lawRead value input))).choose_spec
  change MotherPhysicalLaws.lawRead (unpair value).1 = _ at first
  change MotherPhysicalLaws.lawRead (unpair value).2 = _ at last
  rw [first, last]
  funext input index
  have reassembled := Equiv.natSumNatEquivNat.apply_symm_apply index
  cases split : Equiv.natSumNatEquivNat.symm index with
  | inl coordinate =>
    rw [split] at reassembled
    simp only [pairStream, split, Sum.elim_inl, firstStream, reassembled]
  | inr coordinate =>
    rw [split] at reassembled
    simp only [pairStream, split, Sum.elim_inr, lastStream, reassembled]

theorem unpair_pair (values : Base × Base) : unpair (pair values) = values :=
  pair_injective (pair_unpair (pair values))

/-- Currying uses the source-formed pair as its actual higher-law input. -/
def family (operation : Formed) (base : Base) : Formed :=
  (MotherHigherLawFormation.read_surjective
    (fun argument => MotherHigherLawFormation.read operation (pair (base, argument)))).choose

theorem family_read (operation : Formed) (base : Base) :
    MotherHigherLawFormation.read (family operation base) =
      fun argument => MotherHigherLawFormation.read operation (pair (base, argument)) :=
  (MotherHigherLawFormation.read_surjective _).choose_spec

/-- One existing higher material forms every whole higher-law-valued family. -/
theorem every_family (target : Base → Formed) :
    ∃ operation : Formed, family operation = target := by
  let values : Base × Base → Stream :=
    fun arguments => MotherHigherLawFormation.read (target arguments.1) arguments.2
  obtain ⟨operation, formed⟩ := MotherHigherLawFormation.read_surjective
    (Function.extend pair values (fun _ => 0))
  refine ⟨operation, ?_⟩
  funext base
  apply MotherHigherLawFormation.read_uniformEmbedding.injective
  funext argument
  rw [family_read, formed]
  exact pair_injective.extend_apply values (fun _ => 0) (base, argument)

/-- All higher material is retained by the whole generated family. -/
theorem family_injective : Function.Injective family := by
  intro first last same
  apply MotherHigherLawFormation.read_uniformEmbedding.injective
  funext input
  have observed := congrArg MotherHigherLawFormation.read (congrFun same (unpair input).1)
  rw [family_read, family_read] at observed
  have atInput := congrFun observed (unpair input).2
  simpa only [Prod.mk.eta, pair_unpair] using atInput

theorem family_bijective : Function.Bijective family :=
  ⟨family_injective, every_family⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHigherLawFamily
