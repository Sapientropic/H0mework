import H0mework.Physics.MotherProgrammesFormation.Declarations.HigherLaw.Formation
import H0mework.Physics.MotherLaws.RestrictionConsumer

/-! Source operations for reading old laws and finite typed data from one
higher material. Target values occur only in coverage proofs. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHigherLawValue

open MotherStreamLaws MotherClosedRestrictions
open scoped Classical

noncomputable section

abbrev Base := MotherHigherLawFormation.Base
abbrev Formed := MotherHigherLawFormation.Formed
abbrev Input := MotherPhysicalLaws.Input

/-- An old input is distinguished by its actual singleton evaluation law. -/
def point (input : Input) : Base := by
  classical
  exact (MotherPhysicalLaws.lawRead_surjective
    (fun argument => fun _ => if argument = input then 1 else 0)).choose

theorem point_read (input argument : Input) :
    MotherPhysicalLaws.lawRead (point input) argument =
      fun _ => if argument = input then 1 else 0 := by
  classical
  exact congrFun (MotherPhysicalLaws.lawRead_surjective _).choose_spec argument

theorem point_injective : Function.Injective point := by
  classical
  intro first last same
  by_contra different
  have sampled := congrFun (congrFun (congrArg MotherPhysicalLaws.lawRead same) first) 0
  simp only [point_read, if_neg different] at sampled
  norm_num at sampled

def readBase (material : Formed) : Base :=
  (MotherPhysicalLaws.lawRead_surjective
    (fun input => MotherHigherLawFormation.read material (point input))).choose

theorem readBase_read (material : Formed) :
    MotherPhysicalLaws.lawRead (readBase material) =
      fun input => MotherHigherLawFormation.read material (point input) :=
  (MotherPhysicalLaws.lawRead_surjective _).choose_spec

theorem readBase_surjective : Function.Surjective readBase := by
  intro value
  obtain ⟨material, formed⟩ := MotherHigherLawFormation.read_surjective
    (Function.extend point (MotherPhysicalLaws.lawRead value) (fun _ => 0))
  refine ⟨material, ?_⟩
  apply MotherPhysicalLaws.lawRead_uniformEmbedding.injective
  funext input
  rw [readBase_read, formed]
  exact point_injective.extend_apply _ _ input

def pack (values : Formed × Formed) : Formed :=
  (MotherHigherLawFormation.read_surjective (fun base =>
    pairStream (MotherHigherLawFormation.read values.1 base)
      (MotherHigherLawFormation.read values.2 base))).choose

theorem pack_read (values : Formed × Formed) :
    MotherHigherLawFormation.read (pack values) = fun base =>
      pairStream (MotherHigherLawFormation.read values.1 base)
        (MotherHigherLawFormation.read values.2 base) :=
  (MotherHigherLawFormation.read_surjective _).choose_spec

def split (value : Formed) : Formed × Formed :=
  ((MotherHigherLawFormation.read_surjective
      (fun base => firstStream (MotherHigherLawFormation.read value base))).choose,
    (MotherHigherLawFormation.read_surjective
      (fun base => lastStream (MotherHigherLawFormation.read value base))).choose)

theorem split_read (value : Formed) :
    MotherHigherLawFormation.read (split value).1 =
        (fun base => firstStream (MotherHigherLawFormation.read value base)) ∧
      MotherHigherLawFormation.read (split value).2 =
        (fun base => lastStream (MotherHigherLawFormation.read value base)) :=
  ⟨(MotherHigherLawFormation.read_surjective _).choose_spec,
    (MotherHigherLawFormation.read_surjective _).choose_spec⟩

theorem split_pack (values : Formed × Formed) : split (pack values) = values := by
  apply Prod.ext
  · apply MotherHigherLawFormation.read_uniformEmbedding.injective
    rw [(split_read _).1, pack_read]
    exact funext fun _ => first_pair _ _
  · apply MotherHigherLawFormation.read_uniformEmbedding.injective
    rw [(split_read _).2, pack_read]
    exact funext fun _ => last_pair _ _

def scalar (value : ℝ) : Formed :=
  (MotherHigherLawFormation.read_surjective (fun _ => fun _ => value)).choose

theorem scalar_read (value : ℝ) (base : Base) (coordinate : ℕ) :
    MotherHigherLawFormation.read (scalar value) base coordinate = value :=
  congrFun (congrFun (MotherHigherLawFormation.read_surjective _).choose_spec base) coordinate

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHigherLawValue
