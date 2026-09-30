import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Fields

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin.FieldEncoding
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {R : RestructuringVocabulary.{0}}
    (coordinates : Coordinates source) (world : WorldCoordinates N) (vocabulary : VocabularyCoordinates R)
    (fields : Fields source R)

def graph (tag : Nat) (code : B) : Prop :=
  ∃ (index : Fin 6) (input : Domain source R index), index.val = tag ∧
    domainAddress source R coordinates world vocabulary index input = (MotherHigherLawFamily.unpair code).1 ∧
    codomainAddress R world vocabulary index (fields index input) = (MotherHigherLawFamily.unpair code).2

def reader (code : B) (tag : Nat) : ℝ := if graph coordinates world vocabulary fields tag code then 0 else 1

variable {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates world vocabulary fields)
include hm

theorem at_graph (index : Fin 6) (input : Domain source R index) (output : Codomain (N := N) R index) :
    r2 material index.val (domainAddress source R coordinates world vocabulary index input)
      (codomainAddress R world vocabulary index output) ↔ output = fields index input := by
  have readBit (code : B) (tag : Nat) : bit material tag code ↔ graph coordinates world vocabulary fields tag code := by
    by_cases seen : graph coordinates world vocabulary fields tag code <;>
      simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]
  rw [r2, readBit]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, value, tagEq, inputEq, outputEq⟩
    have same : other = index := Fin.ext tagEq
    cases same
    have same : value = input := (domainAddress source R coordinates world vocabulary index).injective inputEq
    cases same
    exact (codomainAddress R world vocabulary index).injective outputEq.symm
  · intro same
    cases same
    exact ⟨index, input, rfl, rfl, rfl⟩

theorem checked : FieldCheck coordinates world vocabulary material := fun index input =>
  ⟨fields index input, (at_graph coordinates world vocabulary fields hm index input _).mpr rfl,
    fun output selected => (at_graph coordinates world vocabulary fields hm index input output).mp selected⟩

theorem recovered (check : FieldCheck coordinates world vocabulary material) :
    generatedFields coordinates world vocabulary material check = fields := by
  funext index input
  exact (at_graph coordinates world vocabulary fields hm index input _).mp (Classical.choose_spec (check index input)).1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin.FieldEncoding
