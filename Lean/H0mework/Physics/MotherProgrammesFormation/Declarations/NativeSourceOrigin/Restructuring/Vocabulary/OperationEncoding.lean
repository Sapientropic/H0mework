import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Operations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin.OperationEncoding
open MotherNetworkFactory
open scoped Classical
noncomputable section

variable (base families : M) (old : Operations (formedSorts base) (formedFamilies base families))

def graph (tag : Nat) (code : B) : Prop :=
  let first := MotherHigherLawFamily.unpair code
  let second := MotherHigherLawFamily.unpair first.2
  let third := MotherHigherLawFamily.unpair second.2
  match tag with
  | 0 => old.null.val = code
  | 1 => ∃ value, value.val = first.1 ∧ (old.complement value).val = first.2
  | 2 => ∃ source, source.val = first.1 ∧ (old.anchorIdentity source).val = second.1 ∧
      (old.anchorScope source).val = third.1 ∧ (old.anchorLineage source).val = third.2
  | 3 => ∃ source, source.val = first.1 ∧ (old.incidence source).val = first.2
  | 4 => ∃ (source : Field base 0) (obstruction : Obstruction base families source), source.val = first.1 ∧
      obstruction.val = second.1 ∧ (old.demandContent obstruction).val = second.2
  | 5 => ∃ (source : Field base 0) (obstruction : Obstruction base families source), source.val = first.1 ∧
      obstruction.val = second.1 ∧ (old.demandResidual obstruction).val = second.2
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if graph base families old tag code then 0 else 1

theorem reader_bit {material : M} (hm : MotherHigherLawFormation.read material = reader base families old)
    (tag : Nat) (code : B) : bit material tag code ↔ graph base families old tag code := by
  by_cases seen : graph base families old tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

variable {material : M} (hm : MotherHigherLawFormation.read material = reader base families old)

include hm

theorem null_graph (value : Field base 8) : bit material 0 value.val ↔ value = old.null := by
  rw [reader_bit base families old hm]
  exact ⟨fun same => Subtype.ext same.symm, fun same => congrArg Subtype.val same.symm⟩

theorem complement_graph (value result : Field base 8) : r2 material 1 value.val result.val ↔ result = old.complement value := by
  rw [r2, reader_bit base families old hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, valueEq, resultEq⟩
    have same : other = value := Subtype.ext valueEq
    cases same
    exact Subtype.ext resultEq.symm
  · intro same
    cases same
    exact ⟨value, rfl, rfl⟩

theorem anchor_graph (source : Field base 0) (body : AnchorBody base) :
    r4 material 2 source.val body.1.val body.2.1.val body.2.2.val ↔
      body = (old.anchorIdentity source, old.anchorScope source, old.anchorLineage source) := by
  rw [r4, reader_bit base families old hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, sourceEq, identityEq, scopeEq, lineageEq⟩
    have same : other = source := Subtype.ext sourceEq
    cases same
    exact Prod.ext (Subtype.ext identityEq.symm) (Prod.ext (Subtype.ext scopeEq.symm) (Subtype.ext lineageEq.symm))
  · intro same
    cases same
    exact ⟨source, rfl, rfl, rfl, rfl⟩

theorem incidence_graph (source : Field base 0) (result : Field base 7) :
    r2 material 3 source.val result.val ↔ result = old.incidence source := by
  rw [r2, reader_bit base families old hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, sourceEq, resultEq⟩
    have same : other = source := Subtype.ext sourceEq
    cases same
    exact Subtype.ext resultEq.symm
  · intro same
    cases same
    exact ⟨source, rfl, rfl⟩

theorem content_graph (source : Field base 0) (obstruction : Obstruction base families source) (result : Field base 1) :
    r3 material 4 source.val obstruction.val result.val ↔ result = old.demandContent obstruction := by
  rw [r3, reader_bit base families old hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, value, sourceEq, valueEq, resultEq⟩
    have same : other = source := Subtype.ext sourceEq
    cases same
    have same : value = obstruction := Subtype.ext valueEq
    cases same
    exact Subtype.ext resultEq.symm
  · intro same
    cases same
    exact ⟨source, obstruction, rfl, rfl, rfl⟩

theorem residual_graph (source : Field base 0) (obstruction : Obstruction base families source) (result : Field base 2) :
    r3 material 5 source.val obstruction.val result.val ↔ result = old.demandResidual obstruction := by
  rw [r3, reader_bit base families old hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, value, sourceEq, valueEq, resultEq⟩
    have same : other = source := Subtype.ext sourceEq
    cases same
    have same : value = obstruction := Subtype.ext valueEq
    cases same
    exact Subtype.ext resultEq.symm
  · intro same
    cases same
    exact ⟨source, obstruction, rfl, rfl, rfl⟩

include hm in
theorem checked : DataCheck base families material where
  null := ⟨old.null, (null_graph base families old hm _).mpr rfl,
    fun value selected => (null_graph base families old hm value).mp selected⟩
  complement := fun value => ⟨old.complement value, (complement_graph base families old hm value _).mpr rfl,
    fun result selected => (complement_graph base families old hm value result).mp selected⟩
  anchor := fun source => ⟨(old.anchorIdentity source, old.anchorScope source, old.anchorLineage source),
    (anchor_graph base families old hm source _).mpr rfl,
    fun result selected => (anchor_graph base families old hm source result).mp selected⟩
  incidence := fun source => ⟨old.incidence source, (incidence_graph base families old hm source _).mpr rfl,
    fun result selected => (incidence_graph base families old hm source result).mp selected⟩
  demandContent := fun source obstruction => ⟨old.demandContent obstruction, (content_graph base families old hm source obstruction _).mpr rfl,
    fun result selected => (content_graph base families old hm source obstruction result).mp selected⟩
  demandResidual := fun source obstruction => ⟨old.demandResidual obstruction, (residual_graph base families old hm source obstruction _).mpr rfl,
    fun result selected => (residual_graph base families old hm source obstruction result).mp selected⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin.OperationEncoding
