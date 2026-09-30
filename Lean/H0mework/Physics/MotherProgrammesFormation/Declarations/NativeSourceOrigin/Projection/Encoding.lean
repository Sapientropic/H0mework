import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Signature

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin.Encoding
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeLedgerSource N V}
    (coordinates : Coordinates source.source) (old : SourceNativeProjectionLaw source) (encode : Encoding old)

def graph (tag : Nat) (code : B) : Prop :=
  let first := MotherHigherLawFamily.unpair code
  let second := MotherHigherLawFamily.unpair first.2
  let third := MotherHigherLawFamily.unpair second.2
  match tag with
  | 0 => ∃ p, encode.projection p = code
  | 1 => ∃ p point active, encode.projection p = first.1 ∧ coordinates.occurrence point = second.1 ∧
      encode.active ⟨p, point, active⟩ = second.2
  | 2 => ∃ p point inactive, encode.projection p = first.1 ∧ coordinates.occurrence point = second.1 ∧
      encode.inactive ⟨p, point, inactive⟩ = second.2
  | 3 => ∃ p point active payload, encode.projection p = first.1 ∧ coordinates.occurrence point = second.1 ∧
      encode.active ⟨p, point, active⟩ = third.1 ∧ encode.payload ⟨p, point, active, payload⟩ = third.2
  | 4 => ∃ p point active, encode.projection p = first.1 ∧ coordinates.occurrence point = second.1 ∧
      encode.active ⟨p, point, active⟩ = second.2 ∧ old.classify p point.2 = .inl active
  | 5 => ∃ p point inactive, encode.projection p = first.1 ∧ coordinates.occurrence point = second.1 ∧
      encode.inactive ⟨p, point, inactive⟩ = second.2 ∧ old.classify p point.2 = .inr inactive
  | 6 => ∃ p point active, encode.projection p = first.1 ∧ coordinates.occurrence point = second.1 ∧
      encode.active ⟨p, point, active⟩ = third.1 ∧ encode.payload ⟨p, point, active, old.project p point.2 active⟩ = third.2
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if graph coordinates old encode tag code then 0 else 1

theorem reader_bit {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates old encode)
    (tag : Nat) (code : B) : bit material tag code ↔ graph coordinates old encode tag code := by
  by_cases seen : graph coordinates old encode tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

def projectionEquiv {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates old encode) :
    old.Projection ≃ Projection material :=
  MotherNetworkOrigin.imageEquiv encode.projection (bit material 0) (by
    intro code
    exact reader_bit coordinates old encode hm 0 code)

def activeEquiv {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates old encode)
    (p : old.Projection) (point : Point source.source) :
    old.ActiveAt p point.2 ≃ Active coordinates material (projectionEquiv coordinates old encode hm p) point :=
  MotherNetworkOrigin.imageEquiv (activeAt old encode p point)
    (fun code => r3 material 1 (encode.projection p) (coordinates.occurrence point) code) (by
      intro code
      rw [r3, reader_bit coordinates old encode hm]
      simp only [graph, MotherHigherLawFamily.unpair_pair]
      constructor
      · rintro ⟨q, other, active, pEq, pointEq, codeEq⟩
        have same := encode.projection.injective pEq
        cases same
        have same := coordinates.occurrence.injective pointEq
        cases same
        exact ⟨active, codeEq⟩
      · rintro ⟨active, codeEq⟩
        exact ⟨p, point, active, rfl, rfl, codeEq⟩)

def inactiveEquiv {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates old encode)
    (p : old.Projection) (point : Point source.source) :
    old.InactiveAt p point.2 ≃ Inactive coordinates material (projectionEquiv coordinates old encode hm p) point :=
  MotherNetworkOrigin.imageEquiv (inactiveAt old encode p point)
    (fun code => r3 material 2 (encode.projection p) (coordinates.occurrence point) code) (by
      intro code
      rw [r3, reader_bit coordinates old encode hm]
      simp only [graph, MotherHigherLawFamily.unpair_pair]
      constructor
      · rintro ⟨q, other, inactive, pEq, pointEq, codeEq⟩
        have same := encode.projection.injective pEq
        cases same
        have same := coordinates.occurrence.injective pointEq
        cases same
        exact ⟨inactive, codeEq⟩
      · rintro ⟨inactive, codeEq⟩
        exact ⟨p, point, inactive, rfl, rfl, codeEq⟩)

def payloadEquiv {material : M} (hm : MotherHigherLawFormation.read material = reader coordinates old encode)
    (p : old.Projection) (point : Point source.source) (active : old.ActiveAt p point.2) :
    old.PayloadAt p point.2 active ≃ Payload coordinates material (projectionEquiv coordinates old encode hm p) point
      (activeEquiv coordinates old encode hm p point active) :=
  MotherNetworkOrigin.imageEquiv (payloadAt old encode p point active)
    (fun code => r4 material 3 (encode.projection p) (coordinates.occurrence point) (encode.active ⟨p, point, active⟩) code) (by
      intro code
      rw [r4, reader_bit coordinates old encode hm]
      simp only [graph, MotherHigherLawFamily.unpair_pair]
      constructor
      · rintro ⟨q, other, value, payload, pEq, pointEq, activeEq, codeEq⟩
        have same := encode.projection.injective pEq
        cases same
        have same := coordinates.occurrence.injective pointEq
        cases same
        have same := (activeAt old encode p point).injective activeEq
        cases same
        exact ⟨payload, codeEq⟩
      · rintro ⟨payload, codeEq⟩
        exact ⟨p, point, active, payload, rfl, rfl, rfl, codeEq⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProjectionOrigin.Encoding
