import H0mework.Physics.MotherDeclarationsPhysical.LawsObservation
import H0mework.Physics.MotherLaws.PointwiseApproximation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws

open MotherFamilyOccurrence StageEightDiscreteFormation RationalSourceFormation Stage9C.Revision
open MotherStreamLaws CurrentMaterial StageNineCanonicalCauchyState

noncomputable section

local instance instEncodableChannel_scratch : Encodable Channel := MotherRawCurrent.channelCodec
abbrev Kind := Channel ⊕ ℕ

def kindRead (code : ℕ) : Kind := (Encodable.decode code).getD (.inr 0)

def count (visit : MotherVisit) : ℕ := (codeOf visit).unpair.1

def readPoint (points : MotherStreamFormation.Carrier) (index : ℕ) : StageNineSpatialPoint :=
  WithLp.toLp 2 (fun axis => MotherStreamFormation.read points (Nat.pair index axis.val))

def observationAt (visit : MotherVisit) (points : MotherStreamFormation.Carrier)
    (index : Fin (count visit)) : Observation :=
  match kindRead (unpack (count visit) (codeOf visit).unpair.2 index) with
  | .inl channel => .inl (channel, readPoint points index.val)
  | .inr slot => .inr slot

def features (visit : MotherVisit) (points : MotherStreamFormation.Carrier) (input : Input) : Stream :=
  pad (count visit) (fun index => observeInput (observationAt visit points index) input)

/-- Both visits and the complete point material belong to the existing mother. -/
abbrev Programme := (MotherVisit × MotherStreamFormation.Carrier) × MotherVisit

def finiteLaw (programme : Programme) : Input → Stream :=
  fun input => MotherPointwiseLaws.finiteLaw programme.2
    (features programme.1.1 programme.1.2 input)

theorem every_features (n : ℕ) (observations : Fin n → Observation) :
    ∃ visit : MotherVisit, ∃ points : MotherStreamFormation.Carrier,
      features visit points = fun input => pad n (fun index => observeInput (observations index) input) := by
  let kind : Fin n → Kind := fun index => match observations index with
    | .inl (channel, _) => .inl channel
    | .inr slot => .inr slot
  let code := Nat.pair n (pack (fun index => Encodable.encode (kind index)))
  let visit := SpinPair.visit (10 + code)
  let coordinates : Stream := fun address =>
    if bound : address.unpair.1 < n then match observations ⟨address.unpair.1, bound⟩ with
      | .inl (_, point) => if axis : address.unpair.2 < 3 then point ⟨address.unpair.2, axis⟩ else 0
      | .inr _ => 0
    else 0
  obtain ⟨points, formed⟩ := MotherStreamFormation.read_surjective coordinates
  have sourceCode : codeOf visit = code := code_at code
  refine ⟨visit, points, ?_⟩
  funext input
  simp only [features, observationAt, count]
  rw [sourceCode]
  dsimp only [code]
  rw [Nat.unpair_pair]
  simp only [unpack_pack, kindRead, Encodable.encodek, Option.getD_some]
  apply congrArg (pad n)
  funext index
  cases observation : observations index with
  | inl pair =>
    rcases pair with ⟨channel, point⟩
    simp only [kind, observation]
    congr 2
    apply congrArg (fun p : StageNineSpatialPoint => (channel, p))
    apply PiLp.ext
    intro axis
    simp only [readPoint, formed, coordinates, Nat.unpair_pair,
      dif_pos index.isLt, observation, dif_pos axis.isLt]
  | inr slot => simp only [kind, observation]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws
