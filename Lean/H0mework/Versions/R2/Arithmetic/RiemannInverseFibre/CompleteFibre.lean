import H0mework.Versions.R2.Arithmetic.RiemannInverseFibre.DeterminantLineIncidence

/-!
# Complete determinant-line inverse fibre

For a fixed generated zero observation the lawful conditional fibre is
exactly two installed charts times one unrestricted complex partner.  Before
assuming a zero, the coordinate fibre also retains the zero witness itself.
Both forward and reverse maps are explicit and choice-free.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLine
open CanonicalUnitArithmeticFactorizationWholePrimeDualBlockGlobalComplexDeterminantLineDerivedSpecialization

noncomputable section

namespace InverseZeroFibre

def pointWithLeftZero (observation : GeneratedRiemannZeroObservation)
    (partner : ℂ) : DeterminantLinePoint where
  pair := (observation.coordinate, partner)
  sectionZero := by
    change riemannZeta observation.coordinate * riemannZeta partner = 0
    rw [observation.mathlibZero, zero_mul]

def pointWithRightZero (observation : GeneratedRiemannZeroObservation)
    (partner : ℂ) : DeterminantLinePoint where
  pair := (partner, observation.coordinate)
  sectionZero := by
    change riemannZeta partner * riemannZeta observation.coordinate = 0
    rw [observation.mathlibZero, mul_zero]

def leftPreimage (observation : GeneratedRiemannZeroObservation)
    (partner : ℂ) : InverseZeroFibre observation :=
  ⟨.left (pointWithLeftZero observation partner) observation.zero,
    GeneratedRiemannZeroObservation.ext _ _ rfl⟩

def rightPreimage (observation : GeneratedRiemannZeroObservation)
    (partner : ℂ) : InverseZeroFibre observation :=
  ⟨.right (pointWithRightZero observation partner) observation.zero,
    GeneratedRiemannZeroObservation.ext _ _ rfl⟩

def encode (observation : GeneratedRiemannZeroObservation) :
    Sum ℂ ℂ → InverseZeroFibre observation
  | .inl partner => leftPreimage observation partner
  | .inr partner => rightPreimage observation partner

def decode {observation : GeneratedRiemannZeroObservation} :
    InverseZeroFibre observation → Sum ℂ ℂ
  | ⟨.left point _, _⟩ => .inl point.pair.2
  | ⟨.right point _, _⟩ => .inr point.pair.1

def forgetChart : Sum ℂ ℂ → ℂ
  | .inl partner => partner
  | .inr partner => partner

def flipChart : Sum ℂ ℂ → Sum ℂ ℂ
  | .inl partner => .inr partner
  | .inr partner => .inl partner

@[simp] theorem decode_encode
    (observation : GeneratedRiemannZeroObservation) (residual : Sum ℂ ℂ) :
    decode (encode observation residual) = residual := by
  cases residual <;> rfl

@[simp] theorem encode_decode
    (observation : GeneratedRiemannZeroObservation)
    (fibre : InverseZeroFibre observation) :
    encode observation (decode fibre) = fibre := by
  rcases fibre with ⟨incidence, readback⟩
  cases incidence with
  | left point zero =>
      cases readback
      cases point with
      | mk pair sectionZero =>
          cases pair
          rfl
  | right point zero =>
      cases readback
      cases point with
      | mk pair sectionZero =>
          cases pair
          rfl

def completeEquiv (observation : GeneratedRiemannZeroObservation) :
    InverseZeroFibre observation ≃ Sum ℂ ℂ where
  toFun := decode
  invFun := encode observation
  left_inv := encode_decode observation
  right_inv := decode_encode observation

/-- Complete conditional fibre before a zero witness is known. -/
abbrev CoordinateInverseZeroFibre (coordinate : ℂ) :=
  {incidence : LawfulPointZeroIncidence //
    incidence.observation.coordinate = coordinate}

def coordinateDecode {coordinate : ℂ} :
    CoordinateInverseZeroFibre coordinate →
      PLift (generatedRiemannZeta ActualAnalyticOwner coordinate = 0) ×
        Sum ℂ ℂ
  | ⟨.left point zero, coordinate_eq⟩ =>
      ⟨⟨by rw [← coordinate_eq]; exact zero⟩, .inl point.pair.2⟩
  | ⟨.right point zero, coordinate_eq⟩ =>
      ⟨⟨by rw [← coordinate_eq]; exact zero⟩, .inr point.pair.1⟩

def coordinateEncode (coordinate : ℂ) :
    PLift (generatedRiemannZeta ActualAnalyticOwner coordinate = 0) ×
        Sum ℂ ℂ →
      CoordinateInverseZeroFibre coordinate :=
  fun source =>
    let observation := GeneratedRiemannZeroObservation.observe
      coordinate source.1.down
    let fibre := encode observation source.2
    ⟨fibre.1, congrArg GeneratedRiemannZeroObservationAt.coordinate fibre.2⟩

@[simp] theorem coordinateDecode_encode (coordinate : ℂ)
    (source :
      PLift (generatedRiemannZeta ActualAnalyticOwner coordinate = 0) ×
        Sum ℂ ℂ) :
    coordinateDecode (coordinateEncode coordinate source) = source := by
  rcases source with ⟨zero, residual⟩
  cases residual <;> rfl

@[simp] theorem coordinateEncode_decode (coordinate : ℂ)
    (fibre : CoordinateInverseZeroFibre coordinate) :
    coordinateEncode coordinate (coordinateDecode fibre) = fibre := by
  rcases fibre with ⟨incidence, coordinate_eq⟩
  cases incidence with
  | left point zero =>
      cases coordinate_eq
      cases point with
      | mk pair sectionZero =>
          cases pair
          rfl
  | right point zero =>
      cases coordinate_eq
      cases point with
      | mk pair sectionZero =>
          cases pair
          rfl

def coordinateCompleteEquiv (coordinate : ℂ) :
    CoordinateInverseZeroFibre coordinate ≃
      PLift (generatedRiemannZeta ActualAnalyticOwner coordinate = 0) ×
        Sum ℂ ℂ where
  toFun := coordinateDecode
  invFun := coordinateEncode coordinate
  left_inv := coordinateEncode_decode coordinate
  right_inv := coordinateDecode_encode coordinate

theorem coordinateFibre_nonempty_iff (coordinate : ℂ) :
    Nonempty (CoordinateInverseZeroFibre coordinate) ↔
      generatedRiemannZeta ActualAnalyticOwner coordinate = 0 := by
  constructor
  · rintro ⟨fibre⟩
    exact (coordinateCompleteEquiv coordinate fibre).1.down
  · intro zero
    exact ⟨(coordinateCompleteEquiv coordinate).symm
      ⟨⟨zero⟩, Sum.inl 0⟩⟩

theorem coordinateFibre_isEmpty_iff (coordinate : ℂ) :
    IsEmpty (CoordinateInverseZeroFibre coordinate) ↔
      generatedRiemannZeta ActualAnalyticOwner coordinate ≠ 0 := by
  constructor
  · intro empty zero
    exact empty.false <|
      (coordinateCompleteEquiv coordinate).symm ⟨⟨zero⟩, Sum.inl 0⟩
  · intro nonzero
    exact ⟨fun fibre =>
      nonzero (coordinateCompleteEquiv coordinate fibre).1.down⟩

end InverseZeroFibre

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
