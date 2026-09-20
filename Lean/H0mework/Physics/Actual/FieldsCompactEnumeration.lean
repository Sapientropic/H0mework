import H0mework.Physics.Actual.FieldsCompactFaithful

/-! One countable coordinate inventory for every scale and all nine fields. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fields

open ProofFreeRicherAnholonomicSource StageNineHolonomicField

noncomputable section

local instance coordinateEncodable : Encodable Coordinate := Fintype.toEncodable _

def readIndex (code : ℕ) : ℕ × Coordinate :=
  ((Nat.unpair code).1,
    (Encodable.decode (Nat.unpair code).2).getD (.coframe 0 0))

def readCode (scale : ℕ) (coordinate : Coordinate) : ℕ :=
  Nat.pair scale (Encodable.encode coordinate)

@[simp] theorem readIndex_readCode (scale : ℕ) (coordinate : Coordinate) :
    readIndex (readCode scale coordinate) = (scale, coordinate) := by
  simp only [readIndex, readCode, Nat.unpair_pair, Encodable.encodek, Option.getD_some]

def compactCoordinates (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (code : ℕ) : CompactL2 :=
  compactRead configuration smooth (readIndex code).1 (readIndex code).2

@[simp] theorem compactCoordinates_readCode (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth) (scale : ℕ) (coordinate : Coordinate) :
    compactCoordinates configuration smooth (readCode scale coordinate) =
      compactRead configuration smooth scale coordinate := by
  simp only [compactCoordinates, readIndex_readCode]

theorem configuration_eq_of_compactCoordinates_eq
    {left right : StageNineHolonomicConfiguration}
    (leftSmooth : left.Smooth) (rightSmooth : right.Smooth)
    (same : compactCoordinates left leftSmooth = compactCoordinates right rightSmooth) :
    left = right := by
  apply configuration_eq_of_compactRead_eq leftSmooth rightSmooth
  intro scale coordinate
  simpa only [compactCoordinates_readCode] using congrFun same (readCode scale coordinate)

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fields
