import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Lower A6 endpoint-coordinate core

This module contains the arithmetic A6 coordinate layer used by the
pre-realization crystal source:

* the six Dynkin coordinates and type-A adjacency/Cartan lowering;
* the signed-height readout and its unit-lowering law;
* the concrete endpoint/source label and coordinate readouts.

It deliberately stops before Boolean endpoint checks, generated shells,
coverage, normalizers, repair cells, or endpoint realization.  The historical
declarations retain their namespace, definition bodies, and unfoldability.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

/-! ## A6 coordinate arithmetic -/

/-- Abstract A6 Dynkin/weight label used by the SU(7) representation repair
interface. -/
abbrev SU7A6WeightLabel := Fin 6 -> Int

/-- Adjacency of simple roots in the A6 Dynkin chain. -/
def su7A6Adjacent (i j : Fin 6) : Prop :=
  i.1 + 1 = j.1 ∨ j.1 + 1 = i.1

/-- A6 Cartan-matrix entry in the simply-laced chain convention. -/
def su7A6CartanEntry (i j : Fin 6) : Int :=
  by
    classical
    exact if i = j then 2 else if su7A6Adjacent i j then -1 else 0

/-- Lower a Dynkin-coordinate weight by the simple root indexed by `i`. -/
def su7A6LowerBySimpleRoot
    (i : Fin 6) (source : SU7A6WeightLabel) : SU7A6WeightLabel :=
  fun j => source j - su7A6CartanEntry i j

/-- Concrete A6/SU(7) simple-root adjacency on Dynkin labels. -/
def SU7A6SimpleRootMove
    (source target : SU7A6WeightLabel) : Prop :=
  ∃ i : Fin 6, target = su7A6LowerBySimpleRoot i source

/-- The A6 height functional dual to the all-ones simple-root decrement. -/
def su7A6SignedHeight (label : SU7A6WeightLabel) : Int :=
  3 * label ⟨0, by decide⟩ +
    5 * label ⟨1, by decide⟩ +
      6 * label ⟨2, by decide⟩ +
        6 * label ⟨3, by decide⟩ +
          5 * label ⟨4, by decide⟩ +
            3 * label ⟨5, by decide⟩

/-- Numeric-coordinate readout of the signed-height functional. -/
theorem su7A6SignedHeight_num
    (label : SU7A6WeightLabel) :
    su7A6SignedHeight label =
      3 * label (0 : Fin 6) +
        5 * label (1 : Fin 6) +
          6 * label (2 : Fin 6) +
            6 * label (3 : Fin 6) +
              5 * label (4 : Fin 6) +
                3 * label (5 : Fin 6) := by
  rfl

/-- A6 Cartan arithmetic: every simple-root lowering spends exactly one unit
of the signed height functional. -/
theorem su7A6SignedHeight_lowerBySimpleRoot
    (source : SU7A6WeightLabel) (i : Fin 6) :
    su7A6SignedHeight (su7A6LowerBySimpleRoot i source) + 1 =
      su7A6SignedHeight source := by
  fin_cases i <;>
    simp [su7A6SignedHeight, su7A6LowerBySimpleRoot,
      su7A6CartanEntry, su7A6Adjacent] <;>
    omega

/-- Simple-root moves are unit descents for the A6 signed height. -/
theorem su7A6SignedHeight_unit_decrement_of_simpleRootMove
    {source target : SU7A6WeightLabel}
    (hmove : SU7A6SimpleRootMove source target) :
    su7A6SignedHeight target + 1 =
      su7A6SignedHeight source := by
  rcases hmove with ⟨i, rfl⟩
  exact su7A6SignedHeight_lowerBySimpleRoot source i

/-- Natural residual-code readout of the A6 signed-height functional. -/
def su7A6SignedHeightNat (label : SU7A6WeightLabel) : Nat :=
  (su7A6SignedHeight label).toNat

/-- A simple-root move is a unit decrement for the natural signed-height
readout whenever the lowered target remains nonnegative. -/
theorem su7A6SignedHeightNat_unit_decrement_of_simpleRootMove
    {source target : SU7A6WeightLabel}
    (hmove : SU7A6SimpleRootMove source target)
    (htarget_nonneg : 0 ≤ su7A6SignedHeight target) :
    su7A6SignedHeightNat target + 1 =
      su7A6SignedHeightNat source := by
  have hunit :
      su7A6SignedHeight target + 1 =
        su7A6SignedHeight source :=
    su7A6SignedHeight_unit_decrement_of_simpleRootMove hmove
  have hsource_nonneg : 0 ≤ su7A6SignedHeight source := by
    omega
  unfold su7A6SignedHeightNat
  have htarget_cast :
      (((su7A6SignedHeight target).toNat : Nat) : Int) =
        su7A6SignedHeight target :=
    Int.toNat_of_nonneg htarget_nonneg
  have hsource_cast :
      (((su7A6SignedHeight source).toNat : Nat) : Int) =
        su7A6SignedHeight source :=
    Int.toNat_of_nonneg hsource_nonneg
  have hcast :
      (((su7A6SignedHeight target).toNat + 1 : Nat) : Int) =
        ((su7A6SignedHeight source).toNat : Nat) := by
    rw [Int.natCast_add, htarget_cast, hsource_cast]
    exact hunit
  exact Int.ofNat_injective hcast

/-! ## Concrete endpoint/source coordinates -/

/-- Integer correction term used by the concrete endpoint/source A6 encoding. -/
def su7A6EndpointSourceEnergyCorrection
    (left right energy : Nat) : Int :=
  (energy : Int) - 3 * (left : Int) - 5 * (right : Int)

/-- Concrete A6 label carrying endpoint source codes and residual energy. -/
def su7A6EndpointSourceLabel
    (left right energy : Nat) : SU7A6WeightLabel :=
  fun i =>
    if i = ⟨0, by decide⟩ then
      (left : Int)
    else if i = ⟨1, by decide⟩ then
      (right : Int)
    else if i = ⟨2, by decide⟩ then
      su7A6EndpointSourceEnergyCorrection left right energy
    else if i = ⟨4, by decide⟩ then
      -su7A6EndpointSourceEnergyCorrection left right energy
    else
      0

/-- Left endpoint code readout for the concrete endpoint/source A6 encoding. -/
def su7A6EndpointSourceLeftCodeOf
    (label : SU7A6WeightLabel) : Nat :=
  Int.natAbs (label ⟨0, by decide⟩)

/-- Right endpoint code readout for the concrete endpoint/source A6 encoding. -/
def su7A6EndpointSourceRightCodeOf
    (label : SU7A6WeightLabel) : Nat :=
  Int.natAbs (label ⟨1, by decide⟩)

theorem su7A6EndpointSourceLabel_leftCode
    (left right energy : Nat) :
    su7A6EndpointSourceLeftCodeOf
      (su7A6EndpointSourceLabel left right energy) = left := by
  simp [su7A6EndpointSourceLeftCodeOf, su7A6EndpointSourceLabel]

theorem su7A6EndpointSourceLabel_rightCode
    (left right energy : Nat) :
    su7A6EndpointSourceRightCodeOf
      (su7A6EndpointSourceLabel left right energy) = right := by
  simp [su7A6EndpointSourceRightCodeOf, su7A6EndpointSourceLabel]

@[simp] theorem su7A6EndpointSourceLabel_zero_num
    (left right energy : Nat) :
    su7A6EndpointSourceLabel left right energy (0 : Fin 6) =
      (left : Int) := by
  simp [su7A6EndpointSourceLabel]

@[simp] theorem su7A6EndpointSourceLabel_one_num
    (left right energy : Nat) :
    su7A6EndpointSourceLabel left right energy (1 : Fin 6) =
      (right : Int) := by
  simp [su7A6EndpointSourceLabel]

@[simp] theorem su7A6EndpointSourceLabel_two_num
    (left right energy : Nat) :
    su7A6EndpointSourceLabel left right energy (2 : Fin 6) =
      su7A6EndpointSourceEnergyCorrection left right energy := by
  simp [su7A6EndpointSourceLabel]

@[simp] theorem su7A6EndpointSourceLabel_three_num
    (left right energy : Nat) :
    su7A6EndpointSourceLabel left right energy (3 : Fin 6) = 0 := by
  simp [su7A6EndpointSourceLabel]

@[simp] theorem su7A6EndpointSourceLabel_four_num
    (left right energy : Nat) :
    su7A6EndpointSourceLabel left right energy (4 : Fin 6) =
      -su7A6EndpointSourceEnergyCorrection left right energy := by
  simp [su7A6EndpointSourceLabel]

@[simp] theorem su7A6EndpointSourceLabel_five_num
    (left right energy : Nat) :
    su7A6EndpointSourceLabel left right energy (5 : Fin 6) = 0 := by
  simp [su7A6EndpointSourceLabel]

theorem su7A6EndpointSourceLabel_signedHeight
    (left right energy : Nat) :
    su7A6SignedHeight
      (su7A6EndpointSourceLabel left right energy) =
        (energy : Int) := by
  simp [su7A6SignedHeight, su7A6EndpointSourceLabel,
    su7A6EndpointSourceEnergyCorrection]
  ring

/-- Concrete `(5,7,E=8)` source label used by the lower crystal trace. -/
def su7A6FiveSevenSourceLabel : SU7A6WeightLabel :=
  su7A6EndpointSourceLabel 5 7 8

end

end StandardModelConstraint
end SaturationMonoid
