import Mathlib.LinearAlgebra.FreeModule.PID
import H0mework.Versions.R2.Arithmetic.EulerLocal.DependentDiagram

/-!
# Common anti-invariant whole-history factorization carrier

At one exact finite runtime occurrence there are two persistent whole
coordinates `w₀,w₁`.  Every actual prime-power row contributes one quotient
coordinate `q_(p,k)` and only the anti-invariant equation

`(w₀ - w₁) - p^k * q_(p,k) = 0`.

Reversal exchanges `w₀,w₁` and negates every quotient coordinate.  Runtime
successor forgets only newly generated quotient rows.  Thus frozen
prime-power rigidity can kill `w₀-w₁` without killing the shared diagonal
unit.  No completed `(p,k)` table, division root, fixedness or determinant is
accepted by this domain carrier.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationOccurrence
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram

noncomputable section

abbrev FactorExponent (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage) :=
  ExponentIndex (StageHistory seed stage) primeIndex

abbrev FactorRow (seed : FactorizationPayload) (stage : Nat) :=
  Σ primeIndex : StagePrime seed stage,
    FactorExponent seed stage primeIndex

/-- Retained for the full-Euler whole-relation complex.  The integral carrier
below uses the stricter `VertexIndex` with one quotient coordinate per row. -/
abbrev WholeRole (seed : FactorizationPayload) (stage : Nat) :=
  Option (FactorRow seed stage)

/-- Two whole endpoints plus one anti-invariant quotient coordinate per row. -/
abbrev VertexIndex (seed : FactorizationPayload) (stage : Nat) :=
  Fin 2 ⊕ FactorRow seed stage

abbrev VertexLattice (seed : FactorizationPayload) (stage : Nat) :=
  VertexIndex seed stage → ℤ

abbrev RelationIndex (seed : FactorizationPayload) (stage : Nat) :=
  FactorRow seed stage

abbrev RelationLattice (seed : FactorizationPayload) (stage : Nat) :=
  RelationIndex seed stage → ℤ

def rowPrime {seed : FactorizationPayload} {stage : Nat}
    (row : FactorRow seed stage) : Nat.Primes :=
  prime (StageHistory seed stage) row.1

def rowExponent {seed : FactorizationPayload} {stage : Nat}
    (row : FactorRow seed stage) : Nat :=
  exponent row.2

def wholeIndex (seed : FactorizationPayload) (stage : Nat)
    (dualIndex : Fin 2) : VertexIndex seed stage :=
  Sum.inl dualIndex

def quotientIndex {seed : FactorizationPayload} {stage : Nat}
    (row : FactorRow seed stage) : VertexIndex seed stage :=
  Sum.inr row

/-- Exact domain row: only the anti-invariant whole difference is divisible. -/
def factorizationEquation (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed stage →ₗ[ℤ] RelationLattice seed stage where
  toFun := fun value row =>
    (value (wholeIndex seed stage 0) -
        value (wholeIndex seed stage 1)) -
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        value (quotientIndex row)
  map_add' := by
    intro left right
    funext row
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro scalar value
    funext row
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Simultaneous integral solutions of every actual anti-invariant row. -/
abbrev Carrier (seed : FactorizationPayload) (stage : Nat) :=
  LinearMap.ker (factorizationEquation seed stage)

noncomputable def carrierBasis (seed : FactorizationPayload) (stage : Nat) :
    Σ rank : Nat, Module.Basis (Fin rank) ℤ (Carrier seed stage) :=
  Submodule.basisOfPid
    (Module.finBasis ℤ (VertexLattice seed stage))
    (Carrier seed stage)

noncomputable instance carrierFree (seed : FactorizationPayload)
    (stage : Nat) : Module.Free ℤ (Carrier seed stage) :=
  Module.Free.of_basis (carrierBasis seed stage).2

noncomputable instance carrierFinite (seed : FactorizationPayload)
    (stage : Nat) : Module.Finite ℤ (Carrier seed stage) :=
  Module.Finite.of_basis (carrierBasis seed stage).2

def wholeCoordinate (seed : FactorizationPayload) (stage : Nat)
    (dualIndex : Fin 2) : Carrier seed stage →ₗ[ℤ] ℤ where
  toFun value := value.1 (wholeIndex seed stage dualIndex)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def quotientCoordinate {seed : FactorizationPayload} {stage : Nat}
    (row : FactorRow seed stage) : Carrier seed stage →ₗ[ℤ] ℤ where
  toFun value := value.1 (quotientIndex row)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def wholeDifference (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage →ₗ[ℤ] ℤ :=
  wholeCoordinate seed stage 0 - wholeCoordinate seed stage 1

/-- The exact local landing is read from kernel membership of the same
carrier element. -/
theorem wholeDifference_eq_primePower_mul_quotientCoordinate
    (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage) (value : Carrier seed stage) :
    wholeDifference seed stage value =
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        quotientCoordinate row value := by
  have equationZero := congrFun (LinearMap.mem_ker.mp value.2) row
  change
    (value.1 (wholeIndex seed stage 0) -
        value.1 (wholeIndex seed stage 1)) -
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        value.1 (quotientIndex row) = 0 at equationZero
  change
    value.1 (wholeIndex seed stage 0) -
        value.1 (wholeIndex seed stage 1) =
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        value.1 (quotientIndex row)
  linarith

def wholeCoefficient (seed : FactorizationPayload) (stage : Nat) : Nat :=
  (factorialHistory (StageHistory seed stage)).cardinalShadow

def quotientCoefficient {seed : FactorizationPayload} {stage : Nat}
    (row : FactorRow seed stage) : Nat :=
  (quotientHistory row.1 row.2).cardinalShadow

theorem wholeCoefficient_eq_primePower_mul_quotientCoefficient
    (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage) :
    wholeCoefficient seed stage =
      (rowPrime row : Nat) ^ rowExponent row * quotientCoefficient row := by
  have landing := congrArg UnitHistory.cardinalShadow
    (primePower_joint_landing row.1 row.2)
  simpa [wholeCoefficient, quotientCoefficient, rowPrime, rowExponent,
    UnitHistory.cardinalShadow_joint, primePowerHistory,
    UnitHistory.cardinalShadow_generate] using landing

abbrev DualBase := Fin 2 → ℤ

/-- Actual history fold into the repaired carrier.  The single quotient row
reads the difference of the two source units. -/
def solutionVertex (seed : FactorizationPayload) (stage : Nat) :
    DualBase →ₗ[ℤ] VertexLattice seed stage where
  toFun := fun base index =>
    match index with
    | Sum.inl dualIndex =>
        (wholeCoefficient seed stage : ℤ) * base dualIndex
    | Sum.inr row =>
        (quotientCoefficient row : ℤ) * (base 0 - base 1)
  map_add' := by
    intro left right
    funext index
    cases index <;> simp only [Pi.add_apply] <;> ring
  map_smul' := by
    intro scalar base
    funext index
    cases index <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

theorem factorizationEquation_solutionVertex_eq_zero
    (seed : FactorizationPayload) (stage : Nat) (base : DualBase) :
    factorizationEquation seed stage (solutionVertex seed stage base) = 0 := by
  funext row
  change
    ((wholeCoefficient seed stage : ℤ) * base 0 -
        (wholeCoefficient seed stage : ℤ) * base 1) -
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        ((quotientCoefficient row : ℤ) * (base 0 - base 1)) = 0
  have coefficientEquality :=
    wholeCoefficient_eq_primePower_mul_quotientCoefficient seed stage row
  have coefficientEqualityInt :
      (wholeCoefficient seed stage : ℤ) =
        ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
          (quotientCoefficient row : ℤ) := by
    exact_mod_cast coefficientEquality
  rw [coefficientEqualityInt]
  ring

def solutionOfBase (seed : FactorizationPayload) (stage : Nat) :
    DualBase →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage) (solutionVertex seed stage)
    (fun base => by
      rw [LinearMap.mem_ker]
      exact factorizationEquation_solutionVertex_eq_zero seed stage base)

/-! ## Strong diagonal-unit kill test -/

def diagonalUnitVertex (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed stage
  | Sum.inl _dualIndex => 1
  | Sum.inr _row => 0

theorem factorizationEquation_diagonalUnitVertex_eq_zero
    (seed : FactorizationPayload) (stage : Nat) :
    factorizationEquation seed stage (diagonalUnitVertex seed stage) = 0 := by
  funext row
  simp [factorizationEquation, diagonalUnitVertex, wholeIndex, quotientIndex]

/-- `w₀=w₁=1, q_(p,k)=0` is an actual carrier element. -/
def diagonalUnit (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage :=
  ⟨diagonalUnitVertex seed stage,
    factorizationEquation_diagonalUnitVertex_eq_zero seed stage⟩

@[simp] theorem diagonalUnit_wholeCoordinate
    (seed : FactorizationPayload) (stage : Nat) (dualIndex : Fin 2) :
    wholeCoordinate seed stage dualIndex (diagonalUnit seed stage) = 1 := by
  rfl

@[simp] theorem diagonalUnit_quotientCoordinate
    (seed : FactorizationPayload) (stage : Nat)
    (row : FactorRow seed stage) :
    quotientCoordinate row (diagonalUnit seed stage) = 0 := by
  rfl

def liftFactorExponent (seed : FactorizationPayload) (stage : Nat)
    (primeIndex : StagePrime seed stage)
    (localExponent : FactorExponent seed stage primeIndex) :
    FactorExponent seed (stage + 1) (liftPrime seed stage primeIndex) := by
  refine ⟨localExponent.1, ?_⟩
  have order := factorization_mono_succ seed stage primeIndex.1
  exact localExponent.2.trans_le order

def liftFactorRow (seed : FactorizationPayload) (stage : Nat) :
    FactorRow seed stage → FactorRow seed (stage + 1)
  | ⟨primeIndex, localExponent⟩ =>
      ⟨liftPrime seed stage primeIndex,
        liftFactorExponent seed stage primeIndex localExponent⟩

@[simp] theorem liftFactorRow_prime (seed : FactorizationPayload)
    (stage : Nat) (row : FactorRow seed stage) :
    rowPrime (liftFactorRow seed stage row) = rowPrime row := by
  apply Subtype.ext
  rfl

@[simp] theorem liftFactorRow_exponent (seed : FactorizationPayload)
    (stage : Nat) (row : FactorRow seed stage) :
    rowExponent (liftFactorRow seed stage row) = rowExponent row := by
  rfl

def liftVertexIndex (seed : FactorizationPayload) (stage : Nat) :
    VertexIndex seed stage → VertexIndex seed (stage + 1)
  | Sum.inl dualIndex => Sum.inl dualIndex
  | Sum.inr row => Sum.inr (liftFactorRow seed stage row)

def liftRelationIndex (seed : FactorizationPayload) (stage : Nat) :
    RelationIndex seed stage → RelationIndex seed (stage + 1) :=
  liftFactorRow seed stage

def vertexRestriction (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed (stage + 1) →ₗ[ℤ] VertexLattice seed stage where
  toFun := fun value index => value (liftVertexIndex seed stage index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

def relationRestriction (seed : FactorizationPayload) (stage : Nat) :
    RelationLattice seed (stage + 1) →ₗ[ℤ] RelationLattice seed stage where
  toFun := fun value index => value (liftRelationIndex seed stage index)
  map_add' := by intro left right; rfl
  map_smul' := by intro scalar value; rfl

theorem restriction_equation_square (seed : FactorizationPayload)
    (stage : Nat) :
    (factorizationEquation seed stage).comp (vertexRestriction seed stage) =
      (relationRestriction seed stage).comp
        (factorizationEquation seed (stage + 1)) := by
  apply LinearMap.ext
  intro value
  funext row
  change
    (value (wholeIndex seed (stage + 1) 0) -
        value (wholeIndex seed (stage + 1) 1)) -
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        value (quotientIndex (liftFactorRow seed stage row)) =
    (value (wholeIndex seed (stage + 1) 0) -
        value (wholeIndex seed (stage + 1) 1)) -
      ((rowPrime (liftFactorRow seed stage row) : Nat) : ℤ) ^
          rowExponent (liftFactorRow seed stage row) *
        value (quotientIndex (liftFactorRow seed stage row))
  rw [liftFactorRow_prime, liftFactorRow_exponent]

/-- Actual successor restriction forgets only newly generated quotient rows. -/
def carrierRestriction (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed (stage + 1) →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage)
    ((vertexRestriction seed stage).comp (Carrier seed (stage + 1)).subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun
        (restriction_equation_square seed stage) value.1
      change factorizationEquation seed stage
          (vertexRestriction seed stage value.1) = 0
      change factorizationEquation seed stage
          (vertexRestriction seed stage value.1) =
        relationRestriction seed stage
          (factorizationEquation seed (stage + 1) value.1) at square
      rw [LinearMap.mem_ker.mp value.2, map_zero] at square
      exact square)

theorem carrierRestriction_wholeCoordinate (seed : FactorizationPayload)
    (stage : Nat) (dualIndex : Fin 2)
    (value : Carrier seed (stage + 1)) :
    wholeCoordinate seed stage dualIndex (carrierRestriction seed stage value) =
      wholeCoordinate seed (stage + 1) dualIndex value := by
  rfl

theorem carrierRestriction_quotientCoordinate (seed : FactorizationPayload)
    (stage : Nat) (row : FactorRow seed stage)
    (value : Carrier seed (stage + 1)) :
    quotientCoordinate row (carrierRestriction seed stage value) =
      quotientCoordinate (liftFactorRow seed stage row) value := by
  rfl

@[simp] theorem carrierRestriction_diagonalUnit
    (seed : FactorizationPayload) (stage : Nat) :
    carrierRestriction seed stage (diagonalUnit seed (stage + 1)) =
      diagonalUnit seed stage := by
  apply Subtype.ext
  funext index
  cases index <;> rfl

def vertexReversal (seed : FactorizationPayload) (stage : Nat) :
    VertexLattice seed stage →ₗ[ℤ] VertexLattice seed stage where
  toFun := fun value index =>
    match index with
    | Sum.inl dualIndex => value (wholeIndex seed stage dualIndex.rev)
    | Sum.inr row => -value (quotientIndex row)
  map_add' := by
    intro left right
    funext index
    cases index <;> simp [add_comm]
  map_smul' := by
    intro scalar value
    funext index
    cases index <;> simp

def relationReversal (seed : FactorizationPayload) (stage : Nat) :
    RelationLattice seed stage →ₗ[ℤ] RelationLattice seed stage where
  toFun := fun value row => -value row
  map_add' := by intro left right; funext row; simp [add_comm]
  map_smul' := by intro scalar value; funext row; simp

theorem reversal_equation_square (seed : FactorizationPayload) (stage : Nat) :
    (factorizationEquation seed stage).comp (vertexReversal seed stage) =
      (relationReversal seed stage).comp
        (factorizationEquation seed stage) := by
  apply LinearMap.ext
  intro value
  funext row
  change
    (value (wholeIndex seed stage 1) -
        value (wholeIndex seed stage 0)) -
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        (-value (quotientIndex row)) =
    -((value (wholeIndex seed stage 0) -
        value (wholeIndex seed stage 1)) -
      ((rowPrime row : Nat) : ℤ) ^ rowExponent row *
        value (quotientIndex row))
  ring

def carrierReversal (seed : FactorizationPayload) (stage : Nat) :
    Carrier seed stage →ₗ[ℤ] Carrier seed stage :=
  LinearMap.codRestrict (Carrier seed stage)
    ((vertexReversal seed stage).comp (Carrier seed stage).subtype)
    (fun value => by
      rw [LinearMap.mem_ker]
      have square := LinearMap.congr_fun
        (reversal_equation_square seed stage) value.1
      change factorizationEquation seed stage
          (vertexReversal seed stage value.1) = 0
      change factorizationEquation seed stage
          (vertexReversal seed stage value.1) =
        relationReversal seed stage
          (factorizationEquation seed stage value.1) at square
      rw [LinearMap.mem_ker.mp value.2, map_zero] at square
      exact square)

theorem carrierReversal_involutive (seed : FactorizationPayload)
    (stage : Nat) : Function.Involutive (carrierReversal seed stage) := by
  intro value
  apply Subtype.ext
  funext index
  cases index with
  | inl dualIndex =>
      simp [carrierReversal, vertexReversal, wholeIndex, quotientIndex]
  | inr row =>
      simp [carrierReversal, vertexReversal, wholeIndex, quotientIndex]

@[simp] theorem carrierReversal_diagonalUnit
    (seed : FactorizationPayload) (stage : Nat) :
    carrierReversal seed stage (diagonalUnit seed stage) =
      diagonalUnit seed stage := by
  apply Subtype.ext
  funext index
  cases index <;> simp [carrierReversal, vertexReversal, diagonalUnit,
    diagonalUnitVertex, wholeIndex, quotientIndex]

theorem carrierRestriction_reversal_square (seed : FactorizationPayload)
    (stage : Nat) :
    (carrierRestriction seed stage).comp (carrierReversal seed (stage + 1)) =
      (carrierReversal seed stage).comp (carrierRestriction seed stage) := by
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  funext index
  cases index <;> rfl

/-- Exact-root occurrence of the repaired anti-invariant equation. -/
def solutionOccurrence (seed : FactorizationPayload) (stage : Nat) :
    RootedAccountedUnfolding
      (FactorizationPayload ×
        (VertexLattice seed stage →ₗ[ℤ] RelationLattice seed stage)) :=
  (stageOccurrenceFrom seed stage).map fun owner =>
    (owner, factorizationEquation seed stage)

theorem solutionOccurrence_projects (seed : FactorizationPayload)
    (stage : Nat) :
    (solutionOccurrence seed stage).map Prod.fst =
      stageOccurrenceFrom seed stage := by
  unfold solutionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change (stageOccurrenceFrom seed stage).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem preserves_antiInvariant_rows_diagonalUnit_reversal_and_successor
    (seed : FactorizationPayload) (stage : Nat) :
    (solutionOccurrence seed stage).root.2 =
        factorizationEquation seed stage ∧
      wholeCoordinate seed stage 0 (diagonalUnit seed stage) = 1 ∧
      wholeCoordinate seed stage 1 (diagonalUnit seed stage) = 1 ∧
      (∀ row, quotientCoordinate row (diagonalUnit seed stage) = 0) ∧
      Function.Involutive (carrierReversal seed stage) ∧
      carrierRestriction seed stage (diagonalUnit seed (stage + 1)) =
        diagonalUnit seed stage ∧
      (carrierRestriction seed stage).comp
          (carrierReversal seed (stage + 1)) =
        (carrierReversal seed stage).comp (carrierRestriction seed stage) := by
  exact ⟨by simp [solutionOccurrence], diagonalUnit_wholeCoordinate _ _ _,
    diagonalUnit_wholeCoordinate _ _ _, diagonalUnit_quotientCoordinate _ _,
    carrierReversal_involutive seed stage,
    carrierRestriction_diagonalUnit seed stage,
    carrierRestriction_reversal_square seed stage⟩

end
end CanonicalUnitArithmeticFactorizationWholeHistorySolutionCarrier
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
