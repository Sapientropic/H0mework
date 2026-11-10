import Mathlib.Tactic
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.BoundedSuccessorRealizationSteps
import H0mework.Versions.Re60a8605.ReleaseMaterials.RepresentationArithmeticAtomProjectionDefect.Lean.SignedResidualNatAbs

/-!
# Composite source successor steps

This module upgrades the non-prime calibration from an order-threshold atom
filter to a multiplicative source family:

```text
CompositeAtom m := exists a b >= 2, m = a*b
```

For `n >= 6`, a residual-height source produces a composite endpoint pair by
parity:

```text
height 2*t     |-> (4, 2*(n+t-2))
height 2*t + 1 |-> (9, 2*(n+t-4))
```

The endpoint sum is always `2*n + height`, so the atom-pair energy is exactly
the source height.  This supplies bounded positive successor-realization steps
without a finite endpoint table, Bool coverage, or a prime-pair premise.
-/

namespace RepresentationArithmeticAtomProjectionDefect

namespace CompositeSourceFamily

/-- Multiplicative composite endpoint filter.  This is deliberately not the
prime / multiplicative-atom predicate: every accepted endpoint carries a
nontrivial multiplicative factorization. -/
def CompositeAtom (m : Nat) : Prop :=
  ∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧ m = a * b

/-- The composite filter admits `4 = 2*2`. -/
theorem composite_four : CompositeAtom 4 := by
  exact ⟨2, 2, by decide, by decide, rfl⟩

/-- The composite filter admits `9 = 3*3`. -/
theorem composite_nine : CompositeAtom 9 := by
  exact ⟨3, 3, by decide, by decide, rfl⟩

/-- Every sufficiently large even endpoint is composite by the visible factor
`2*q`. -/
theorem composite_two_mul (q : Nat) (hq : 2 ≤ q) :
    CompositeAtom (2 * q) := by
  exact ⟨2, q, by decide, hq, rfl⟩

/-- Sanity check: this family is not the natural-number multiplicative atom
predicate. -/
theorem four_not_nat_multiplicatively_atomic :
    ¬ NatMultiplicativelyAtomic 4 := by
  intro hAtomic
  have hFactor : (2 : Nat) = 1 ∨ (2 : Nat) = 1 :=
    hAtomic.right (show 4 = 2 * 2 by rfl)
  rcases hFactor with hLeft | hRight
  · norm_num at hLeft
  · norm_num at hRight

/-- Source evidence for the composite family: a residual height with its parity
branch resolved. -/
inductive CompositeShellSource where
  | even (t : Nat)
  | odd (t : Nat)

namespace CompositeShellSource

/-- Residual height carried by a parity-resolved source object. -/
def energy : CompositeShellSource -> Nat
  | even t => 2 * t
  | odd t => 2 * t + 1

/-- Canonical source object for any residual height. -/
def sourceOfHeight : Nat -> CompositeShellSource
  | 0 => even 0
  | Nat.succ k =>
      match sourceOfHeight k with
      | even t => odd t
      | odd t => even (t + 1)

/-- The canonical source object reads back to the requested residual height. -/
theorem sourceOfHeight_energy (k : Nat) :
    energy (sourceOfHeight k) = k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      cases hSource : sourceOfHeight k with
      | even t =>
          simp [sourceOfHeight, hSource, energy] at ih ⊢
          omega
      | odd t =>
          simp [sourceOfHeight, hSource, energy] at ih ⊢
          omega

end CompositeShellSource

/-- Additive residual transport for the parity-resolved source heights. -/
def residualTransport :
    AdditiveResidualTransportCategory CompositeShellSource where
  residualEnergy := CompositeShellSource.energy
  step := fun source target =>
    CompositeShellSource.energy target + 1 =
      CompositeShellSource.energy source
  step_decreases_one := by
    intro _ _ hstep
    exact hstep

/-- Trivial feasible source category for the composite source-height toy. -/
def sourceCategory :
    RepresentationFeasibleCategory CompositeShellSource where
  feasible := fun _ => True
  path := fun source target =>
    CompositeShellSource.energy target ≤
      CompositeShellSource.energy source
  path_preserves_feasible := by
    intro _ _ _ _
    trivial

/-- A residual step is a source path for the source-height category. -/
theorem stepPathCompatibility :
    ResidualStepSourcePathCompatibility
      CompositeShellSource residualTransport sourceCategory where
  step_is_path := by
    intro source target hstep
    dsimp [residualTransport, sourceCategory] at hstep ⊢
    have hle :
        CompositeShellSource.energy target ≤
          CompositeShellSource.energy target + 1 :=
      Nat.le_succ _
    rwa [hstep] at hle

/-- Endpoint-code formula produced by the composite source family. -/
def sourceCode (n : Nat) :
    CompositeShellSource -> EndpointCodePair n
  | CompositeShellSource.even t => {
      leftCode := 4
      rightCode := 2 * (n + t - 2)
    }
  | CompositeShellSource.odd t => {
      leftCode := 9
      rightCode := 2 * (n + t - 4)
    }

theorem sourceCode_left_atomic (n : Nat)
    (source : CompositeShellSource) :
    CompositeAtom (sourceCode n source).leftCode := by
  cases source with
  | even _ =>
      exact composite_four
  | odd _ =>
      exact composite_nine

theorem sourceCode_right_atomic (n : Nat)
    (source : CompositeShellSource) (hn : 6 ≤ n) :
    CompositeAtom (sourceCode n source).rightCode := by
  cases source with
  | even t =>
      dsimp [sourceCode]
      exact composite_two_mul (n + t - 2) (by omega)
  | odd t =>
      dsimp [sourceCode]
      exact composite_two_mul (n + t - 4) (by omega)

/-- The composite source-code formula lands in the shell `2*n + height`. -/
theorem sourceCode_sum (n : Nat)
    (source : CompositeShellSource) (hn : 6 ≤ n) :
    (sourceCode n source).leftCode +
      (sourceCode n source).rightCode =
    2 * n + CompositeShellSource.energy source := by
  cases source with
  | even t =>
      dsimp [sourceCode, CompositeShellSource.energy]
      omega
  | odd t =>
      dsimp [sourceCode, CompositeShellSource.energy]
      omega

/-- The source-code formula has exactly the source residual height as energy.
-/
theorem sourceCode_energy (n : Nat)
    (source : CompositeShellSource) (hn : 6 ≤ n) :
    EndpointCodePair.energy (sourceCode n source) =
      CompositeShellSource.energy source := by
  rw [EndpointCodePair.energy, EndpointCodePair.residual]
  rw [sourceCode_sum n source hn]
  exact
    natAbs_center_minus_center_add
      (2 * n) (CompositeShellSource.energy source)

/-- Faithful endpoint-code projection for the composite source family. -/
def codeProjection (n : Nat) (hn : 6 ≤ n) :
    AtomicEndpointCodeProjection
      CompositeAtom CompositeShellSource n residualTransport where
  codeProjection := {
    projectCode := fun source => some (sourceCode n source)
    code_energy_faithful := by
      intro source code hproject
      cases hproject
      exact sourceCode_energy n source hn
  }
  left_atomic := by
    intro source code hproject
    cases hproject
    exact sourceCode_left_atomic n source
  right_atomic := by
    intro source code hproject
    cases hproject
    exact sourceCode_right_atomic n source hn

/-- Composite atom-pair readout of a source object. -/
def sourceAtomPair (n : Nat)
    (source : CompositeShellSource) (hn : 6 ≤ n) :
    ArithmeticAtomPair CompositeAtom n :=
  atomPairOfEndpointCodePair
    (sourceCode n source)
    (sourceCode_left_atomic n source)
    (sourceCode_right_atomic n source hn)

theorem sourceAtomPair_energy (n : Nat)
    (source : CompositeShellSource) (hn : 6 ≤ n) :
    ArithmeticAtomPair.energy (sourceAtomPair n source hn) =
      CompositeShellSource.energy source := by
  dsimp [sourceAtomPair]
  rw [atomPairOfEndpointCodePair_energy]
  exact sourceCode_energy n source hn

/-- Every residual height has a formula-produced composite atom-pair
realization. -/
theorem atom_pair_realization_of_source_height
    (n k : Nat) (hn : 6 ≤ n) :
    ∃ p : ArithmeticAtomPair CompositeAtom n,
      ArithmeticAtomPair.energy p = k := by
  refine
    ⟨sourceAtomPair n (CompositeShellSource.sourceOfHeight k) hn, ?_⟩
  rw [sourceAtomPair_energy]
  exact CompositeShellSource.sourceOfHeight_energy k

/-- The source object at height `k+1` supplies the positive successor-shell
realization. -/
theorem atom_pair_realization_successor_of_source_step
    (n : Nat) (hn : 6 ≤ n) {k : Nat} :
    (∃ p : ArithmeticAtomPair CompositeAtom n,
      ArithmeticAtomPair.energy p = k) ->
    ∃ p : ArithmeticAtomPair CompositeAtom n,
      ArithmeticAtomPair.energy p = k + 1 := by
  intro _hRealized
  exact atom_pair_realization_of_source_height n (k + 1) hn

/-- Multiplicative factorization category for composite endpoint atoms. -/
def compositeFactorizationCategory :
    MultiplicativeAtomFactorizationCategory CompositeAtom :=
  listProductMultiplicativeAtomFactorizationCategory CompositeAtom

/-- Source-height realization with endpoint factorization readout. -/
theorem factorized_atom_pair_realization_of_source_height
    (n k : Nat) (hn : 6 ≤ n) :
    FactorizedAtomPairRealization
      CompositeAtom compositeFactorizationCategory n k := by
  rcases atom_pair_realization_of_source_height n k hn with
    ⟨p, hEnergy⟩
  exact
    factorizedAtomPairRealizationOfPair
      compositeFactorizationCategory p hEnergy

/-- The composite source family supplies bounded positive realization-successor
steps without finite endpoint search or endpoint coverage. -/
theorem boundedCompositeAtomPairRealizationSuccessorSteps
    (n bound : Nat) (hn : 6 ≤ n) :
    BoundedAtomPairRealizationSuccessorSteps CompositeAtom n bound := by
  exact {
    lift_realization := by
      intro k _hk hRealized
      exact
        atom_pair_realization_successor_of_source_step
          n hn hRealized
  }


end CompositeSourceFamily

end RepresentationArithmeticAtomProjectionDefect
