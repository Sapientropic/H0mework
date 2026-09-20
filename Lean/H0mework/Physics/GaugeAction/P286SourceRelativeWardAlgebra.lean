import H0mework.Physics.GaugeAction.P286BracketCalculus
import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryVariation

/-!
# Stage-9 source-relative P286 Ward algebra

This dependency-light module exposes the invariant pairing identity required
by the source-relative P286 Ward balance.  The proof is performed directly
on the typed matrix commutator and uses cyclicity of the finite matrix trace:

```text
⟪[X,Y], Z⟫ = ⟪X, [Y,Z]⟫.
```

No action-invariance premise, Ward certificate, equation, residual zero,
source torque cancellation, or stationary actual is accepted.  In
particular, later frozen-source Ward theorems must still retain their scalar
source-torque term.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP286SourceRelativeWardAlgebra

open StageNineHolonomicField
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open StageNineGlobalIntegratedAction
open StageNineP286GaugeAuxiliaryVariation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

local instance p286WardAlgebraModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286WardAlgebraCoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Trace-invariant typed Lie pairings -/

/-- Cyclicity of the matrix trace makes the special-unitary Lie pairing
invariant under the actual commutator. -/
theorem specialUnitaryLiePairing_bracket_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    specialUnitaryLiePairing (suLieBracket first second) residual =
      specialUnitaryLiePairing first (suLieBracket second residual) := by
  unfold specialUnitaryLiePairing suLieBracket
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle'
    (first : Matrix n n ℂ) (residual : Matrix n n ℂ)
    (second : Matrix n n ℂ)]

/-- The product P286 pairing inherits trace invariance in both non-Abelian
blocks; its Abelian hypercharge commutator is zero definitionally. -/
theorem p286LiePairing_bracket_left
    (first second residual : P286LieBlockData) :
    p286LiePairing (p286LieBracket first second) residual =
      p286LiePairing first (p286LieBracket second residual) := by
  unfold p286LiePairing p286LieBracket
  rw [specialUnitaryLiePairing_bracket_left,
    specialUnitaryLiePairing_bracket_left]
  simp [hyperchargeLiePairing]

/-- Public dependency-light coordinate form used by the later Ward and
BF-double-divergence calculations. -/
theorem p286CoordinateLiePairing_bracket_left
    (first second residual : P286CoordinateCarrier) :
    p286CoordinateLiePairing
        (p286CoordinateLieBracket first second) residual =
      p286CoordinateLiePairing first
        (p286CoordinateLieBracket second residual) := by
  unfold p286CoordinateLiePairing p286CoordinateLieBracket
  simp only [LinearEquiv.symm_apply_apply]
  exact p286LiePairing_bracket_left _ _ _

end

end
  SaturationMonoid.PhysicsCore.StageNineP286SourceRelativeWardAlgebra
