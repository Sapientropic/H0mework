import H0mework.Physics.Geometry.PlebanskiReductionCoherence
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# A genuine Plebanski first-variation coordinate

`PlebanskiFirstVariationOperators.deltaBOf` is an operation supplied by an
action-variation system.  Merely applying that operation to the stored master
action does not prove that the result is its mathematical derivative.

This module fixes the meaning of the bivector channel using Mathlib's
`HasFDerivAt`: the residual carrier is the continuous linear derivative of the
action with respect to the bivector coordinate.  The correctness relation is
therefore not an arbitrary compatibility predicate supplied by a caller.

The concrete quadratic model then keeps the master action, reduced action,
and exact `II+` reduction provenance unchanged while changing only the stored
candidate derivative.  It proves local independence of derivative provenance
from branch-reduction provenance.  The other three Plebanski channels still
need their own coordinate substitutions and derivative theorems before a
complete physical admissibility statement can be made.
-/

namespace SaturationMonoid
namespace PhysicsCore

universe uScalar uConstitutive uConnection uBivector uMultiplier uMatter
universe uTetrad uActionValue uDeltaPhi uDeltaOmega uDeltaE

/-- The stored `δB` residual is the actual Fréchet derivative of the master
action along the bivector coordinate at every configuration. -/
def PlebanskiBivectorFirstVariationCorrect
    {Scalar : Type uScalar} {Constitutive : Type uConstitutive}
    {Connection : Type uConnection} {BivectorTwoForm : Type uBivector}
    {Multiplier : Type uMultiplier} {Matter : Type uMatter}
    {Tetrad : Type uTetrad} {ActionValue : Type uActionValue}
    {DeltaPhiResidual : Type uDeltaPhi}
    {DeltaOmegaResidual : Type uDeltaOmega}
    {DeltaEResidual : Type uDeltaE}
    [NontriviallyNormedField Scalar]
    [NormedAddCommGroup BivectorTwoForm]
    [NormedSpace Scalar BivectorTwoForm]
    [NormedAddCommGroup ActionValue]
    [NormedSpace Scalar ActionValue]
    (S : PlebanskiActionVariationSystem Constitutive Connection
      BivectorTwoForm Multiplier Matter Tetrad ActionValue
      (BivectorTwoForm →L[Scalar] ActionValue) DeltaPhiResidual
      DeltaOmegaResidual DeltaEResidual) : Prop :=
  ∀ law q,
    HasFDerivAt
      (fun b : BivectorTwoForm =>
        S.masterAction law (q.withBivector b))
      (S.firstVariation.deltaBOf S.masterAction law q)
      q.bivector

/-! ## Concrete local independence witness -/

namespace PlebanskiFirstVariationProvenanceToy

abbrev Configuration :=
  PlebanskiMasterConfiguration Unit ℝ Unit Unit

abbrev BivectorCovector := ℝ →L[ℝ] ℝ

abbrev System :=
  PlebanskiActionVariationSystem Unit Unit ℝ Unit Unit Unit ℝ
    BivectorCovector Unit Unit Unit

def masterAction : Unit → Configuration → ℝ :=
  fun _ q => q.bivector ^ 2

def rawSubstitution : RawPlebanskiIIPlusSubstitution ℝ Unit where
  tetradWedge := fun _ => 0
  internalBivectorDual := id

def correctFirstVariation :
    PlebanskiFirstVariationOperators Unit Unit ℝ Unit Unit Unit ℝ
      BivectorCovector Unit Unit Unit where
  deltaBOf := fun _ _ q =>
    (2 * q.bivector) • ContinuousLinearMap.id ℝ ℝ
  deltaPhiOf := fun _ _ _ => ()
  deltaOmegaOf := fun _ _ _ => ()
  deltaEOf := fun _ _ _ _ => ()

def incorrectFirstVariation :
    PlebanskiFirstVariationOperators Unit Unit ℝ Unit Unit Unit ℝ
      BivectorCovector Unit Unit Unit where
  deltaBOf := fun _ _ _ => 0
  deltaPhiOf := fun _ _ _ => ()
  deltaOmegaOf := fun _ _ _ => ()
  deltaEOf := fun _ _ _ _ => ()

def correctSystem : System :=
  ⟨masterAction,
    restrictMasterActionByIIPlusSubstitution rawSubstitution masterAction,
    correctFirstVariation⟩

def incorrectSystem : System :=
  ⟨masterAction,
    restrictMasterActionByIIPlusSubstitution rawSubstitution masterAction,
    incorrectFirstVariation⟩

/-- Keep the correct derivative but replace the computed reduced action by an
independent constant. -/
def reductionIncorrectSystem : System :=
  ⟨masterAction, fun _ _ _ => 1, correctFirstVariation⟩

theorem correctSystem_bivectorFirstVariationCorrect :
    PlebanskiBivectorFirstVariationCorrect correctSystem := by
  intro law q
  simpa [correctSystem, correctFirstVariation, masterAction,
    PlebanskiMasterConfiguration.withBivector] using
      (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := q.bivector))

theorem incorrectSystem_bivectorFirstVariation_not_correct :
    ¬ PlebanskiBivectorFirstVariationCorrect incorrectSystem := by
  intro hcorrect
  let q : Configuration :=
    { connection := (), bivector := 1, multiplier := (), matter := () }
  have hincorrect := hcorrect () q
  have hactual :=
    hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := (1 : ℝ))
  have heq := hactual.unique hincorrect
  have hvalue := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) heq
  norm_num [incorrectSystem, incorrectFirstVariation, masterAction,
    PlebanskiMasterConfiguration.withBivector, q] at hvalue

theorem reductionIncorrectSystem_bivectorFirstVariationCorrect :
    PlebanskiBivectorFirstVariationCorrect reductionIncorrectSystem := by
  intro law q
  simpa [reductionIncorrectSystem, correctFirstVariation, masterAction,
    PlebanskiMasterConfiguration.withBivector] using
      (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) 2 (x := q.bivector))

theorem correctSystem_reductionCoherent :
    PlebanskiRawIIPlusReductionCoherent correctSystem rawSubstitution :=
  rfl

theorem incorrectSystem_reductionCoherent :
    PlebanskiRawIIPlusReductionCoherent incorrectSystem rawSubstitution :=
  rfl

theorem reductionIncorrectSystem_not_reductionCoherent :
    ¬ PlebanskiRawIIPlusReductionCoherent
      reductionIncorrectSystem rawSubstitution := by
  intro hcoherent
  let q : Configuration :=
    { connection := (), bivector := 0, multiplier := (), matter := () }
  have hvalue := congrFun
    (congrFun (congrFun hcoherent ()) q) ()
  norm_num [reductionIncorrectSystem,
    PlebanskiRawIIPlusReductionCoherent,
    restrictMasterActionByIIPlusSubstitution, rawSubstitution,
    RawPlebanskiIIPlusSubstitution.gravitationalBivector,
    masterAction, PlebanskiMasterConfiguration.withBivector, q] at hvalue

/-- The same action and the same correctly restricted reduced action admit a
correct or an incorrect stored `δB` candidate.  Thus actual derivative
provenance cannot be inferred from branch-reduction provenance. -/
theorem bivectorFirstVariationProvenance_independent_of_reductionCoherence :
    ∃ good bad : System,
      good.masterAction = bad.masterAction ∧
        good.reducedIIPlusAction = bad.reducedIIPlusAction ∧
        PlebanskiRawIIPlusReductionCoherent good rawSubstitution ∧
        PlebanskiRawIIPlusReductionCoherent bad rawSubstitution ∧
        PlebanskiBivectorFirstVariationCorrect good ∧
        ¬ PlebanskiBivectorFirstVariationCorrect bad :=
  ⟨correctSystem, incorrectSystem, rfl, rfl,
    correctSystem_reductionCoherent, incorrectSystem_reductionCoherent,
    correctSystem_bivectorFirstVariationCorrect,
    incorrectSystem_bivectorFirstVariation_not_correct⟩

/-- Conversely, a correct mathematical derivative does not force the stored
reduced action to come from the raw substitution. -/
theorem reductionProvenance_independent_of_bivectorFirstVariation :
    ∃ good bad : System,
      PlebanskiBivectorFirstVariationCorrect good ∧
        PlebanskiBivectorFirstVariationCorrect bad ∧
        PlebanskiRawIIPlusReductionCoherent good rawSubstitution ∧
        ¬ PlebanskiRawIIPlusReductionCoherent bad rawSubstitution :=
  ⟨correctSystem, reductionIncorrectSystem,
    correctSystem_bivectorFirstVariationCorrect,
    reductionIncorrectSystem_bivectorFirstVariationCorrect,
    correctSystem_reductionCoherent,
    reductionIncorrectSystem_not_reductionCoherent⟩

end PlebanskiFirstVariationProvenanceToy

end PhysicsCore
end SaturationMonoid
