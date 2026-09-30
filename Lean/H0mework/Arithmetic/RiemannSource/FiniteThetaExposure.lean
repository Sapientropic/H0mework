import H0mework.Arithmetic.EulerGlobal.CoordinateGerm
import H0mework.Foundation.Source.AdditiveTraceFold
import H0mework.Foundation.Source.TraceAdvance

/-!
# Canonical Riemann finite theta exposure

Each positive integer magnitude is read from the current of one exact
canonical arithmetic runtime.  Its positive and negative Gaussian terms are
then emitted together by one finite rooted advance.  There is no caller-
supplied integer window, sign selector, completed theta function, analytic
continuation, zeta value, or zero.

The generated finite material is installed as a dependent payload on
`globalGermOccurrence`; forgetting that payload returns the literal same
occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open ArithmeticGeneration
open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticRoot
open CanonicalUnitArithmeticRuntimeCofinalEuler
open RootedAccountedUnfolding

noncomputable section

abbrev GlobalGermOwner :=
  FactorizationPayload × GeneratedGlobalDeterminantCoordinateGerm

/-- The current history of an exact runtime generates one positive shell
magnitude.  The private constructor prevents detached magnitude submission. -/
structure GeneratedIntegerShellAt (owner : GlobalGermOwner) : Type 5 where
  private mk ::
  stage : Nat
  authority : RuntimeAuthority
  authority_eq : authority = runtimeAuthorityAt stage
  magnitude : Nat
  magnitude_eq :
    magnitude = authority.1.current.visit.current.cardinalShadow

namespace GeneratedIntegerShellAt

def generate (owner : GlobalGermOwner) (stage : Nat) :
    GeneratedIntegerShellAt owner where
  stage := stage
  authority := runtimeAuthorityAt stage
  authority_eq := rfl
  magnitude := (runtimeAt stage).current.visit.current.cardinalShadow
  magnitude_eq := rfl

def positivePoint {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) : ℤ :=
  shell.magnitude

def negativePoint {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) : ℤ :=
  -shell.magnitude

end GeneratedIntegerShellAt

/-- The source current at stage `n` contains exactly `n + 1` actual units.
This is the arithmetic origin of the theta-shell magnitude. -/
theorem runtimeCurrent_cardinalShadow (stage : Nat) :
    (runtimeAt stage).current.visit.current.cardinalShadow = stage + 1 := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [runtimeAt_succ]
      change Nat.succ (runtimeAt stage).current.visit.current.cardinalShadow =
        Nat.succ stage + 1
      omega

@[simp] theorem GeneratedIntegerShellAt.generate_magnitude
    (owner : GlobalGermOwner) (stage : Nat) :
    (GeneratedIntegerShellAt.generate owner stage).magnitude = stage + 1 := by
  exact runtimeCurrent_cardinalShadow stage

@[simp] theorem GeneratedIntegerShellAt.generate_positivePoint
    (owner : GlobalGermOwner) (stage : Nat) :
    (GeneratedIntegerShellAt.generate owner stage).positivePoint =
      ((stage + 1 : ℕ) : ℤ) := by
  rw [GeneratedIntegerShellAt.positivePoint,
    GeneratedIntegerShellAt.generate_magnitude]

@[simp] theorem GeneratedIntegerShellAt.generate_negativePoint
    (owner : GlobalGermOwner) (stage : Nat) :
    (GeneratedIntegerShellAt.generate owner stage).negativePoint =
      -((stage + 1 : ℕ) : ℤ) := by
  rw [GeneratedIntegerShellAt.negativePoint,
    GeneratedIntegerShellAt.generate_magnitude]

theorem GeneratedIntegerShellAt.generate_authority_succ
    (owner : GlobalGermOwner) (stage : Nat) :
    (GeneratedIntegerShellAt.generate owner (stage + 1)).authority.1 =
      (GeneratedIntegerShellAt.generate owner stage).authority.1.tick.next := by
  exact runtimeAt_succ stage

/-- One shell has an anchor and the two source-generated orientations.  The
orientations are emitted together; there is no exposed bit selecting one. -/
inductive ThetaShellEventAt (owner : GlobalGermOwner) : Type 5
  | anchor (shell : GeneratedIntegerShellAt owner)
  | positive (shell : GeneratedIntegerShellAt owner)
  | negative (shell : GeneratedIntegerShellAt owner)

namespace ThetaShellEventAt

def latticePoint {owner : GlobalGermOwner} :
    ThetaShellEventAt owner → Option ℤ
  | .anchor _ => none
  | .positive shell => some shell.positivePoint
  | .negative shell => some shell.negativePoint

end ThetaShellEventAt

/-- The exact generated two-sided patch. -/
def thetaShellPatch {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) :
    RootedAccountedUnfolding (ThetaShellEventAt owner) :=
  .occur (.positive shell)
    (.singleton (RootedAccountedUnfolding.zero (.negative shell)))

/-- One shell is born by advancing its rooted anchor exactly once. -/
def thetaShellOccurrence {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) :
    RootedAccountedUnfolding (ThetaShellEventAt owner) :=
  (RootedAccountedUnfolding.zero (.anchor shell)).advance
    (fun _ => thetaShellPatch shell)

@[simp] theorem thetaShellOccurrence_trace {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) :
    (thetaShellOccurrence shell).trace =
      [.anchor shell, .positive shell, .negative shell] := by
  rfl

@[simp] theorem thetaShellOccurrence_frontier {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) :
    (thetaShellOccurrence shell).frontier = [.negative shell] := by
  rfl

@[simp] theorem thetaShellOccurrence_latticePoints
    {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner) :
    (thetaShellOccurrence shell).trace.filterMap
        ThetaShellEventAt.latticePoint =
      [shell.positivePoint, shell.negativePoint] := by
  rfl

/-- Every event in a shell is old anchor material or belongs to the exact
patch generated at that anchor. -/
theorem thetaShellOccurrence_event_provenance
    {owner : GlobalGermOwner}
    (shell : GeneratedIntegerShellAt owner)
    (event : ThetaShellEventAt owner) :
    event ∈ (thetaShellOccurrence shell).trace ↔
      event ∈ (RootedAccountedUnfolding.zero
        (ThetaShellEventAt.anchor shell)).trace ∨
        ∃ leaf,
          leaf ∈ (RootedAccountedUnfolding.zero
            (ThetaShellEventAt.anchor shell)).frontier ∧
            event ∈ (thetaShellPatch shell).trace :=
  mem_trace_advance_iff (fun _ => thetaShellPatch shell)
    (RootedAccountedUnfolding.zero
      (ThetaShellEventAt.anchor shell)) event

noncomputable def gaussianWeight {owner : GlobalGermOwner} (t : ℝ) :
    ThetaShellEventAt owner → ℝ
  | .anchor _ => 0
  | .positive shell =>
      Real.exp (-Real.pi * (shell.positivePoint : ℝ) ^ 2 * t)
  | .negative shell =>
      Real.exp (-Real.pi * (shell.negativePoint : ℝ) ^ 2 * t)

/-- The finite Gaussian value is read only by the canonical additive fold. -/
noncomputable def thetaShellFold {owner : GlobalGermOwner}
    (t : ℝ) (shell : GeneratedIntegerShellAt owner) : ℝ :=
  (thetaShellOccurrence shell).fold
    (additiveFoldAlgebra (gaussianWeight t))

theorem thetaShellFold_eq_traceSum {owner : GlobalGermOwner}
    (t : ℝ) (shell : GeneratedIntegerShellAt owner) :
    thetaShellFold t shell =
      traceSum (gaussianWeight t) (thetaShellOccurrence shell) := by
  unfold thetaShellFold
  exact (traceSum_eq_fold (gaussianWeight t)
    (thetaShellOccurrence shell)).symm

@[simp] theorem thetaShellFold_eq_two_mul {owner : GlobalGermOwner}
    (t : ℝ) (shell : GeneratedIntegerShellAt owner) :
    thetaShellFold t shell =
      2 * Real.exp (-Real.pi * (shell.magnitude : ℝ) ^ 2 * t) := by
  rw [thetaShellFold_eq_traceSum]
  simp [traceSum, gaussianWeight,
    GeneratedIntegerShellAt.positivePoint,
    GeneratedIntegerShellAt.negativePoint]
  ring

/-- A finite theta patch is indexed by its exact global-germ owner. -/
structure GeneratedFiniteThetaPatchAt (owner : GlobalGermOwner) : Type 5 where
  private mk ::
  shell : GeneratedIntegerShellAt owner
  exposure : RootedAccountedUnfolding (ThetaShellEventAt owner)
  exposure_eq : exposure = thetaShellOccurrence shell

namespace GeneratedFiniteThetaPatchAt

def generate (owner : GlobalGermOwner) (stage : Nat) :
    GeneratedFiniteThetaPatchAt owner where
  shell := GeneratedIntegerShellAt.generate owner stage
  exposure := thetaShellOccurrence
    (GeneratedIntegerShellAt.generate owner stage)
  exposure_eq := rfl

/-- The cofinal consumer must fold this stored exposure, not regenerate a
parallel shell occurrence. -/
noncomputable def gaussianFold {owner : GlobalGermOwner}
    (generated : GeneratedFiniteThetaPatchAt owner) (t : ℝ) : ℝ :=
  generated.exposure.fold
    (additiveFoldAlgebra (gaussianWeight t))

theorem gaussianFold_eq_thetaShellFold {owner : GlobalGermOwner}
    (generated : GeneratedFiniteThetaPatchAt owner) (t : ℝ) :
    generated.gaussianFold t = thetaShellFold t generated.shell := by
  unfold gaussianFold thetaShellFold
  rw [generated.exposure_eq]

@[simp] theorem generate_gaussianFold
    (owner : GlobalGermOwner) (stage : Nat) (t : ℝ) :
    (generate owner stage).gaussianFold t =
      2 * Real.exp (-Real.pi * (stage + 1 : ℕ) ^ 2 * t) := by
  rw [gaussianFold_eq_thetaShellFold, thetaShellFold_eq_two_mul]
  change 2 * Real.exp (-Real.pi *
      ((GeneratedIntegerShellAt.generate owner stage).magnitude : ℝ) ^ 2 * t) = _
  rw [GeneratedIntegerShellAt.generate_magnitude]

end GeneratedFiniteThetaPatchAt

abbrev FiniteThetaPayload :=
  Σ owner : GlobalGermOwner, GeneratedFiniteThetaPatchAt owner

/-- Literal same occurrence, now carrying its source-generated finite theta
patch as a dependent face. -/
def finiteThetaOccurrence (stage : Nat) :
    RootedAccountedUnfolding FiniteThetaPayload :=
  globalGermOccurrence.map fun owner =>
    ⟨owner, GeneratedFiniteThetaPatchAt.generate owner stage⟩

theorem finiteThetaOccurrence_projects (stage : Nat) :
    (finiteThetaOccurrence stage).map Sigma.fst = globalGermOccurrence := by
  rw [finiteThetaOccurrence, RootedAccountedUnfolding.map_map]
  change globalGermOccurrence.map id = globalGermOccurrence
  exact RootedAccountedUnfolding.map_id _

@[simp] theorem finiteThetaOccurrence_root_payload (stage : Nat) :
    (finiteThetaOccurrence stage).root.2 =
      GeneratedFiniteThetaPatchAt.generate globalGermOccurrence.root stage :=
  rfl

theorem finiteThetaOccurrence_projects_to_seed (stage : Nat) :
    ((finiteThetaOccurrence stage).map Sigma.fst).map Prod.fst =
      seedOccurrence := by
  rw [finiteThetaOccurrence_projects, globalGermOccurrence_projects]

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
