import H0mework.Arithmetic.RiemannSource.FiniteEulerNonvanishingAtGeneratedZero

/-!
# Source-owned finite Clozel--Tate jump

The rational Tate kernel has finite prefix
`x^(s-1) * ∑_{n ≤ x} n^(-s) + 1/(s-1)`.  This module keeps only its
finite source law: at every generated magnitude the scaled jump is `1`, and
the pole correction contributes `-1`.  The resulting cell is generated as a
dependent face of the existing zero-observation occurrence.

No Fourier relation or vanishing claim is stored here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex
open RootedAccountedUnfolding
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

def actualClozelFinitePrefix (s : ℂ) (stage : Nat) : ℂ :=
  ∑ index ∈ Finset.range (stage + 1),
    ((index + 1 : Nat) : ℂ) ^ (-s)

theorem actualClozelFinitePrefix_succ (s : ℂ) (stage : Nat) :
    actualClozelFinitePrefix s (stage + 1) =
      actualClozelFinitePrefix s stage +
        ((stage + 2 : Nat) : ℂ) ^ (-s) := by
  rw [actualClozelFinitePrefix, actualClozelFinitePrefix,
    Finset.sum_range_succ]

@[simp] theorem actualClozelFinitePrefix_stageZero (s : ℂ) :
    actualClozelFinitePrefix s 0 = 1 := by
  simp [actualClozelFinitePrefix]

@[simp] theorem generatedRiemannThetaShell_magnitude
    (owner : GlobalGermOwner) (stage : Nat) :
    (generatedRiemannThetaShell owner stage).magnitude = stage + 1 := by
  simp [generatedRiemannThetaShell, generatedRiemannThetaPatch,
    GeneratedFiniteThetaPatchAt.generate,
    GeneratedIntegerShellAt.generate_magnitude]

def actualClozelWeightedJump
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) : ℂ :=
  let magnitude := (generatedRiemannThetaShell owner stage).magnitude
  (magnitude : ℂ) ^ (s - 1) * (magnitude : ℂ) ^ (-s)

theorem actualClozelWeightedJump_eq_inv
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) :
    actualClozelWeightedJump owner s stage =
      ((generatedRiemannThetaShell owner stage).magnitude : ℂ)⁻¹ := by
  have magnitudePositive :
      0 < (generatedRiemannThetaShell owner stage).magnitude := by
    rw [generatedRiemannThetaShell_magnitude]
    omega
  have magnitudeNe :
      ((generatedRiemannThetaShell owner stage).magnitude : ℂ) ≠ 0 := by
    exact_mod_cast magnitudePositive.ne'
  unfold actualClozelWeightedJump
  rw [← Complex.cpow_add _ _ magnitudeNe]
  rw [show s - 1 + -s = (-1 : ℂ) by ring,
    Complex.cpow_neg_one]

theorem actualClozel_scaledJump_eq_one
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) :
    ((generatedRiemannThetaShell owner stage).magnitude : ℂ) *
        actualClozelWeightedJump owner s stage = 1 := by
  rw [actualClozelWeightedJump_eq_inv]
  exact mul_inv_cancel₀ <| by
    exact_mod_cast (show 0 <
      (generatedRiemannThetaShell owner stage).magnitude by
        rw [generatedRiemannThetaShell_magnitude]
        omega).ne'

def clozelPoleCorrection (s : ℂ) : ℂ :=
  1 / (s - 1)

theorem clozelPoleCorrection_shiftedScaling_eq_negOne
    (s : ℂ) (notPole : s ≠ 1) :
    (1 - s) * clozelPoleCorrection s = -1 := by
  unfold clozelPoleCorrection
  field_simp [sub_ne_zero.mpr notPole]
  ring

def finiteClozelTateSourceCell
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat) : ℂ × ℂ :=
  (((generatedRiemannThetaShell owner stage).magnitude : ℂ) *
      actualClozelWeightedJump owner s stage,
    (1 - s) * clozelPoleCorrection s)

theorem finiteClozelTateSourceCell_eq_unit_negOne
    (owner : GlobalGermOwner) (s : ℂ) (stage : Nat)
    (notPole : s ≠ 1) :
    finiteClozelTateSourceCell owner s stage = (1, -1) := by
  apply Prod.ext
  · exact actualClozel_scaledJump_eq_one owner s stage
  · exact clozelPoleCorrection_shiftedScaling_eq_negOne s notPole

structure GeneratedClozelFiniteJumpAt
    (payload : GeneratedZeroObservationPayload) (stage : Nat) : Type 5 where
  private mk ::
  thetaPatch : GeneratedFiniteThetaPatchAt payload.1.1
  thetaPatch_eq :
    thetaPatch = GeneratedFiniteThetaPatchAt.generate payload.1.1 stage
  cell : ℂ × ℂ
  cell_eq : cell = finiteClozelTateSourceCell
    payload.1.1 payload.2.coordinate stage

namespace GeneratedClozelFiniteJumpAt

def generate (payload : GeneratedZeroObservationPayload) (stage : Nat) :
    GeneratedClozelFiniteJumpAt payload stage where
  thetaPatch := GeneratedFiniteThetaPatchAt.generate payload.1.1 stage
  thetaPatch_eq := rfl
  cell := finiteClozelTateSourceCell
    payload.1.1 payload.2.coordinate stage
  cell_eq := rfl

@[simp] theorem generate_cell
    (payload : GeneratedZeroObservationPayload) (stage : Nat) :
    (generate payload stage).cell = (1, -1) :=
  finiteClozelTateSourceCell_eq_unit_negOne
    payload.1.1 payload.2.coordinate stage payload.2.coordinate_ne_one

end GeneratedClozelFiniteJumpAt

abbrev ClozelFiniteJumpPayloadAt (stage : Nat) :=
  Σ payload : GeneratedZeroObservationPayload,
    GeneratedClozelFiniteJumpAt payload stage

def zeroOwnedClozelFiniteJumpOccurrence
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    RootedAccountedUnfolding (ClozelFiniteJumpPayloadAt stage) :=
  (zeroObservationReadoutOccurrence observation).map fun payload =>
    ⟨payload, GeneratedClozelFiniteJumpAt.generate payload stage⟩

theorem zeroOwnedClozelFiniteJumpOccurrence_projects
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (zeroOwnedClozelFiniteJumpOccurrence observation stage).map Sigma.fst =
      zeroObservationReadoutOccurrence observation := by
  rw [zeroOwnedClozelFiniteJumpOccurrence,
    RootedAccountedUnfolding.map_map]
  change (zeroObservationReadoutOccurrence observation).map id = _
  exact RootedAccountedUnfolding.map_id _

theorem zeroOwnedClozelFiniteJumpOccurrence_projects_to_seed
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    ((((zeroOwnedClozelFiniteJumpOccurrence observation stage).map
        Sigma.fst).map Sigma.fst).map Sigma.fst).map Prod.fst =
      CanonicalUnitArithmeticFactorizationEulerDependentDiagram.seedOccurrence := by
  rw [zeroOwnedClozelFiniteJumpOccurrence_projects,
    zeroObservationReadoutOccurrence_projects,
    generatedRiemannAnalyticContinuationOccurrence_projects,
    globalGermOccurrence_projects]

@[simp] theorem zeroOwnedClozelFiniteJumpOccurrence_root_cell
    (observation : GeneratedRiemannZeroObservation) (stage : Nat) :
    (zeroOwnedClozelFiniteJumpOccurrence observation stage).root.2.cell =
      (1, -1) :=
  GeneratedClozelFiniteJumpAt.generate_cell _ _

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
