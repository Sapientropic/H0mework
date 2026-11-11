import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionXiEscape
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.Source

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open Complex BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCofinalFullBranchFibre
open scoped lp

open private source_left_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private seed_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial

local notation "R" => burnolDirectRightResolventCLM
local notation "T" => sourceCayley
local notation "δ" => sourceDamping
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem damping_ne (c : BurnolCompletedMellinCoordinate) : (δ c : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'

private def delayedRaw (a : ℓ²(Nat, ℂ)) : Nat → ℂ
  | 0 => 0
  | n+1 => a n

private def delayed (a : ℓ²(Nat, ℂ)) : ℓ²(Nat, ℂ) :=
  ⟨delayedRaw a, memℓp_gen ((summable_nat_add_iff 1).mp ((lp.memℓp a).summable (by norm_num)))⟩

/-- The complete coefficient update is calculated from the current stock by a neighbor difference. -/
def nextCoefficients (c : BurnolCompletedMellinCoordinate) (a : ℓ²(Nat, ℂ)) : ℓ²(Nat, ℂ) :=
  (δ c : ℂ)⁻¹ • (delayed a - a)

theorem nextCoefficients_zero (c : BurnolCompletedMellinCoordinate) (a : ℓ²(Nat, ℂ)) :
    (δ c : ℂ) * nextCoefficients c a 0 = -a 0 := by
  change (δ c : ℂ) * ((δ c : ℂ)⁻¹ * (0-a 0)) = _
  rw [← mul_assoc, mul_inv_cancel₀ (damping_ne c), one_mul, zero_sub]

theorem nextCoefficients_succ (c : BurnolCompletedMellinCoordinate) (a : ℓ²(Nat, ℂ)) (n : Nat) :
    (δ c : ℂ) * nextCoefficients c a (n+1) = a n - a (n+1) := by
  change (δ c : ℂ) * ((δ c : ℂ)⁻¹ * (a n-a (n+1))) = _
  rw [← mul_assoc, mul_inv_cancel₀ (damping_ne c), one_mul]

/-- The inverse reads exactly one finite prefix for each original coordinate. -/
def inversePrefix (c : BurnolCompletedMellinCoordinate) (b : ℓ²(Nat, ℂ)) (n : Nat) : ℂ :=
  -(δ c : ℂ) * ∑ i ∈ Finset.range (n+1), b i

theorem nextCoefficients_fibre (c : BurnolCompletedMellinCoordinate) (a b : ℓ²(Nat, ℂ)) :
    nextCoefficients c a = b ↔ ∀ n, a n = inversePrefix c b n := by
  constructor
  · intro action n
    induction n with
    | zero =>
      have head := nextCoefficients_zero c a
      rw [action] at head
      change a 0 = -(δ c : ℂ) * ∑ i ∈ Finset.range 1, b i
      rw [Finset.sum_range_one]
      linear_combination head
    | succ n previous =>
      have step := nextCoefficients_succ c a n
      rw [action, previous] at step
      unfold inversePrefix
      rw [Finset.sum_range_succ]
      unfold inversePrefix at step
      linear_combination step
  · intro inventory
    apply lp.ext
    funext n
    apply mul_left_cancel₀ (damping_ne c)
    cases n with
    | zero =>
      rw [nextCoefficients_zero, inventory, inversePrefix, Finset.sum_range_one]
      ring
    | succ n =>
      rw [nextCoefficients_succ, inventory n, inventory (n+1), inversePrefix, inversePrefix,
        Finset.sum_range_succ (n := n+1)]
      ring

/-- A complete inverse exists exactly when the generated prefixes are in the original Hilbert stock. -/
theorem nextCoefficients_inverse_iff (c : BurnolCompletedMellinCoordinate) (b : ℓ²(Nat, ℂ)) :
    (∃! a, nextCoefficients c a = b) ↔ Memℓp (inversePrefix c b) 2 := by
  constructor
  · rintro ⟨a, step, _⟩
    rw [← funext ((nextCoefficients_fibre c a b).1 step)]
    exact lp.memℓp a
  · intro paid
    let a : ℓ²(Nat, ℂ) := ⟨inversePrefix c b, paid⟩
    exact ⟨a, (nextCoefficients_fibre c a b).2 (fun _ => rfl),
      fun other action => lp.ext (funext ((nextCoefficients_fibre c other b).1 action))⟩

private theorem actual_next_stock (c : BurnolCompletedMellinCoordinate) (x y : PositionField)
    (performed : (y : BurnolL2) = R c x) :
    nextCoefficients c ((basis c).repr x) = (basis c).repr y := by
  let next := x + (δ c : ℂ) • y
  have next_raw : (next : BurnolL2) = T c x := by
    change (x : BurnolL2)+(δ c : ℂ) • (y : BurnolL2) = _
    rw [sourceCayley_apply, performed]
    rfl
  have row (n : Nat) : (basis c).repr next n = (basis c).repr x n +
      (δ c : ℂ) * (basis c).repr y n := by
    dsimp only [next]
    rw [map_add, map_smul]
    rfl
  have head : (basis c).repr next 0 = 0 := by
    rw [actual_coefficient, next_raw, pow_zero, one_apply_eq_self,
      actual_gap_cayley_conjugate_zero c _ x.property.1, mul_zero]
  have tail (n : Nat) : (basis c).repr next (n+1) = (basis c).repr x n := by
    rw [actual_coefficient, actual_coefficient, next_raw, pow_succ, mul_apply_eq_comp, source_left_inverse]
  apply lp.ext
  funext n
  apply mul_left_cancel₀ (damping_ne c)
  cases n with
  | zero =>
    rw [nextCoefficients_zero]
    have equation := row 0
    rw [head] at equation
    linear_combination equation
  | succ n =>
    rw [nextCoefficients_succ]
    have equation := row (n+1)
    rw [tail] at equation
    linear_combination equation

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => D.raw observation nontrivial half depth
local notation "input" => D.input observation nontrivial half depth
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate

private def current (ordinal : Nat) : PositionField :=
  ⟨raw ordinal, OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal,
    mem_evenL2ClosedFace_iff.mpr (by
      rw [CofinalCanonicalSourceMaterial.actual_raw_field observation nontrivial half]
      exact CofinalCanonicalSourceMaterial.actual_iterate_even c _ seed_even _)⟩

/-- Read the whole inventory from the same literal Division frame. -/
def coefficientsAt (ordinal : Nat) : ℓ²(Nat, ℂ) :=
  (basis c).repr (current observation nontrivial half depth ordinal)

local notation "inventory" => coefficientsAt observation nontrivial half depth

theorem actual_division_coefficient_step (ordinal : Nat) :
    nextCoefficients c (inventory ordinal) = inventory (ordinal+1) :=
  actual_next_stock c _ _ ((OriginalKCombFirstFullSourceDynamics.raw_successor observation
    nontrivial half depth ordinal).trans (by rw [OriginalKCombCofinalRAction.original_R_direct]; rfl))

theorem actual_division_first_coefficient (ordinal : Nat) :
    (∀ n < m, inventory ordinal n = 0) ∧
      inventory ordinal m = normalization c * DivisionXiEscape.divisionLeading observation half ordinal 0 ∧
      inventory ordinal m ≠ 0 := by
  obtain ⟨zero, first, live, _, _⟩ := DivisionXiEscape.actual_division_exact_adjoint_escape
    observation nontrivial half depth ordinal
  refine ⟨fun n within => ?_, ?_, ?_⟩
  · rw [coefficientsAt, actual_coefficient, show (current observation nontrivial half depth ordinal : BurnolL2) =
        raw ordinal from rfl, zero n within, mul_zero]
  · rw [coefficientsAt, actual_coefficient, show (current observation nontrivial half depth ordinal : BurnolL2) =
        raw ordinal from rfl, first]
  · rw [coefficientsAt, actual_coefficient, show (current observation nontrivial half depth ordinal : BurnolL2) =
        raw ordinal from rfl, first]
    exact mul_ne_zero (normalization_ne_zero c) live

/-- Apply the original physical and exterior projections after whole-field synthesis. -/
def splitInventory (coord : BurnolCompletedMellinCoordinate) (a : ℓ²(Nat, ℂ)) : SourcePair :=
  let whole : BurnolL2 := (basis coord).repr.symm a
  (P.physicalProjection whole, P.physicalRemainder whole)

theorem actual_division_inventory_synthesis (ordinal : Nat) :
    HasSum (fun n => inventory ordinal n • ((T c)^n) (positionHead c)) (raw ordinal) := by
  have paid := actual_synthesis c (inventory ordinal)
  rwa [coefficientsAt, LinearIsometryEquiv.symm_apply_apply] at paid

theorem actual_division_inventory_readback (ordinal : Nat) :
    splitInventory c (inventory ordinal) = input ordinal := by
  unfold splitInventory coefficientsAt
  rw [LinearIsometryEquiv.symm_apply_apply]
  change (P.physicalProjection (raw ordinal), P.physicalRemainder (raw ordinal)) = input ordinal
  cases ordinal with
  | zero => rw [OriginalKCombFirstFullSourceDynamics.first_pair, OriginalKCombFirstFullSourceDynamics.raw_origin]
  | succ n => rw [OriginalKCombFirstFullSourceDynamics.next_pair, OriginalKCombFirstFullSourceDynamics.raw_successor]

/-- The coefficient update writes the two complete original branches at the literal next occurrence. -/
theorem actual_division_inventory_write (ordinal : Nat) :
    let a := inventory ordinal;
    let generated := nextCoefficients c a;
    splitInventory c a = input ordinal ∧
      splitInventory c generated = input (ordinal+1) ∧
      sourceStep observation nontrivial half (splitInventory c a) = splitInventory c generated := by
  dsimp only
  rw [actual_division_coefficient_step, actual_division_inventory_readback,
    actual_division_inventory_readback, actual_source_step]
  exact ⟨rfl,rfl,rfl⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
