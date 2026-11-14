import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit.Recovery

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit

open BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock
open scoped InnerProductSpace lp

open private original_R_real_energy rightQuarter from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource

local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "R₀" => burnolDirectRightResolventCLM

abbrev MixedRead := WithLp 2 (BurnolL2 × BurnolL2)

/-- The read uses the current exterior and the physical part of its actual R successor. -/
def mixedObservation (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] MixedRead :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ BurnolL2 BurnolL2).symm.toContinuousLinearMap.comp
    ((O).prod ((P).comp (R₀ c)))

private theorem physical_R_detects (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (physical : P v = v) (gone : P (R₀ c v) = 0) :
    v = 0 := by
  let p := burnolEvenAmbientProjection v
  have read := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left p (R₀ c v)
  change inner ℂ (P v) (P (R₀ c v)) = inner ℂ (P v) (R₀ c v) at read
  rw [physical, gone, inner_zero_right] at read
  have energy := original_R_real_energy c v
  change 2*(inner ℂ v (R₀ c v)).re = -sourceDamping c * ‖R₀ c v‖^2 at energy
  rw [← read, Complex.zero_re, mul_zero] at energy
  have square : ‖R₀ c v‖^2 = 0 :=
    (mul_eq_zero.mp energy.symm).resolve_left (neg_ne_zero.mpr (sourceDamping_pos c).ne')
  have image : R₀ c v = 0 := by
    by_contra live
    exact (pow_ne_zero _ (norm_ne_zero_iff.mpr live)) square
  exact burnolDirectRightResolvent_reflects_zero (c.value/2) (rightQuarter c) v image

/-- The original R energy separates any two whole fields observed at these two slots. -/
theorem mixedObservation_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (mixedObservation c) := by
  intro x y same
  let v := x-y
  have outside : O x = O y := congrArg (fun z : MixedRead => (WithLp.ofLp z).1) same
  have successor : P (R₀ c x) = P (R₀ c y) := congrArg (fun z : MixedRead => (WithLp.ofLp z).2) same
  have outsideZero : O v = 0 := by
    change O (x-y) = 0
    rw [map_sub, outside, sub_self]
  have physical : P v = v := by
    have split := OriginalKCombFullResidualAction.split_complete v
    rwa [outsideZero, add_zero] at split
  have nextZero : P (R₀ c v) = 0 := by
    change P (R₀ c (x-y)) = 0
    rw [map_sub, map_sub, successor, sub_self]
  exact sub_eq_zero.mp (physical_R_detects c v physical nextZero)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ j : Nat, observation.coordinate = -2 * (j+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
variable (depth width start : Nat)
local notation "V" => Orbit.value observation nontrivial half depth width start
local notation "W" => stock observation nontrivial half depth width start

/-- Both slots are read from the actual paid born sequence. -/
def actualMixed (k : Nat) : MixedRead :=
  WithLp.toLp 2 (O (V k), P (V (k+1)))

theorem actual_mixed_stock (k : Nat) :
    mixedObservation c (field (W k)) = actualMixed observation nontrivial half depth width start k := by
  rw [stock_field, actualMixed, actual_direct_R observation nontrivial half depth width start k]
  rfl

/-- The actual physical component is invisible in the current exterior and visible after the original R action. -/
theorem actual_physical_component_detected (k : Nat) :
    O (P (V k)) = 0 ∧ P (R₀ c (P (V k))) ≠ 0 := by
  let p := burnolEvenAmbientProjection (V k)
  have physical : P (P (V k)) = P (V k) := by
    change (burnolEvenAmbientProjection (p : BurnolL2) : BurnolL2) = (p : BurnolL2)
    exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p)
  constructor
  · have split := OriginalKCombFullResidualAction.split_complete (P (V k))
    rw [physical] at split
    exact add_left_cancel (split.trans (add_zero _).symm)
  · intro erased
    exact (actual_gap_and_live observation nontrivial half depth width start k).2
      (physical_R_detects c (P (V k)) physical erased)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.RNext.Orbit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
