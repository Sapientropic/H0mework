import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram

/-! Subordinate same-K source experiment.  The fixed RH root and its next are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountedPa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PaCut
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields
open OriginalKPairedBEulerJunctionSource
open scoped Topology InnerProductSpace
open private forward_reflect from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
open private paired_pair from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
local notation "K" => burnolCompletedMellinRieszVector
local notation "T" => burnolTateReciprocalL2
local notation "D" => burnolMultiplicativeDilation
local notation "A" => sourceAnnulusCut
local notation "V" => sourceVolterraResolvent
local notation "DN" => DualSource.source
local notation "AN" => FiniteForcing.source
local notation "h₀" => Real.log stageZeroSonineQ
local notation "Q" => pairedBurnolMultiplicativeDilation

private theorem annulus_pair (u v : BurnolL2) :
    inner ℂ (A u) v = inner ℂ u (A v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceAnnulusCut_coeFn u, sourceAnnulusCut_coeFn v] with x left right
  rw [left, right]
  by_cases inside : (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4
  · rw [if_pos inside, if_pos inside]
  · rw [if_neg inside, if_neg inside, inner_zero_left, inner_zero_right]

private theorem dilation_pair (t : ℝ) (u v : BurnolL2) :
    inner ℂ u (D t v) = inner ℂ (D (-t) u) v := by
  have source := (D (-t)).inner_map_eq_flip u v
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at source
  exact source.symm

private theorem paired_symmetric (h : ℝ) (u v : BurnolL2) :
    inner ℂ u (Q h v) = inner ℂ (Q h u) v := by
  change inner ℂ u ((1 / 2 : ℂ) • (D h v + D (-h) v)) =
    inner ℂ ((1 / 2 : ℂ) • (D h u + D (-h) u)) v
  rw [inner_smul_right, inner_add_right, inner_smul_left, inner_add_left,
    dilation_pair h, dilation_pair (-h), neg_neg]
  norm_num only [starRingEnd_apply, star_div₀, star_one, star_ofNat]
  ring

private theorem paired_tate (h : ℝ) (u : BurnolL2) : Q h (T u) = T (Q h u) := by
  change (1 / 2 : ℂ) • (D h (T u) + D (-h) (T u)) =
    T ((1 / 2 : ℂ) • (D h u + D (-h) u))
  rw [map_smul, map_add, burnolTateReciprocalL2_dilation_inverse,
    burnolTateReciprocalL2_dilation_inverse]
  simp only [neg_neg]
  module

private theorem counted_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    reflectL2 (countedKernel c zero) = countedKernel c zero := by
  have seed : reflectL2 (T (K c : BurnolL2)) = T (K c : BurnolL2) := by
    rw [← burnolTateReciprocal_reflect, mem_evenL2ClosedFace_iff.mp (K c).property.2]
  have base := actual_counted_kernel_forward c zero
  have reflected := (reflectL2.continuous.tendsto _).comp base
  exact tendsto_nhds_unique (reflected.congr' (Eventually.of_forall (fun N => by
    dsimp only [Function.comp_apply]
    rw [forward_reflect, seed]))) base

/-- The two genuinely moved K-counting feet generate their own annulus input. -/
def jointInput (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) : BurnolL2 :=
  A (Q h (countedKernel c zero))

private theorem jointInput_even (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) :
    reflectL2 (jointInput c zero h) = jointInput c zero h := by
  apply sourceAnnulusCut_even
  change reflectL2 ((1 / 2 : ℂ) • (D h (countedKernel c zero) + D (-h) (countedKernel c zero))) = _
  rw [map_smul, map_add, reflectL2_burnolMultiplicativeDilation,
    reflectL2_burnolMultiplicativeDilation, counted_even c zero]
  rfl

def jointPa (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) : BurnolPaAmbientCarrier :=
  sourceVolterraPhysical c (jointInput c zero h)

/-- Both slots use the literal K and its same-N counting graph. -/
theorem actual_joint_K_source_pair (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) :
    inner ℂ (K c : BurnolL2) (Q h (jointPa c zero h : BurnolL2)) =
      inner ℂ (jointInput c zero h) (V c (jointInput c zero h)) := by
  let sigma := T (burnolMobiusSourceL2 (jointPa c zero h))
  have reverse := actual_volterra_reverse c (jointInput c zero h)
  change Tendsto (fun N : ℕ => DN N sigma) atTop (𝓝 (T (jointPa c zero h : BurnolL2))) at reverse
  have qcontinuous : Continuous (fun u : BurnolL2 => Q h u) := by
    unfold pairedBurnolMultiplicativeDilation
    fun_prop
  have moving := qcontinuous.tendsto _ |>.comp reverse
  have finite (N : ℕ) : DN N (Q h sigma) = Q h (DN N sigma) := by
    change DN N ((1 / 2 : ℂ) • (D h sigma + D (-h) sigma)) = _
    simp only [CountingDual.dual_eq_adjoint, map_smul, map_add]
    rw [← CountingDual.dual_eq_adjoint, ← CountingDual.dual_eq_adjoint,
      dual_dilation, dual_dilation]
    rw [CountingDual.dual_eq_adjoint]
    rfl
  have reverseQ : Tendsto (fun N : ℕ => DN N (Q h sigma)) atTop
      (𝓝 (T (Q h (jointPa c zero h : BurnolL2)))) := by
    rw [← paired_tate h]
    exact moving.congr' (Eventually.of_forall (fun N => (finite N).symm))
  have left := (actual_counted_kernel_forward c zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := Q h sigma))
  have right := (tendsto_const_nhds (x := T (K c : BurnolL2))).inner (𝕜 := ℂ) reverseQ
  have same := left.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N _ _))
  have pair := tendsto_nhds_unique same right
  rw [OriginalRieszFiniteSynthesis.tate_pairing, burnolTateReciprocalL2_involutive] at pair
  rw [← pair, paired_symmetric h]
  have source : sigma = sourceVolterraWindow c (jointInput c zero h) :=
    sourceVolterraPhysical_source c _ (jointInput_even c zero h) (sourceAnnulusCut_idempotent _)
  rw [source]
  change inner ℂ (Q h (countedKernel c zero)) (A (V c (jointInput c zero h))) = _
  rw [← annulus_pair]
  rfl

private theorem volterra_energy (c : BurnolCompletedMellinCoordinate) (u : BurnolL2) :
    -4 * (inner ℂ u (V c u)).re = (2 * c.value.re - 1) * ‖V c u‖ ^ 2 := by
  have right : 1 / 4 < (c.value / 2).re := by rw [Complex.div_re]; norm_num; linarith [c.rightHalf]
  have gram := burnolDirectRightResolvent_gram (c.value / 2) (c.value / 2) right right (T u)
  have coefficient : c.value / 2 + star (c.value / 2) - 1 / 2 = ((c.value.re - 1 / 2 : ℝ) : ℂ) := by
    change c.value / 2 + (starRingEnd ℂ) (c.value / 2) - 1 / 2 = _
    rw [Complex.add_conj]
    norm_num
    ring
  rw [coefficient, inner_self_eq_norm_sq_to_K] at gram
  change inner ℂ (T u) (burnolDirectRightResolvent (c.value / 2) (T u)) +
    (starRingEnd ℂ) (inner ℂ (T u) (burnolDirectRightResolvent (c.value / 2) (T u))) =
      -((c.value.re - 1 / 2 : ℝ) : ℂ) *
        (‖burnolDirectRightResolvent (c.value / 2) (T u)‖ : ℂ) ^ 2 at gram
  rw [Complex.add_conj] at gram
  have real : 2 * (inner ℂ (T u) (burnolDirectRightResolvent (c.value / 2) (T u))).re =
      -(c.value.re - 1 / 2) * ‖burnolDirectRightResolvent (c.value / 2) (T u)‖ ^ 2 := by
    exact_mod_cast gram
  have pair : inner ℂ u (V c u) = inner ℂ (T u) (burnolDirectRightResolvent (c.value / 2) (T u)) := by
    rw [OriginalRieszFiniteSynthesis.tate_pairing]
    rfl
  have norm : ‖V c u‖ = ‖burnolDirectRightResolvent (c.value / 2) (T u)‖ :=
    burnolTateReciprocalValue_norm _
  rw [pair, norm]
  nlinarith only [real]

/-- A signed quadratic reserve generated by the complete original K source. -/
theorem actual_joint_K_source_energy (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) :
    -4 * (inner ℂ (K c : BurnolL2) (Q h (jointPa c zero h : BurnolL2))).re =
      (2 * c.value.re - 1) * ‖V c (jointInput c zero h)‖ ^ 2 := by
  rw [actual_joint_K_source_pair]
  exact volterra_energy c _

/-- The actual fixed theta consumes this same generated Pa state, after both physical feet act. -/
theorem actual_theta_joint_source_energy (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    4 * (inner ℂ (physicalCotest c : BurnolL2) (jointPa c zero h₀ : BurnolL2)).re =
      (2 * c.value.re - 1) * ‖V c (jointInput c zero h₀)‖ ^ 2 := by
  have inside := sourceVolterraPhysical_mem c (jointInput c zero h₀)
  have original := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c zero
  have orthogonal : inner ℂ (K c : BurnolL2) (jointPa c zero h₀ : BurnolL2) = 0 :=
    inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal _ _).mp original _ inside)
  have projected : inner ℂ (burnolEvenAmbientProjection (sourceAction c)) (jointPa c zero h₀) =
      inner ℂ (sourceAction c) (jointPa c zero h₀ : BurnolL2) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (jointPa c zero h₀) (sourceAction c)
  have fixed : inner ℂ (physicalCotest c : BurnolL2) (jointPa c zero h₀ : BurnolL2) =
      -inner ℂ (K c : BurnolL2) (Q h₀ (jointPa c zero h₀ : BurnolL2)) := by
    rw [physicalCotest, Submodule.coe_sub, Submodule.coe_smul, inner_sub_left,
      inner_smul_left, orthogonal, mul_zero, zero_sub]
    rw [paired_pair]
    exact congrArg Neg.neg projected
  rw [fixed, Complex.neg_re]
  linear_combination actual_joint_K_source_energy c zero h₀

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
