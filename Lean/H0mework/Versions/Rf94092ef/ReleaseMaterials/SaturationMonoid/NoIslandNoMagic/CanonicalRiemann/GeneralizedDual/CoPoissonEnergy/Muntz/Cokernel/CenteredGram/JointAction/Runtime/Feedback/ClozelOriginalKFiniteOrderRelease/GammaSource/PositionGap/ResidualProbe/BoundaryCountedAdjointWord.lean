import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedDivisionTrace

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedAdjointWord

open BurnolPhysicalState Filter
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace Topology BigOperators

open private phase scaleMass from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedMassMesh
open private tailStart damping from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedContinuousInverse
open private scale loss gap from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedWord
open private tail from H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedFiniteFlow
open private right_quarter from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "U" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "mirror" => fourierL2.conjStarAlgEquiv
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "I" => BoundaryCountedContinuousInverse.index
local notation "R" => burnolDirectRightResolventCLM
local notation "W" => BoundaryCountedDivision.commonWord
local notation "M" => BoundaryCountedDivision.sharedLength

private theorem star_dilation (h : ℝ) :
    star ((U h).toContinuousLinearEquiv.toContinuousLinearMap : End) =
      mirror ((U h).toContinuousLinearEquiv.toContinuousLinearMap : End) := by
  apply ContinuousLinearMap.ext
  intro value
  change star ((U h : BurnolL2 ≃ₗᵢ[ℂ] BurnolL2) : End) value =
    mirror ((U h).toContinuousLinearEquiv.toContinuousLinearMap : End) value
  rw [LinearIsometryEquiv.star_eq_symm, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change (U h).symm value = F (U h ((F).symm value))
  rw [fourierL2_burnolMultiplicativeDilation_inverse, (F).apply_symm_apply]

private theorem star_mesh (N mesh : Nat) :
    star (BoundaryCountedMassMesh.meshTail N mesh) = mirror (BoundaryCountedMassMesh.meshTail N mesh) := by
  let a : ℂ := ((N : ℝ) : ℂ)
  let b : ℂ := (scaleMass N : ℂ)
  let c : ℂ := (((mesh : ℝ)⁻¹ : ℝ) : ℂ)
  let d (j : Nat) : End := (U (-phase N (SourceGeneratedUnitMesh.node mesh (j+1)))).toContinuousLinearEquiv.toContinuousLinearMap
  change star (a • b • c • ∑ j ∈ Finset.range mesh, d j) =
    mirror (a • b • c • ∑ j ∈ Finset.range mesh, d j)
  have aReal : star a = a := Complex.conj_ofReal _
  have bReal : star b = b := Complex.conj_ofReal _
  have cReal : star c = c := Complex.conj_ofReal _
  have localAction (j : Nat) : star (d j) = mirror (d j) := star_dilation _
  simp only [star_smul, aReal, bReal, cReal, star_sum, map_smul, map_sum, localAction]

private theorem conjugate_index (coordinate : ℂ) (n : Nat) : I (star coordinate) n = I coordinate n := by
  simp only [BoundaryCountedContinuousInverse.index, tailStart, Complex.star_def, Complex.conj_re]

private theorem conjugate_scale (coordinate : ℂ) (n : Nat) :
    star (scale coordinate n) = scale (star coordinate) n := by
  rw [scale, scale, conjugate_index, damping, damping, star_sub, star_add, star_natCast, star_div₀, star_one, star_ofNat]

private theorem conjugate_loss (coordinate : ℂ) (n : Nat) :
    loss (star coordinate) n = loss coordinate n := by
  rw [loss, loss, gap, gap, show (star coordinate).re = coordinate.re from Complex.conj_re _,
    ← conjugate_scale, Complex.star_def, Complex.norm_conj]

private theorem star_relative (coordinate : ℂ) (n mesh : Nat) :
    star (SourceGeneratedFiniteInverseWord.relative (scale coordinate n) (tail coordinate n mesh)) =
      mirror (SourceGeneratedFiniteInverseWord.relative (scale (star coordinate) n) (tail (star coordinate) n mesh)) := by
  unfold SourceGeneratedFiniteInverseWord.relative
  rw [star_smul, star_inv₀, conjugate_scale, map_smul, tail, tail, conjugate_index, star_mesh]

private theorem star_word (coordinate : ℂ) (n mesh length : Nat) :
    star (BoundaryCountedFiniteFlow.word coordinate n mesh length) =
      mirror (BoundaryCountedFiniteFlow.word (star coordinate) n mesh length) := by
  unfold BoundaryCountedFiniteFlow.word SourceGeneratedFiniteInverseWord.word
  simp only [star_smul, star_inv₀, conjugate_scale, star_sum, star_pow, star_relative, map_smul, map_sum, map_pow]

private theorem conjugate_parameter (coordinate : BurnolCompletedMellinCoordinate) :
    (C coordinate).value/2 = star (coordinate.value/2) := by
  change star coordinate.value/2 = _
  rw [star_div₀, star_ofNat]

private theorem conjugate_length (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    M (C coordinate) n = M coordinate n := by
  unfold BoundaryCountedDivision.sharedLength
  rw [conjugate_parameter, conjugate_loss]

/-- The actual reverse word is the exact adjoint on the original whole carrier. -/
theorem adjoint_source (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) :
    (W coordinate n).adjoint = mirror (W (C coordinate) n) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, BoundaryCountedDivision.commonWord,
    BoundaryCountedDivision.commonWord, star_neg, map_neg, star_word, conjugate_parameter, conjugate_length]

private theorem original_adjoint_source (coordinate : BurnolCompletedMellinCoordinate) :
    (R coordinate).adjoint = mirror (R (C coordinate)) := by
  apply ContinuousLinearMap.ext
  intro value
  apply ext_inner_right ℂ
  intro test
  rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  let z := coordinate.value/2
  have forward := FiniteMobiusResolventFlux.fourier_R ((C coordinate).value/2)
    (right_quarter (C coordinate)) ((F).symm value)
  rw [(F).apply_symm_apply, conjugate_parameter coordinate] at forward
  have actual := OriginalKCompactAdjointRSource.actual_original_R_adjoint z (right_quarter coordinate) value test
  change inner ℂ value (burnolDirectRightResolvent z test) =
    inner ℂ (F (burnolDirectRightResolvent ((C coordinate).value/2) ((F).symm value))) test
  rw [actual, conjugate_parameter coordinate, forward]

theorem adjoint_tendsto (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    Tendsto (fun n : Nat => (W coordinate n).adjoint value) atTop (𝓝 ((R coordinate).adjoint value)) := by
  rw [original_adjoint_source]
  have h := ((F).continuous.tendsto _).comp (BoundaryCountedDivision.common_tendsto (C coordinate) ((F).symm value))
  refine h.congr' (Eventually.of_forall (fun n => ?_))
  change F (W (C coordinate) n ((F).symm value)) = (W coordinate n).adjoint value
  rw [adjoint_source, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

theorem adjoint_frequency (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) (value : BurnolL2)
    (inside : (F).symm value ∈ locallyConstantFace burnolUnscaledCommonGapRadius) :
    (F).symm ((W coordinate n).adjoint value) ∈ locallyConstantFace burnolUnscaledCommonGapRadius := by
  rw [adjoint_source, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, (F).symm_apply_apply]
  exact BoundaryCountedDivision.common_gap (C coordinate) n _ inside

private def finiteCayley (coordinate : BurnolCompletedMellinCoordinate) (n : Nat) : End :=
  1 + (sourceDamping coordinate : ℂ) • W coordinate n

private theorem adjoint_cayley_tendsto (coordinate : BurnolCompletedMellinCoordinate) (test : BurnolL2) :
    Tendsto (fun n : Nat => (finiteCayley coordinate n).adjoint test) atTop
      (𝓝 ((sourceCayley coordinate).adjoint test)) := by
  have adjoint (op : End) :
      ((1 : End) + (sourceDamping coordinate : ℂ) • op).adjoint test =
        test + (sourceDamping coordinate : ℂ) • op.adjoint test := by
    change star ((1 : End)+(sourceDamping coordinate : ℂ) • op) test = _
    rw [star_add, star_one, star_smul, show star (sourceDamping coordinate : ℂ) =
      (sourceDamping coordinate : ℂ) from Complex.conj_ofReal _]
    rfl
  change Tendsto (fun n : Nat => (((1 : End)+(sourceDamping coordinate : ℂ) • W coordinate n).adjoint) test)
    atTop (𝓝 ((((1 : End)+(sourceDamping coordinate : ℂ) • R coordinate).adjoint) test))
  simp only [adjoint]
  exact (tendsto_const_nhds (x := test)).add ((adjoint_tendsto coordinate test).const_smul _)

local notation "Q" => burnolQuarterRestriction
local notation "Z" => OriginalRieszSource.Constructor.zeroMean
local notation "S" => HilbertInventory.PositionField

private def finiteQuarterRead (anchor : BurnolCompletedMellinCoordinate) (value : S)
    (test : BurnolPaAmbientCarrier) (n : Nat) : ℂ :=
  inner ℂ (Z (Q ((finiteCayley anchor n).adjoint (test : BurnolL2)))) (BoundaryQuarterRelease.release anchor value)

private theorem quarter_tendsto (anchor : BurnolCompletedMellinCoordinate) (value : S)
    (test : BurnolPaAmbientCarrier) :
    Tendsto (finiteQuarterRead anchor value test) atTop (𝓝 (BoundaryQuarterRelease.quarterPrice anchor value test)) := by
  have linear : Continuous (fun w : BurnolL2 => Z (Q w)) := (Z).continuous.comp (Q).continuous
  have observe : Continuous (fun w : BurnolL2 => inner ℂ (Z (Q w)) (BoundaryQuarterRelease.release anchor value)) :=
    linear.inner continuous_const
  exact (observe.tendsto _).comp (adjoint_cayley_tendsto anchor (test : BurnolL2))

local notation "P" => burnolEvenAmbientProjectionEndomorphism

private def projectedMeans (value : BurnolL2) : ℂ × ℂ :=
  (burnolQuarterMeanCoefficient (Q (P value)),
   burnolQuarterMeanCoefficient (Q (F (P value))))

private theorem projectedMeans_continuous : Continuous projectedMeans := by
  have mean : Continuous burnolQuarterMeanCoefficient := by
    unfold burnolQuarterMeanCoefficient
    exact (continuous_const.inner continuous_id).div_const _
  have position := mean.comp ((Q).continuous.comp (P).continuous)
  have frequency := mean.comp ((Q).continuous.comp ((F).continuous.comp (P).continuous))
  exact position.prodMk frequency

/-- The two original uncentered means read the same finite forward release. -/
theorem release_means (anchor : BurnolCompletedMellinCoordinate) (value : S) :
    let release := burnolQuarterZeroExtension (BoundaryQuarterRelease.release anchor value : BurnolQuarterIntervalL2)
    Tendsto (fun n : Nat => projectedMeans (finiteCayley anchor n release)) atTop
      (𝓝 (projectedMeans (BoundaryAdjointDefect.defect anchor value))) := by
  let release := burnolQuarterZeroExtension (BoundaryQuarterRelease.release anchor value : BurnolQuarterIntervalL2)
  have forward := (tendsto_const_nhds (x := release)).add
    ((BoundaryCountedDivision.common_tendsto anchor release).const_smul (sourceDamping anchor : ℂ))
  have original : release + (sourceDamping anchor : ℂ) • R anchor release = BoundaryAdjointDefect.defect anchor value := by
    rw [BoundaryQuarterRelease.defect_release, BoundaryQuarterRelease.raw, sourceCayley_apply]
    rfl
  rw [original] at forward
  exact (projectedMeans_continuous.tendsto _).comp forward

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "slot" => BoundaryAdjointDefect.nativeSlot observation nontrivial half depth

/-- The original fixed B cotest reads the true reverse finite action at its original Xi slot. -/
theorem actual_fixed_B (ordinal : Nat) :
    Tendsto (finiteQuarterRead (C c) (slot ordinal) (BoundaryAdjointDefect.B.physicalCotest c)) atTop
      (𝓝 (BoundaryAdjointDefect.coefficient (C c) (slot ordinal) *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual))) := by
  rw [← BoundaryQuarterRelease.actual_fixed_quarter observation nontrivial half depth ordinal]
  exact quarter_tendsto _ _ _

local instance pairedPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The paired first resolvent of the literal comb seed retains its original B(0) class. -/
theorem actual_B_zero :
    let seed := (burnolPaCombApproximation 0 : BurnolL2)
    let finite := fun n : Nat => (1/2 : ℂ) • (W c n seed + F (W c n seed))
    let target := burnolPaCombPairedPhysicalResponse observation nontrivial half.down 0
    Tendsto finite atTop (𝓝 (target : BurnolL2)) ∧
    Tendsto (fun n : Nat => OriginalKCombCofinalPaAction.Q (finite n)) atTop
      (𝓝 (OriginalKCombCofinalPaAction.Q (target : BurnolL2))) ∧
    OriginalKCombCofinalPaAction.Q (target : BurnolL2) ≠ 0 := by
  let seed := (burnolPaCombApproximation 0 : BurnolL2)
  let target := burnolPaCombPairedPhysicalResponse observation nontrivial half.down 0
  have first := BoundaryCountedDivision.common_tendsto c seed
  have second := ((F).continuous.tendsto _).comp first
  have paid := (first.add second).const_smul (1/2 : ℂ)
  have original : (1/2 : ℂ) • (R c seed+F (R c seed)) = (target : BurnolL2) := rfl
  rw [original] at paid
  have live : OriginalKCombCofinalPaAction.Q (target : BurnolL2) ≠ 0 := by
    change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolEvenAmbientProjection (target : BurnolL2)) ≠ 0
    have projected : burnolEvenAmbientProjection (target : BurnolL2) = target :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
    rw [projected]
    exact burnolPaCombPairedPhysicalResponse_Q_ne_zero observation nontrivial half.down 0
  exact ⟨paid,(OriginalKCombCofinalPaAction.Q.continuous.tendsto _).comp paid,live⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryCountedAdjointWord
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
