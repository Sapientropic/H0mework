import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.HankelCotests

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open BurnolPhysicalState Filter OriginalKCofinalFullBranchFibre
open scoped InnerProductSpace lp Topology

open private next_field from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

local notation "Seq" => ℓ²(Nat, ℂ)
local notation "R" => burnolDirectRightResolventCLM
local notation "P₀" => OriginalKCombPhysicalAction.physicalProjection
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "F" => fourierL2
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "M" => burnolAmbientCompletedMellinEvaluator

private def finiteHeadData (c : BurnolCompletedMellinCoordinate) (n : Nat) (heads : Nat → ℂ) :
    Gram.Coordinates (Fin n) :=
  WithLp.toLp 2 fun i => waveFromHeads c heads i 0

private theorem cotest_data_compatible (c : BurnolCompletedMellinCoordinate) (n : Nat)
    (data : Gram.Coordinates (Fin n)) : Gram.Compatible (Gram.gram (finiteCotests c n)) data := by
  intro weight silent
  rw [actual_cotest_gram_faithful c n weight silent, inner_zero_left]

/-- The actual finite Gram image inverse consumes just the retained scalar prefix. -/
def finiteHeadInverse (c : BurnolCompletedMellinCoordinate) (n : Nat) (heads : Nat → ℂ) : Seq :=
  let source := finiteCotests c n
  let data := finiteHeadData c n heads
  Gram.sourceEffect (Gram.gram source) (Matrix.isHermitian_gram ℂ source)
    data (cotest_data_compatible c n data) (Gram.synthesis source) (Gram.kernel_synthesis source)

theorem finiteHeadInverse_prefix (c : BurnolCompletedMellinCoordinate) (n : Nat)
    (left right : Nat → ℂ) (same : ∀ k < n, left k = right k) :
    finiteHeadInverse c n left = finiteHeadInverse c n right := by
  have data : finiteHeadData c n left = finiteHeadData c n right := by
    ext i
    exact waveFromHeads_prefix c left right i 0
      (fun k before => same k (by omega))
  unfold finiteHeadInverse
  dsimp only
  rw [data]

/-- The finite calculation is the orthogonal readback in the corresponding actual cotests. -/
theorem finiteHeadInverse_projection (c : BurnolCompletedMellinCoordinate) (n : Nat) (a : Seq) :
    finiteHeadInverse c n (fourierHeadHistory c a) = (Gram.sourceSpan (finiteCotests c n)).starProjection a := by
  have data : finiteHeadData c n (fourierHeadHistory c a) = Gram.rhs (finiteCotests c n) a := by
    ext i
    change waveFromHeads c (fourierHeadHistory c a) (i : Nat) 0 = inner ℂ (hankelCotest c i) a
    rw [actual_wave_from_heads, Function.iterate_zero, id_eq, actual_hankel_cotest]
  rw [← Gram.predictable_readback]
  unfold finiteHeadInverse
  dsimp only
  rw [data]
  rfl

private theorem cotest_mem (c : BurnolCompletedMellinCoordinate) (n : Nat) (i : Fin n) :
    hankelCotest c i ∈ Gram.sourceSpan (finiteCotests c n) := by
  let unit : Gram.Coordinates (Fin n) := PiLp.single 2 i (1 : ℂ)
  refine ⟨unit, ?_⟩
  change ∑ j, unit j • hankelCotest c j = hankelCotest c i
  rw [Finset.sum_eq_single i]
  · simp [unit]
  · intro j _ distinct
    simp only [unit, PiLp.single_apply, if_neg distinct, zero_smul]
  · exact fun absent => (absent (Finset.mem_univ _)).elim

private theorem cotest_span (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    Gram.sourceSpan (finiteCotests c n) = Submodule.span ℂ (Set.range (finiteCotests c n)) := by
  apply le_antisymm
  · rintro _ ⟨weights, rfl⟩
    change ∑ i, weights i • finiteCotests c n i ∈ _
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact cotest_mem c n i

private theorem cotest_dense (c : BurnolCompletedMellinCoordinate) :
    (⨆ n : Nat, Gram.sourceSpan (finiteCotests c n)).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  refine le_antisymm (fun a ortho => ?_) bot_le
  rw [Submodule.mem_bot]
  apply hankel_injective c
  rw [map_zero]
  apply lp.ext
  funext i
  have member : hankelCotest c i ∈ ⨆ n : Nat, Gram.sourceSpan (finiteCotests c n) :=
    le_iSup (fun n => Gram.sourceSpan (finiteCotests c n)) (i+1) (cotest_mem c (i+1) ⟨i,Nat.lt_succ_self _⟩)
  have silent := (Submodule.mem_orthogonal _ _).mp ortho _ member
  rwa [actual_hankel_cotest] at silent

/-- Every original field is the norm limit of the finite source Gram reconstructions. -/
theorem finiteHeadInverse_tendsto (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    Tendsto (fun n => finiteHeadInverse c n (fourierHeadHistory c a)) atTop (𝓝 a) := by
  have grows : Monotone (fun n => Gram.sourceSpan (finiteCotests c n)) := by
    intro i j le
    change Gram.sourceSpan (finiteCotests c i) ≤ Gram.sourceSpan (finiteCotests c j)
    rw [cotest_span, cotest_span]
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨Fin.castLE le k,rfl⟩
  simpa only [finiteHeadInverse_projection] using
    (Submodule.starProjection_tendsto_self (fun n => Gram.sourceSpan (finiteCotests c n)) grows a
      (le_of_eq (cotest_dense c).symm))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => D.raw observation nontrivial half depth
local notation "stock" => coefficientsAt observation nontrivial half depth
local notation "input" => D.input observation nontrivial half depth

/-- Finite literal source histories recover both complete branch pairs in norm. -/
theorem actual_division_finite_head_recovery (ordinal : Nat) :
    let heads := fun time => normalization (d coord) * M coord (F (raw (ordinal+time)));
    Tendsto (fun n => splitInventory coord (finiteHeadInverse coord n heads)) atTop (𝓝 (input ordinal)) ∧
    Tendsto (fun n => splitInventory coord (nextCoefficients coord (finiteHeadInverse coord n heads)))
      atTop (𝓝 (input (ordinal+1))) := by
  let heads := fun time => normalization (d coord) * M coord (F (raw (ordinal+time)))
  have history : fourierHeadHistory coord (stock ordinal) = heads :=
    funext (actual_division_head_history observation nontrivial half depth ordinal)
  have recovered := finiteHeadInverse_tendsto coord (stock ordinal)
  rw [history] at recovered
  have synth : Continuous (fun a : Seq => ((basis coord).repr.symm a : BurnolL2)) :=
    PositionField.subtypeL.continuous.comp (basis coord).repr.symm.continuous
  have next : Continuous (fun a : Seq => ((basis coord).repr.symm (nextCoefficients coord a) : BurnolL2)) :=
    ((R coord).continuous.comp synth).congr (fun a => (next_field coord a).symm)
  have currentRead : Continuous (splitInventory coord) :=
    ((P₀).continuous.comp synth).prodMk ((O).continuous.comp synth)
  have nextRead : Continuous (fun a => splitInventory coord (nextCoefficients coord a)) :=
    ((P₀).continuous.comp next).prodMk ((O).continuous.comp next)
  have first := currentRead.continuousAt.tendsto.comp recovered
  have second := nextRead.continuousAt.tendsto.comp recovered
  rw [actual_division_inventory_readback] at first
  rw [actual_division_coefficient_step, actual_division_inventory_readback] at second
  exact ⟨first, second⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
