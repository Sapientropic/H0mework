import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeWardSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
open Complex MeasureTheory BurnolPhysicalState
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualWholeWaveSource (h : ℝ) : BurnolL2 :=
  OriginalCommonInverseForcing.SourceJoint.upperSourceWave
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h

def actualWholeWaveR (h : ℝ) : BurnolL2 :=
  burnolDirectRightResolvent (observation.coordinate/2)
    (actualWholeWaveSource observation nontrivial half h)
def actualWholeWavePairedR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.paired (actualWholeWaveR observation nontrivial half h)
def actualWholeWaveSiblingR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.sibling (actualWholeWaveR observation nontrivial half h)

def actualWholeWavePairedVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • actualWholeWaveSiblingR observation nontrivial half h +
    (1/2 : ℂ) • (actualWholeWaveSource observation nontrivial half h -
      fourierL2 (actualWholeWaveSource observation nontrivial half h))
def actualWholeWaveSiblingVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • actualWholeWavePairedR observation nontrivial half h +
    (1/2 : ℂ) • (actualWholeWaveSource observation nontrivial half h +
      fourierL2 (actualWholeWaveSource observation nontrivial half h))

/-- Both actual original R wave actions are generated from the born source material, before any diagonal or mixed price. -/
theorem actual_whole_wave_R_actions (h : ℝ) :
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
      (actualWholeWavePairedR observation nontrivial half h))
      (actualWholeWavePairedVelocity observation nontrivial half h) 0 ∧
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
      (actualWholeWaveSiblingR observation nontrivial half h))
      (actualWholeWaveSiblingVelocity observation nontrivial half h) 0 :=
  OriginalKFullSourceRResponse.Paid.ambient_R_paired_equations _
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) _

def actualWholeWaveDiagonalPrice (h : ℝ) : ℂ :=
  inner ℂ (actualWholeWavePairedR observation nontrivial half h)
    (actualWholeWaveSource observation nontrivial half h + fourierL2 (actualWholeWaveSource observation nontrivial half h)) +
  inner ℂ (actualWholeWaveSource observation nontrivial half h - fourierL2 (actualWholeWaveSource observation nontrivial half h))
    (actualWholeWaveSiblingR observation nontrivial half h)

/-- The source unitary action pays the complete wave diagonal by its own whole R quadratic inventory. -/
theorem actual_whole_wave_diagonal_source_price (h : ℝ) :
    actualWholeWaveDiagonalPrice observation nontrivial half h =
    -2 * (observation.coordinate/2-1/4) *
      inner ℂ (actualWholeWavePairedR observation nontrivial half h)
        (actualWholeWavePairedR observation nontrivial half h) -
    2 * star (observation.coordinate/2-1/4) *
      inner ℂ (actualWholeWaveSiblingR observation nontrivial half h)
        (actualWholeWaveSiblingR observation nontrivial half h) := by
  have action := actual_whole_wave_R_actions observation nontrivial half h
  have generated := action.1.inner ℂ action.2
  have fixed : (fun t : ℝ => inner ℂ
      (burnolMultiplicativeDilation (-t/2) (actualWholeWavePairedR observation nontrivial half h))
      (burnolMultiplicativeDilation (-t/2) (actualWholeWaveSiblingR observation nontrivial half h))) =
      fun _ => inner ℂ (actualWholeWavePairedR observation nontrivial half h)
        (actualWholeWaveSiblingR observation nontrivial half h) := by
    funext t
    exact (burnolMultiplicativeDilation (-t/2)).inner_map_map _ _
  rw [fixed] at generated
  have source := generated.unique (hasDerivAt_const (0 : ℝ)
    (inner ℂ (actualWholeWavePairedR observation nontrivial half h)
      (actualWholeWaveSiblingR observation nontrivial half h)))
  simp only [neg_zero, zero_div, burnolMultiplicativeDilation_zero] at source
  unfold actualWholeWavePairedVelocity actualWholeWaveSiblingVelocity at source
  unfold actualWholeWaveDiagonalPrice
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_div₀, star_one, star_ofNat] at source ⊢
  linear_combination 2 * source

/-- This sign is charged to the original whole R wave material, without a transfer to physical norms. -/
theorem actual_whole_wave_diagonal_real_price (h : ℝ) :
    (actualWholeWaveDiagonalPrice observation nontrivial half h).re =
    -(observation.coordinate.re - 1/2) *
      ((inner ℂ (actualWholeWavePairedR observation nontrivial half h)
        (actualWholeWavePairedR observation nontrivial half h)).re +
       (inner ℂ (actualWholeWaveSiblingR observation nontrivial half h)
        (actualWholeWaveSiblingR observation nontrivial half h)).re) := by
  rw [actual_whole_wave_diagonal_source_price]
  norm_num [Complex.mul_re, Complex.sub_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.star_def, inner_self_im, pow_two, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem actual_whole_wave_diagonal_nonpositive (h : ℝ) :
    (actualWholeWaveDiagonalPrice observation nontrivial half h).re ≤ 0 := by
  rw [actual_whole_wave_diagonal_real_price]
  have rate := (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
  change 1/2 < observation.coordinate.re at rate
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (sub_nonneg.mpr rate.le)
  · exact add_nonneg
      (inner_self_nonneg (𝕜 := ℂ) (x := actualWholeWavePairedR observation nontrivial half h))
      (inner_self_nonneg (𝕜 := ℂ) (x := actualWholeWaveSiblingR observation nontrivial half h))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
