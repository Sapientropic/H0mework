import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.PotentialHalf
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.CenteredPayment
import H0mework.Versions.X.NavierStokes.WindowSchurMean.ResidualLoad

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeCenteredPotentialPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceDualEvolution (lifted energy)
open NativeWindowTraceAdjoint (value)
open NativeWindowHistoryMeanAction (meanValue)
open NativeWindowHistoryAdjointSpatialHalf (moment moment_original moment_nonnegative energyCap energyCap_positive)
open NativeUnheatedSexticLatticePower (radical radical_positive radical_fourth)
open NativeCenteredResponseTensor (centered)
open NativeWindowDistributedAdjoint (testAction)
noncomputable section
variable {nu : Viscosity}

private theorem moment_interpolation (M : ℕ) (z : physicalSpace (modes M)) :
    moment (modes M) 3 z^2 ≤ moment (modes M) 2 z*moment (modes M) 4 z := by
  rw [moment_original,moment_original,moment_original]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro k _; positivity [radical_positive k]
  · intro k _; positivity [radical_positive k]
  · intro k _; exact le_of_eq (by ring)

private theorem moment_graph (M : ℕ) (z : physicalSpace (modes M)) :
    moment (modes M) 4 z ≤ (4/(2*Real.pi)^4)*‖coefficients (modes M) (testAction (nu := nu) M z)‖^2 := by
  have graph : ‖coefficients (modes M) (testAction (nu := nu) M z)‖^2=
      ∑ k∈modes M,integerWaveViscousMultiplier k^2*(∑ i : Coordinate,‖z.1 k i‖^2) := by
    rw [← real_inner_self_eq_norm_sq]
    change pairing (modes M) (testAction (nu := nu) M z) (testAction (nu := nu) M z)=_
    rw [NativeWindowHistoryCreationGeometry.pairing_mass]
    simp only [testAction,NativeWindowOperatorGreen.laplacian_row,Pi.smul_apply,norm_smul,
      mul_pow,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
  rw [graph,moment_original,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k member
  have k0 : k≠0 := fun h => modes_zero M (h ▸ member)
  have bound : NativeUnheatedSexticLatticePower.mass k ≤ 2*integerWaveNormSq k := by
    unfold NativeUnheatedSexticLatticePower.mass
    linarith [ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity.one_le_integerWaveNormSq k k0]
  have squared := pow_le_pow_left₀ (NativeUnheatedSexticLatticePower.mass_positive k).le bound 2
  have weight : radical k^8 ≤ (4/(2*Real.pi)^4)*integerWaveViscousMultiplier k^2 := by
    rw [show radical k^8=(radical k^4)^2 by ring,radical_fourth]
    apply squared.trans_eq
    unfold integerWaveViscousMultiplier
    field_simp
    ring
  exact (mul_le_mul_of_nonneg_right weight (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring)

private theorem fourth_young (W S G K eta : ℝ) (S0 : 0 ≤ S) (G0 : 0 ≤ G) (K0 : 0 ≤ K)
    (positive : 0 < eta) (paid : W^4 ≤ K*S^3*G) :
    W ≤ eta*G+(1+K/eta)*S := by
  let B := 1+K/eta
  have B1 : 1 ≤ B := by dsimp only [B]; linarith [div_nonneg K0 positive.le]
  by_cases small : W ≤ B*S
  · exact small.trans (le_add_of_nonneg_left (mul_nonneg positive.le G0))
  have big : B*S < W := lt_of_not_ge small
  have base : S ≤ B*S := by simpa only [one_mul] using mul_le_mul_of_nonneg_right B1 S0
  have ws : S ≤ W := base.trans big.le
  have W0 : 0 < W := lt_of_le_of_lt (mul_nonneg (zero_le_one.trans B1) S0) big
  have scale : K*S ≤ eta*W := by
    have enlarged := mul_le_mul_of_nonneg_left big.le positive.le
    have same : eta*(B*S)=(eta+K)*S := by dsimp only [B]; field_simp
    rw [same] at enlarged
    nlinarith only [enlarged,mul_nonneg positive.le S0]
  have cube := mul_le_mul scale (pow_le_pow_left₀ S0 ws 2) (sq_nonneg S) (mul_nonneg positive.le W0.le)
  have grown := mul_le_mul_of_nonneg_right cube G0
  have controlled : W ≤ eta*G := by
    apply (mul_le_mul_iff_left₀ (pow_pos W0 3)).mp
    nlinarith only [paid,grown]
  exact controlled.trans (le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans B1) S0))

private theorem moment_sub (M : ℕ) (u v : physicalSpace (modes M)) :
    moment (modes M) 2 (u-v) ≤ 2*moment (modes M) 2 u+2*moment (modes M) 2 v := by
  simp only [moment_original,Finset.mul_sum,Submodule.coe_sub,lp.coeFn_sub,Pi.sub_apply]
  have each (k : IntegerWavevector) (i : Coordinate) :
      radical k^4*‖u.1 k i-v.1 k i‖^2 ≤
        2*(radical k^4*‖u.1 k i‖^2)+2*(radical k^4*‖v.1 k i‖^2) := by
    have bounded := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (u.1 k i) (v.1 k i)) 2
    have scalar : ‖u.1 k i-v.1 k i‖^2 ≤2*‖u.1 k i‖^2+2*‖v.1 k i‖^2 := by
      nlinarith only [bounded,sq_nonneg (‖u.1 k i‖-‖v.1 k i‖)]
    exact (mul_le_mul_of_nonneg_left scalar (pow_nonneg (radical_positive k).le _)).trans_eq (by ring)
  simpa only [Finset.sum_add_distrib] using
    (Finset.sum_le_sum (s := modes M) fun k _ =>
      Finset.sum_le_sum (s := Finset.univ) fun i _ => each k i)

private theorem projection (M : ℕ) (u : physicalSpace (modes M)) :
    complexSharpSupportProjection (modes M) u.1=u.1 := by
  apply lp.ext
  funext k
  by_cases inside : k∈modes M
  · simp only [complexSharpSupportProjection_apply,if_pos inside]
  · simp only [complexSharpSupportProjection_apply,if_neg inside,physical_supported u k inside]

theorem centered_moment (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧∀ frame∈Icc 0 horizon,∀ᵐ time : ℝ,0 ≤ time →∀ M,
      moment (modes M) 2 (centered seed M frame time) ≤
        C*(1+NativeUnheatedSourceGradient.mass seed time) := by
  let B := max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon)
  let A := energyCap nu*((NativeUnifiedCompleteSource.budget seed)^2+nu.coeff*(2*Real.pi)^2)
  have B0 : 0 ≤ B := le_max_left _ _
  have A0 : 0 ≤ A := by dsimp only [A]; positivity [nu.coeff_pos,(energyCap_positive nu).le]
  refine ⟨2*(A+B),by positivity,fun frame framed => ?_⟩
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular positive M
  let u := value seed M time
  let m := meanValue seed M frame
  let Y := NativeUnheatedSourceGradient.mass seed time
  have Y0 : 0 ≤ Y := NativeUnheatedSourceGradient.mass_nonnegative seed time
  have gradient := NativeWholeH1Approximation.project_mass_le M
    (NativeUnheatedSourceGradient.physical seed time positive) (regular positive)
  rw [NativeUnheatedSourceGradient.physical_mass] at gradient
  unfold NativeWholeH1Mixed.gradientMass NativeWholeH1Mixed.gradientDensity at gradient
  rw [NativeWholeH1Approximation.project_whole] at gradient
  have actual : NativeUnheatedStressProduct.gradientMass u.1 ≤ Y := by
    rw [show u=value seed M time from rfl,NativeWindowTraceAdjoint.value,
      NativeWindowStageNineSource.lift_load seed time positive M]
    simpa only [NativeWindowStressOseenSource.load,NativeUnheatedSourceQuadraticApprox.physicalSource,
      dif_pos positive] using! gradient
  have curl := NativeWindowAugmentedTestProduct.curl_original (modes M) u (modes_zero M)
  rw [projection] at curl
  have mass := pow_le_pow_left₀ (norm_nonneg _) (NativeWindowTraceAdjoint.value_mass_bound seed M time positive) 2
  have heat : NativeWindowHistoryHeatDual.energy nu M u ≤
      (NativeUnifiedCompleteSource.budget seed)^2+nu.coeff*(2*Real.pi)^2*Y := by
    change ‖coefficients (modes M) u‖^2+nu.coeff*NativeCommonAdvectorAction.curlPair (modes M) u.1 u.1 ≤ _
    rw [curl]
    have scaled := mul_le_mul_of_nonneg_left actual (show 0 ≤ nu.coeff*(2*Real.pi)^2 by positivity [nu.coeff_pos])
    nlinarith only [mass,scaled]
  have raw := (NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M u).trans
    (mul_le_mul_of_nonneg_left heat (energyCap_positive nu).le)
  have mean3 := NativeWindowHistoryCreationMean.mean_moment seed 0 horizon M frame framed
  rw [NativeWindowHistoryMeanResidualLoad.jet_zero_mean] at mean3
  have mean23 : moment (modes M) 2 m ≤ moment (modes M) 3 m := by
    rw [moment_original,moment_original]
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact pow_le_pow_right₀
      (Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr (NativeUnheatedSexticLatticePower.mass_one k))) (by norm_num)
  have mean : moment (modes M) 2 m ≤ B := mean23.trans (mean3.trans (le_max_right _ _))
  have split := moment_sub M u m
  change moment (modes M) 2 (u-m) ≤ _
  dsimp only [A]
  nlinarith only [raw,mean,split,mul_nonneg
    (mul_nonneg (energyCap_positive nu).le (sq_nonneg (NativeUnifiedCompleteSource.budget seed))) Y0,
    mul_nonneg B0 Y0,mul_nonneg (energyCap_positive nu).le (mul_nonneg nu.coeff_pos.le (sq_nonneg (2*Real.pi)))]

theorem source_potential_work_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) (eta : ℝ) (positive : 0 < eta) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧∀ radius ≥ low,∀ outerRadius ≤ radius,∀ M,
      ∀ frame∈Icc 0 horizon,∀ᵐ time : ℝ,time∈Icc 0 horizon →∀ w : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let z := lifted seed M F radius time w
      |NativeCenteredResponsePayment.potentialWork seed M F radius frame time z| ≤
        eta*‖coefficients (modes M) (testAction (nu := nu) M z)‖^2+
          C*(1+NativeUnheatedSourceGradient.mass seed time)*energy seed M F radius time w := by
  obtain ⟨first,K,K0,potentialPaid⟩ := NativeTracePotentialHalf.source_potential_square seed horizon nonnegative
  obtain ⟨last,_,_,controlled⟩ := NativeWindowTraceDualEvolution.source_control seed horizon nonnegative
  obtain ⟨V,V0,centeredPaid⟩ := centered_moment seed horizon
  let A := 3*(2*Real.pi)^2*NativeWindowHistoryAdjointSpatialHalf.cap^2
  let Z := 2*energyCap nu
  let L := 4/(2*Real.pi)^4
  let B := 4*K*A*V
  let J := B^2*Z*L
  have A0 : 0 ≤ A := by dsimp only [A]; positivity
  have Z0 : 0 ≤ Z := by dsimp only [Z]; positivity [(energyCap_positive nu).le]
  have L0 : 0 ≤ L := by dsimp only [L]; positivity
  have B0 : 0 ≤ B := by dsimp only [B]; positivity
  have J0 : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨max first last,1+J/eta,by positivity,fun radius above outerRadius covered M frame framed => ?_⟩
  filter_upwards [centeredPaid frame framed] with time meanBound inside w
  let F := integerWaveFrequencyCube outerRadius
  let v := centered seed M frame time
  let z := lifted seed M F radius time w
  let E := energy seed M F radius time w
  let s := 1+NativeUnheatedSourceGradient.mass seed time
  let G := ‖coefficients (modes M) (testAction (nu := nu) M z)‖^2
  let k := NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M) nu v z
  let P := NativeDistributedLyapunov.potential seed M F radius time z
  let W := |2*pairing (modes M) P k|
  have G0 : 0 ≤ G := sq_nonneg ‖coefficients (modes M) (testAction (nu := nu) M z)‖
  have s1 : 1 ≤ s := by dsimp only [s]; linarith [NativeUnheatedSourceGradient.mass_nonnegative seed time]
  have s0 : 0 ≤ s := zero_le_one.trans s1
  have control := (controlled radius ((le_max_right first last).trans above) outerRadius M time inside).2 w
  have E0 : 0 ≤ E := control.1
  have PP := potentialPaid radius ((le_max_left first last).trans above) outerRadius covered M time inside w
  change ‖coefficients (modes M) P‖^2 ≤ K*E at PP
  have Vpaid : moment (modes M) 2 v ≤ V*s := meanBound inside.1 M
  have heat : NativeWindowHistoryHeatDual.energy nu M z ≤ 2*E := by
    have cost := control.2.1
    have normed : pairing (modes M) z z=‖coefficients (modes M) z‖^2 :=
      real_inner_self_eq_norm_sq (coefficients (modes M) z)
    change pairing (modes M) z z+(nu.coeff/2)*NativeCommonAdvectorAction.curlPair (modes M) z.1 z.1 ≤ E at cost
    rw [normed] at cost
    change ‖coefficients (modes M) z‖^2+nu.coeff*NativeCommonAdvectorAction.curlPair (modes M) z.1 z.1 ≤ _
    nlinarith only [cost,sq_nonneg ‖coefficients (modes M) z‖]
  have m2 : moment (modes M) 2 z ≤ Z*E :=
    ((NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M z).trans
      (mul_le_mul_of_nonneg_left heat (energyCap_positive nu).le)).trans_eq (by dsimp only [Z]; ring)
  have m4 : moment (modes M) 4 z ≤ L*G := moment_graph (nu := nu) M z
  have m3 := (moment_interpolation M z).trans
    (mul_le_mul m2 m4 (moment_nonnegative _ 4 z) (mul_nonneg Z0 E0))
  have advected := NativeWindowHistoryAdjointSpatialHalf.transport_bound true
    (modes M) (modes_zero M) (modes_closed M) nu v z
  have read : NativeWindowHistoryAdjointSpatialHalf.outputSquare true (modes M) k=‖coefficients (modes M) k‖^2 := by
    simpa only [NativeWindowHistoryAdjointSpatialHalf.outputSquare,NativeWindowHistoryAdjointSpatialHalf.weight,
      if_true,one_pow,one_mul] using (NativeWindowHistoryCreationGeometry.pairing_mass (modes M) k).symm.trans
        (real_inner_self_eq_norm_sq (coefficients (modes M) k))
  change NativeWindowHistoryAdjointSpatialHalf.outputSquare true (modes M) k ≤
    A*moment (modes M) 2 v*moment (modes M) 3 z at advected
  rw [read] at advected
  have kk := advected.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Vpaid A0) (moment_nonnegative _ 3 z))
  have pair : W ≤ 2*‖coefficients (modes M) P‖*‖coefficients (modes M) k‖ := by
    dsimp only [W]
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm
      (coefficients (modes M) P) (coefficients (modes M) k)) (by norm_num : (0 : ℝ)≤2)).trans_eq (by ring)
  have combined := mul_le_mul PP kk (sq_nonneg ‖coefficients (modes M) k‖) (mul_nonneg K0 E0)
  have scaled := mul_le_mul_of_nonneg_left combined (show (0 : ℝ) ≤ 4 by norm_num)
  have WS : W^2 ≤ B*s*E*moment (modes M) 3 z := by
    have squared := pow_le_pow_left₀ (abs_nonneg _) pair 2
    dsimp only [B]
    nlinarith only [squared,scaled]
  have squared := pow_le_pow_left₀ (sq_nonneg W) WS 2
  have interpolation := mul_le_mul_of_nonneg_left m3
    (mul_nonneg (mul_nonneg (sq_nonneg B) (sq_nonneg s)) (sq_nonneg E))
  have fourth : W^4 ≤ J*s^2*E^3*G := by
    dsimp only [J]
    nlinarith only [squared,interpolation]
  have grow : s^2 ≤ s^3 := by nlinarith only [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr s1)]
  have enlarged := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left grow J0)
    (mul_nonneg (pow_nonneg E0 3) G0)
  have paid : W^4 ≤ J*(s*E)^3*G := by nlinarith only [fourth,enlarged]
  have final := fourth_young W (s*E) G J eta (mul_nonneg s0 E0) G0 J0 positive paid
  change W ≤ eta*G+(1+J/eta)*s*E
  exact final.trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeCenteredPotentialPayment
