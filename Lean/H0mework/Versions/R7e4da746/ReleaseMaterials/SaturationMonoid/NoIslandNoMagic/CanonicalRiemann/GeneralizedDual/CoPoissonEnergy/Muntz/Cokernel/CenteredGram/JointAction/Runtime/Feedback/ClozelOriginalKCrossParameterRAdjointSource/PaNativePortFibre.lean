import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PaNativePortMoments
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCrossParameterRAdjointSource.PaNativePortFibre
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open PaNativePortSource
open scoped InnerProductSpace Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace
local notation "q" => (1 / 4 : ℝ)
private abbrev Band := Icc q (4 : ℝ)

private instance : IsFiniteMeasure (volume : Measure Band) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact measure_Icc_lt_top

private def logCoordinate : C(Band, ℂ) :=
  ⟨fun x => (Real.log (x.val / q) : ℂ), by
    apply continuous_ofReal.comp
    apply (continuous_subtype_val.div_const q).log
    intro x
    exact div_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) x.property.1)) (by norm_num)⟩

private theorem logCoordinate_injective : Function.Injective logCoordinate := by
  intro x y same
  have logs : Real.log (x.val / q) = Real.log (y.val / q) := Complex.ofReal_injective same
  have positive (z : Band) : 0 < z.val / q :=
    div_pos (lt_of_lt_of_le (by norm_num) z.property.1) (by norm_num)
  have sameRatio := Real.log_injOn_pos (positive x) (positive y) logs
  apply Subtype.ext
  exact (div_left_inj' (by norm_num : q ≠ 0)).mp sameRatio

private theorem star_logCoordinate : star logCoordinate = logCoordinate := by
  ext x
  simp only [ContinuousMap.star_apply, logCoordinate, ContinuousMap.coe_mk, star_def,
    Complex.conj_ofReal]

/-- Log powers separate the whole compact source fibre, without a supplied completeness witness. -/
private theorem log_moments_faithful (w : Band → ℂ) (hw : MemLp w 2 volume)
    (moments : ∀ n : Nat, ∫ x : Band, logCoordinate x ^ n * w x = 0) :
    w =ᵐ[volume] 0 := by
  let F : Lp ℂ 2 (volume : Measure Band) := hw.star.toLp (star w)
  let L : C(Band, ℂ) →L[ℂ] ℂ :=
    (innerSL ℂ F).comp (ContinuousMap.toLp 2 volume ℂ)
  have evaluated (f : C(Band, ℂ)) : L f = ∫ x : Band, f x * w x := by
    change inner ℂ F (ContinuousMap.toLp 2 volume ℂ f) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hw.star,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f]
      with x source test
    rw [source, test]
    simp only [Pi.star_apply, RCLike.inner_apply, starRingEnd_apply, star_star, mul_comm]
  have powers (n : Nat) : L (logCoordinate ^ n) = 0 := by
    rw [evaluated]
    exact moments n
  let A : StarSubalgebra ℂ C(Band, ℂ) := StarAlgebra.adjoin ℂ {logCoordinate}
  have separates : A.SeparatesPoints := by
    intro x y different
    refine ⟨logCoordinate, ⟨logCoordinate, ?_, rfl⟩, ?_⟩
    · exact StarAlgebra.self_mem_adjoin_singleton ℂ logCoordinate
    · exact fun same => different (logCoordinate_injective same)
  have algebra_zero : ∀ f ∈ A, L f = 0 := by
    intro f admitted
    change f ∈ A.toSubalgebra at admitted
    dsimp only [A] at admitted
    rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, star_logCoordinate,
      Set.union_self, Algebra.adjoin_singleton_eq_range_aeval] at admitted
    obtain ⟨polynomial, rfl⟩ := admitted
    change L (Polynomial.aeval logCoordinate polynomial) = 0
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    simp only [map_smul, powers, smul_zero, Finset.sum_const_zero]
  have dense : Dense (A : Set C(Band, ℂ)) := by
    rw [dense_iff_closure_eq]
    change (A.topologicalClosure : Set C(Band, ℂ)) = Set.univ
    rw [ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A separates]
    rfl
  have whole : ∀ f : C(Band, ℂ), L f = 0 := by
    have equal : (fun f => L f) = (fun _ => (0 : ℂ)) :=
      L.continuous.ext_on dense continuous_const algebra_zero
    intro f
    exact congrFun equal f
  have zero : F = 0 :=
    (ContinuousMap.toLp_denseRange ℂ (volume : Measure Band) ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).eq_zero_of_inner_left
      ℂ whole
  filter_upwards [MemLp.coeFn_toLp hw.star, Lp.coeFn_zero ℂ 2 (volume : Measure Band)]
    with x source empty
  have : star (w x) = 0 := by
    change F x = star (w x) at source
    rw [zero] at source
    exact source.symm.trans empty
  exact star_eq_zero.mp this

private def sourceWeight (c : BurnolCompletedMellinCoordinate) : C(Band, ℂ) :=
  ⟨fun x => (x.val : ℂ) ^ (-c.value), by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Complex.continuousAt_ofReal_cpow_const x.val (-c.value)
      (Or.inr (ne_of_gt (lt_of_lt_of_le (by norm_num) x.property.1)))).comp
        continuous_subtype_val.continuousAt⟩

private theorem source_zero_of_ports (c : BurnolCompletedMellinCoordinate) (input : ↥Pa)
    (ports : ∀ n, port c n input = 0) : sourceMap input = 0 := by
  let α := sourceMap input
  have sourceLp : MemLp (fun x : Band => α x.val) 2 volume :=
    ((Lp.memLp α).restrict Band).comp_measurePreserving
      (measurePreserving_subtype_coe measurableSet_Icc)
  have weightedLp : MemLp (fun x : Band => sourceWeight c x * α x.val) 2 volume :=
    sourceLp.mul' (BoundedContinuousFunction.memLp_top
      (BoundedContinuousFunction.mkOfCompact (sourceWeight c)))
  have weightedZero := log_moments_faithful (fun x : Band => sourceWeight c x * α x.val)
    weightedLp (by
      intro n
      have generated := PaNativePortMoments.actual_port_log_moment c n input
      rw [ports n] at generated
      have coefficient : (2 : ℂ) * (-2 : ℂ) ^ n / (n.factorial : ℂ) ≠ 0 := by
        exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      have moment := (mul_eq_zero.mp generated.symm).resolve_left coefficient
      rw [← integral_subtype measurableSet_Icc] at moment
      convert moment using 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [logCoordinate, sourceWeight, ContinuousMap.coe_mk, α]
        ring))
  have positiveZero : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Band → α x = 0 := by
    apply (ae_restrict_iff' measurableSet_Icc).mp
    apply (ae_restrict_iff_subtype measurableSet_Icc).mpr
    filter_upwards [weightedZero] with x zero
    have weight : sourceWeight c x ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_of_lt_of_le (by norm_num) x.property.1))))
    exact (mul_eq_zero.mp zero).resolve_left weight
  have reflected : ∀ᵐ x ∂(volume : Measure ℝ), α (-x) = α x := by
    have reflection := Lp.coeFn_compMeasurePreserving α negMeasurePreserving
    have even : reflectL2 α = α := original_tate_source_even input.val
    change (fun x => reflectL2 α x) =ᵐ[volume] (fun x => α (-x)) at reflection
    rw [even] at reflection
    exact reflection.symm
  have negativeZero := negMeasurePreserving.quasiMeasurePreserving.ae positiveZero
  have annulus : sourceAnnulusCut α = α := sourceAnnulusCut_original_pa input.val input.property
  apply Lp.ext
  filter_upwards [positiveZero, negativeZero, reflected, sourceAnnulusCut_coeFn α,
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x positive negative reflection cut empty
  rw [empty]
  rw [annulus] at cut
  by_cases inside : q < |x| ∧ |x| ≤ 4
  · rcases le_or_gt 0 x with nonnegative | negativeSign
    · exact positive ⟨by simpa only [abs_of_nonneg nonnegative] using inside.1.le,
        by simpa only [abs_of_nonneg nonnegative] using inside.2⟩
    · rw [← reflection]
      exact negative ⟨by simpa only [abs_of_neg negativeSign] using inside.1.le,
        by simpa only [abs_of_neg negativeSign] using inside.2⟩
  · rw [if_neg inside] at cut
    exact cut

/-- Every native feedback coordinate is generated by the actual original correction history. -/
theorem all_ports_zero_iff (c : BurnolCompletedMellinCoordinate) (input : ↥Pa) :
    (∀ n, port c n input = 0) ↔ input = 0 := by
  constructor
  · intro ports
    exact (sourceMap_zero_iff input).mp (source_zero_of_ports c input ports)
  · rintro rfl
    exact zero_port_control c

theorem family_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (fun input : ↥Pa => fun n : Nat => port c n input) := by
  intro left right same
  have difference (n : Nat) : loop c n (left - right) = loop c n left - loop c n right := by
    induction n with
    | zero => rfl
    | succ n previous =>
      unfold loop at *
      simp only [Function.iterate_succ_apply']
      rw [previous, map_sub]
  have ports : ∀ n, port c n (left - right) = 0 := by
    intro n
    unfold port
    rw [difference]
    change burnolPaResolventSourceCoefficient c
      ((loop c n left : BurnolPaAmbientCarrier) - (loop c n right : BurnolPaAmbientCarrier)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun same n)
  exact sub_eq_zero.mp ((all_ports_zero_iff c (left - right)).mp ports)

end OriginalKCrossParameterRAdjointSource.PaNativePortFibre
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
