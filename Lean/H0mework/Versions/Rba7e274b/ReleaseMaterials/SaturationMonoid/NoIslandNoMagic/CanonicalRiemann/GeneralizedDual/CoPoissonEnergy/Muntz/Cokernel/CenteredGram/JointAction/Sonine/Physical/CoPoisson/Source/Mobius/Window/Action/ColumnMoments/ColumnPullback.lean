import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.FiniteSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators
open OriginalRieszSource
namespace F
export FiniteMobiusResolventFlux (fullPullback cutoff cutoff_read lower_source_cutoff)
end F

 theorem original_B_even (coordinate : BurnolCompletedMellinCoordinate) : reflectL2 (originalB coordinate)=originalB coordinate := by
  change reflectL2 (burnolRadiusZeroExtension (1/4:ℝ) (burnolRieszSingleFourierSource coordinate:BurnolQuarterIntervalL2))=_
  rw [burnolRadiusZeroExtension_reflect,burnolRieszSingleFourierSource_reflection_fixed]
  rfl
 theorem original_column_even (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reflectL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h)=OriginalRieszFiniteColumns.fourierColumn coordinate h := by
  rw [OriginalRieszFinitePairing.fourierColumn_action]
  rw [map_sub,map_smul,reflectL2_burnolMultiplicativeDilation]
  have source := original_B_even coordinate
  unfold originalB at source
  rw [source]

 theorem whole_response_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (wholeContactResponse coordinate)=wholeContactResponse coordinate := by
  unfold wholeContactResponse contactResponse
  simp only [map_sub,map_smul]
  change Kernel.A coordinate • reflectL2 Response.wholeU-Kernel.beta coordinate • reflectL2 Response.wholeV=_
  rw [Response.wholeU_reflection,Response.wholeV_reflection]
  rfl

 theorem full_pullback_read (n : ℕ+) (value : BurnolL2) :
    (F.fullPullback n value:ℝ→ℂ)=ᵐ[volume] fun x=>value (x/(n:ℕ)) := by
  unfold F.fullPullback
  simp only [smul_apply,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  filter_upwards [Lp.coeFn_smul (Real.exp (Real.log (n:ℕ)/2):ℂ) (burnolMultiplicativeDilation (-Real.log (n:ℕ)) value),
    burnolMultiplicativeDilation_coeFn (-Real.log (n:ℕ)) value] with x scalar moved
  rw [scalar]
  change (Real.exp (Real.log (n:ℕ)/2):ℂ)*burnolMultiplicativeDilation (-Real.log (n:ℕ)) value x=_
  rw [moved]
  unfold burnolL2RawNormalizedDilation
  have positive : (0:ℝ)<(n:ℕ) := by exact_mod_cast n.property
  have phase : (Real.exp (Real.log (n:ℕ)/2):ℂ)*(Real.exp (-Real.log (n:ℕ)/2):ℂ)=1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show Real.log (n:ℕ)/2+-Real.log (n:ℕ)/2=0 by ring,Real.exp_zero,Complex.ofReal_one]
  rw [← mul_assoc,phase,one_mul,Real.exp_neg,Real.exp_log positive]
  congr 1
  rw [div_eq_mul_inv,mul_comm]

 theorem half_sample_cutoff_pairing (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h)
    (bounded : h≤Real.log 2) (value : BurnolL2) :
    inner ℂ (Paid.pairedColumn coordinate h) (F.cutoff 4 value)=inner ℂ (Paid.pairedColumn coordinate h) value := by
  rw [original_paired_sample_positive coordinate h nonnegative,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [original_positive_sample_raw coordinate h nonnegative bounded,F.cutoff_read 4 value] with x sampled cut
  rw [sampled,cut]
  by_cases inside : x∈outerBand h
  · have inFour : x∈symmetricInterval 4 := abs_le.mp (outer_band_small h bounded inside).le
    simp only [indicator_of_mem inside,indicator_of_mem inFour]
  · simp only [indicator_of_notMem inside,inner_zero_left]

theorem sampled_column_even (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reflectL2 (burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0)=
      burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0 := by
  let col := OriginalRieszFiniteColumns.fourierColumn coordinate h
  let sampled := burnolAnnulusSamplingL2 col 0
  have reflected := Lp.coeFn_compMeasurePreserving col negMeasurePreserving
  change (reflectL2 col:ℝ→ℂ)=ᵐ[volume] fun x=>col (-x) at reflected
  rw [original_column_even] at reflected
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving sampled negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae_eq (burnolAnnulusSamplingL2_coeFn col 0),
    burnolAnnulusSamplingL2_coeFn col 0,reflected] with x shifted negative direct same
  simp only [Function.comp_def] at negative
  change reflectL2 sampled x=sampled x
  change reflectL2 sampled x=sampled (-x) at shifted
  rw [shifted,negative,direct]
  simp only [burnolAnnulusSamplingRaw,Nat.cast_zero,zero_add,one_mul]
  have incidence : -x∈burnolSamplingAnnulus ↔ x∈burnolSamplingAnnulus := by simp only [burnolSamplingAnnulus,mem_ofPred_eq,abs_neg]
  by_cases inside : x∈burnolSamplingAnnulus
  · rw [indicator_of_mem inside,indicator_of_mem (incidence.mpr inside),← same]
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun after=>inside (incidence.mp after))]

 theorem full_pullback_even (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ+) :
    reflectL2 (F.fullPullback n (wholeContactResponse coordinate))=F.fullPullback n (wholeContactResponse coordinate) := by
  unfold F.fullPullback
  simp only [smul_apply,LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry,map_smul,
    reflectL2_burnolMultiplicativeDilation,whole_response_even]

 theorem column_response_divisor_read (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) (n : ℕ+) :
    inner ℂ (Paid.pairedColumn coordinate h) (F.fullPullback n (wholeContactResponse coordinate))=
      -(2:ℂ)*(Real.exp (h/2):ℂ)*
        (∫ y : ℝ in ((1/4:ℝ)*Real.exp (-h))..(1/4:ℝ),
          star (originalB coordinate y)*wholeContactResponse coordinate (Real.exp h*y/(n:ℕ))) := by
  let sampled := burnolAnnulusSamplingL2 (OriginalRieszFiniteColumns.fourierColumn coordinate h) 0
  let field := F.fullPullback n (wholeContactResponse coordinate)
  let f := fun x : ℝ=>inner ℂ (sampled x) (field x)
  have regular := L2.integrable_inner (𝕜:=ℂ) sampled field
  have even : (fun x : ℝ=>f (-x))=ᵐ[volume] f := by
    have source := Lp.coeFn_compMeasurePreserving sampled negMeasurePreserving
    have sibling := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
    change (reflectL2 sampled:ℝ→ℂ)=ᵐ[volume] fun x=>sampled (-x) at source
    change (reflectL2 field:ℝ→ℂ)=ᵐ[volume] fun x=>field (-x) at sibling
    rw [sampled_column_even] at source
    rw [full_pullback_even] at sibling
    filter_upwards [source,sibling] with x left right
    dsimp only [f]
    rw [← left,← right]
  have support : ∀ᵐ x : ℝ ∂volume,x∉symmetricInterval ((1/4:ℝ)*Real.exp h)→f x=0 := by
    filter_upwards [original_positive_sample_raw coordinate h nonnegative bounded] with x source outside
    dsimp only [f,sampled]
    rw [source,indicator_of_notMem (show x∉outerBand h from fun inside=>outside (abs_le.mp inside.2)),inner_zero_left]
  have exterior := OriginalRieszFinitePairing.exterior_integral_eq_scaled h nonnegative f regular.integrableOn even support
  have innerExterior : inner ℂ sampled field=(∫ x : ℝ in (symmetricInterval (1/4:ℝ))ᶜ,f x) := by
    rw [L2.inner_def,← integral_indicator (measurableSet_symmetricInterval (1/4:ℝ)).compl]
    apply integral_congr_ae
    filter_upwards [original_positive_sample_raw coordinate h nonnegative bounded] with x source
    change inner ℂ (sampled x) (field x)=_
    by_cases outside : x∈(symmetricInterval (1/4:ℝ))ᶜ
    · rw [indicator_of_mem outside]
    · have quarter : |x|≤(1/4:ℝ) := abs_le.mpr (not_not.mp outside)
      rw [indicator_of_notMem outside]
      dsimp only [sampled]
      rw [source,indicator_of_notMem (show x∉outerBand h from fun inside=>not_lt_of_ge quarter inside.1),inner_zero_left]
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ=>Real.exp h*x) volume volume := by
    simpa only [smul_eq_mul] using Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
      (r:=Real.exp h) (Real.exp_ne_zero h)
  have rawIntegral : (∫ y : ℝ in ((1/4:ℝ)*Real.exp (-h))..(1/4:ℝ),f (Real.exp h*y))=
      -(Real.exp (-h/2):ℂ)*
        (∫ y : ℝ in ((1/4:ℝ)*Real.exp (-h))..(1/4:ℝ),
          star (originalB coordinate y)*wholeContactResponse coordinate (Real.exp h*y/(n:ℕ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [ae_restrict_of_ae (qmp.ae_eq (original_positive_sample_raw coordinate h nonnegative bounded)),
      ae_restrict_of_ae (qmp.ae_eq (full_pullback_read n (wholeContactResponse coordinate))),
      ae_restrict_mem measurableSet_uIoc] with y source actual inside
    simp only [Function.comp_def] at source actual
    have order : (1/4:ℝ)*Real.exp (-h)≤(1/4:ℝ) := by nlinarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)]
    have band : y∈Ioc ((1/4:ℝ)*Real.exp (-h)) (1/4:ℝ) := by simpa only [uIoc_of_le order] using inside
    have inverse : Real.exp (-h)*(Real.exp h*y)=y := by rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
    have moved : Real.exp h*y∈outerBand h := by
      apply (normalized_source_band_membership h _).mp
      rw [inverse]
      exact ⟨by simpa only [abs_of_pos (lt_trans (mul_pos (by norm_num) (Real.exp_pos _)) band.1)] using band.1,
        by simpa only [abs_of_pos (lt_trans (mul_pos (by norm_num) (Real.exp_pos _)) band.1)] using band.2⟩
    dsimp only [f,sampled,field]
    rw [source,indicator_of_mem moved,inverse,actual,RCLike.inner_apply]
    simp only [map_mul,map_neg,Complex.conj_ofReal]
    change wholeContactResponse coordinate (Real.exp h*y/(n:ℕ))*(-(Real.exp (-h/2):ℂ)*star (originalB coordinate y))=
      -(Real.exp (-h/2):ℂ)*(star (originalB coordinate y)*wholeContactResponse coordinate (Real.exp h*y/(n:ℕ)))
    ring
  rw [original_paired_sample_positive coordinate h nonnegative,innerExterior,exterior,rawIntegral]
  have phase : (Real.exp h:ℂ)*(Real.exp (-h/2):ℂ)=(Real.exp (h/2):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  have scalar : (2:ℂ)*(Real.exp h:ℂ)*(-(Real.exp (-h/2):ℂ))=-(2:ℂ)*(Real.exp (h/2):ℂ) := by
    calc
      _=-(2:ℂ)*((Real.exp h:ℂ)*(Real.exp (-h/2):ℂ)) := by ring
      _=_ := by rw [phase]
  rw [← mul_assoc,scalar]

 theorem original_response_mu_word (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0≤h)
    (bounded : h≤Real.log 2) :
    inner ℂ (Paid.pairedColumn coordinate h) (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))=
    ∑ n ∈ burnolCenteredMobiusCutoffFinset 4,FiniteMobiusResolventFlux.coefficient n*
      inner ℂ (Paid.pairedColumn coordinate h) (F.fullPullback n (wholeContactResponse coordinate)) := by
  rw [F.lower_source_cutoff,whole_contact_response_mean]
  simp only [zero_smul,sub_zero,inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro n _
  rw [half_sample_cutoff_pairing _ _ nonnegative bounded]

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
