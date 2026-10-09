import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorOccupation
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceGeneralThreeParticleResponse
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussDensityCore
open GaussHalfDensity GaussCoreLabel GaussHistoryHilbert GaussUnitaryHistory NativeHistoryGrade GeneralThreeParticleResponse
open SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse CompositeFullYBorn
open SourceResolventBandLimit SourceResolventLorentzian
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace ContDiff Topology
attribute [local irreducible] embed GaussCoreLabel.project NativeHistoryGrade.projection
  literalCoreResolvent literalSharpResolvent

/-- The full504 mixed-spectator CAR source is inserted directly into the actual
smooth physical core; no hyperPlus-only wedge220 carrier is used. -/
def candidateTest (dual : Bool) (f : ScalarTest) : QuantumTest :=
  ⟨fun z => f z • candidate dual, f.contDiff.smul contDiff_const,
    f.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans f.tsupport_subset⟩

theorem actual_candidate_test_sector (dual : Bool) (f : ScalarTest) :
    project (3,0) (candidateTest dual f) = candidateTest dual f := by
  apply DFunLike.ext
  intro z
  rw [project_apply]
  change fiberPiece (3,0) (f z • candidate dual) = f z • candidate dual
  rw [map_smul,actual_candidate_bottom_sector]

private theorem candidate_support (dual : Bool) (word : Occupation) (hw : word.card ≠ 3) :
    candidate dual word = 0 := by
  have h := congrArg (fun v : FockFiber => v word) (actual_candidate_bottom_sector dual)
  rw [fiberPiece_apply,if_neg] at h
  · exact h.symm
  · intro hl
    exact hw (congrArg (fun l : Label => l.1.val) hl)

private theorem candidate_weight (dual : Bool) (c : ℕ → ℂ) :
    weight c (candidate dual) = c 3 • candidate dual := by
  apply PiLp.ext
  intro word
  rw [weight_apply]
  change c word.card * candidate dual word = c 3 * candidate dual word
  by_cases h : word.card = 3
  · rw [h]
  · rw [candidate_support dual word h,mul_zero,mul_zero]

/-- The literal occupation density retains the actual mixed source's norm²=2. -/
theorem actual_candidate_test_density (dual : Bool) (f g : ScalarTest) (z : SourceCoordinateSlice) :
    densityPair (candidateTest dual f) (candidateTest dual g) z =
      2 * (complexDensity 3 z * star (f z) * g z) := by
  rw [densityPair]
  change inner ℂ (weight (fun N => complexDensity N z) (f z • candidate dual))
    (g z • candidate dual) = _
  rw [map_smul,candidate_weight,inner_smul_left,inner_smul_right,
    inner_smul_left,actual_candidate_norm_sq]
  have hc : star (complexDensity 3 z) = complexDensity 3 z := by simp [complexDensity]
  change (star (f z) * (g z * (star (complexDensity 3 z) * 2))) = _
  rw [hc]
  ring

theorem actual_candidate_test_pair (dual : Bool) (f g : ScalarTest) :
    inner ℂ (embed (candidateTest dual f)) (embed (candidateTest dual g)) =
      2 * GaussDensityCore.pair 3 f g := by
  change sourcePair _ _ = _
  rw [sourcePair_integral]
  simp_rw [actual_candidate_test_density]
  exact integral_const_mul 2 _

theorem actual_candidate_test_norm (dual : Bool) (f : ScalarTest) :
    ‖embed (candidateTest dual f)‖^2 = 2 * ‖scalarLp 3 f‖^2 := by
  have h := actual_candidate_test_pair dual f f
  rw [←GaussDensityCore.hilbert_pair] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat] using! h)

theorem actual_candidate_test_nonzero (dual : Bool) (f : ScalarTest) (hf : f ≠ 0) :
    embed (candidateTest dual f) ≠ 0 := by
  intro hz
  have ht : candidateTest dual f = 0 := embed_injective (hz.trans (map_zero embed).symm)
  apply hf
  apply DFunLike.ext
  intro z
  have h := congrArg (fun q : QuantumTest => q z) ht
  change f z • candidate dual = 0 at h
  exact (smul_eq_zero.mp h).resolve_right (actual_candidate_nonzero dual)

/-- An actual compact smooth source profile is generated inside the original
physical chart, with its value fixed at the native source point. -/
theorem actual_scalar_test_exists : ∃f : ScalarTest, f sourcePoint.val = 1 := by
  obtain ⟨b,hbs,hbk,hbc,_,hb1⟩ := exists_contDiff_tsupport_subset
    (n := (⊤ : ℕ∞)) (physicalChart.isOpen.mem_nhds sourcePoint.property)
  let f : ScalarTest := ⟨fun z => (b z : ℂ),Complex.ofRealCLM.contDiff.comp hbc,
    hbk.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset (by simp : (Complex.ofReal : ℝ → ℂ) 0 = 0) b).trans hbs⟩
  refine ⟨f,?_⟩
  change (b sourcePoint.val : ℂ) = 1
  rw [hb1,Complex.ofReal_one]

/-- The full half-density completion of this actual test has precisely the
same mixed-CAR coefficients and the Number-three scalar half-density. -/
theorem actual_candidate_half_density (dual : Bool) (f : ScalarTest) :
    fockHalfDensityEquiv (embed (candidateTest dual f)) =
      WithLp.toLp 2 (fun word : Occupation => candidate dual word • halfDensityEquiv 3 (scalarLp 3 f)) := by
  apply PiLp.ext
  intro word
  have hcoord : (fockHalfDensityEquiv (embed (candidateTest dual f))) word =
      halfDensityEquiv word.card ((embed (candidateTest dual f)) word) := by
    unfold fockHalfDensityEquiv
    exact congrArg (fun v : FlatFockHilbert => v word)
      (LinearIsometryEquiv.piLpCongrRight_apply (p := 2)
        (fun w : Occupation => halfDensityEquiv w.card) (embed (candidateTest dual f)))
  rw [hcoord]
  have he : (embed (candidateTest dual f)) word = candidate dual word • scalarLp word.card f := by
    apply Lp.ext
    filter_upwards [embed_ae (candidateTest dual f) word,
      scalarLp_ae word.card f,Lp.coeFn_smul (candidate dual word) (scalarLp word.card f)] with z he hf hs
    rw [he,hs]
    change f z * candidate dual word = candidate dual word * scalarLp word.card f z
    rw [hf,mul_comm]
  rw [he,map_smul]
  change candidate dual word • halfDensityEquiv word.card (scalarLp word.card f) =
    candidate dual word • halfDensityEquiv 3 (scalarLp 3 f)
  by_cases hc : word.card = 3
  · have hs : ∀N : ℕ, N = 3 → halfDensityEquiv N (scalarLp N f) = halfDensityEquiv 3 (scalarLp 3 f) := by
      intro N hN
      subst N
      rfl
    rw [hs word.card hc]
  · rw [candidate_support dual word hc,zero_smul,zero_smul]

/-- A genuine nonzero full504 core input is generated without a supplied
nonzero witness or wedge220 realization. -/
theorem actual_candidate_core_source (dual : Bool) :
    ∃f : ScalarTest, f sourcePoint.val = 1 ∧ project (3,0) (candidateTest dual f) = candidateTest dual f ∧
      embed (candidateTest dual f) ≠ 0 := by
  obtain ⟨f,hf⟩ := actual_scalar_test_exists
  refine ⟨f,hf,actual_candidate_test_sector dual f,actual_candidate_test_nonzero dual f ?_⟩
  intro hz
  have hv := congrArg (fun g : ScalarTest => g sourcePoint.val) hz
  change f sourcePoint.val = 0 at hv
  rw [hf] at hv
  exact one_ne_zero hv

/-- The actual Q1 mixed-spectator source has the complete full-H0+Y response
and the independently generated sharp response, with four physical grades. -/
theorem actual_candidate_full_response (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (dual : Bool) (f : ScalarTest) :
    literalCoreResolvent F z hz (candidateTest dual f) =
      ∑j : Fin 4, leg F z hz (candidateTest dual f) j.val ∧
    literalSharpResolvent F z hz (candidateTest dual f) = resolventCore F z hz (candidateTest dual f) :=
  ⟨full_response F z hz _ (actual_candidate_test_sector dual f),
    sharp_response F z hz _ (actual_candidate_test_sector dual f)⟩

/-- Direct coherent two-profile Q1 source spectrum on one ordinary event.
The scalar profile, true complex cross term and original full-source forcing
remain explicit; π/μ is the pulse mass factor. -/
theorem actual_candidate_source_pulse_spectrum (B : Index) (dual : Bool) (f g : ScalarTest) :
    ∃K₀ : Index, B ⊆ K₀ ∧ ∀K : Index, K₀ ⊆ K →
      ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ,
      (∀w : ℝ, sourcePulseGram K (candidateTest dual f) (candidateTest dual g) sharp advanced μ hμ w =
        (kernel μ 0 w : ℂ) * (2 * GaussDensityCore.pair 3 f g)) ∧
      Integrable (sourcePulseGram K (candidateTest dual f) (candidateTest dual g) sharp advanced μ hμ) ∧
      (∫w : ℝ, sourcePulseGram K (candidateTest dual f) (candidateTest dual g) sharp advanced μ hμ w) =
        (Real.pi / μ : ℂ) * (2 * GaussDensityCore.pair 3 f g) ∧
      sourcePulseMeasure K (candidateTest dual f) sharp advanced μ hμ =
        volume.withDensity (fun w => ENNReal.ofReal (kernel μ 0 w * (2 * ‖scalarLp 3 f‖^2))) ∧
      sourcePulseMeasure K (candidateTest dual f) sharp advanced μ hμ Set.univ =
        ENNReal.ofReal ((Real.pi / μ) * (2 * ‖scalarLp 3 f‖^2)) := by
  obtain ⟨K₀,hB,hK₀⟩ := actual_source_pulse_spectrum B (candidateTest dual f) (candidateTest dual g)
  refine ⟨K₀,hB,?_⟩
  intro K hK sharp advanced μ hμ
  simpa only [actual_candidate_test_pair,actual_candidate_test_norm] using hK₀ K hK sharp advanced μ hμ

/-- The native chart generates a nonzero mixed-spectator source whose actual
full-H0+Y and independent-sharp pulse responses and positive spectral mass
hold together on one ordinary cofinal event, with no supplied source witness. -/
theorem actual_generated_candidate_pulse (B : Index) (dual : Bool) :
    ∃f : ScalarTest, f sourcePoint.val = 1 ∧ ∃K₀ : Index, B ⊆ K₀ ∧
      ∀K : Index, K₀ ⊆ K → ∀sharp advanced : Bool, ∀μ : ℝ, ∀hμ : 0 < μ,
      (∀w : ℝ, embed (literalResponse K sharp
        (fullSourcePulse sharp (candidateTest dual f) advanced μ w) advanced μ hμ w) =
          (line (FullYPairedParseval.direction advanced * μ) w)⁻¹ • embed (candidateTest dual f) ∧
        embed (literalResponse K sharp
          (fullSourcePulse sharp (candidateTest dual f) advanced μ w) advanced μ hμ w) ≠ 0) ∧
      sourcePulseMeasure K (candidateTest dual f) sharp advanced μ hμ Set.univ =
        ENNReal.ofReal ((Real.pi / μ) * (2 * ‖scalarLp 3 f‖^2)) ∧
      0 < sourcePulseMeasure K (candidateTest dual f) sharp advanced μ hμ Set.univ := by
  classical
  obtain ⟨f,hf,_,hne⟩ := actual_candidate_core_source dual
  obtain ⟨KR,hBR,hR⟩ := full_source_pulse_return B (candidateTest dual f) (candidateTest dual f)
  obtain ⟨KM,hBM,hM⟩ := actual_source_pulse_spectrum B (candidateTest dual f) (candidateTest dual f)
  refine ⟨f,hf,KR ∪ KM,fun x hx => Finset.mem_union.mpr (Or.inl (hBR hx)),?_⟩
  intro K hK sharp advanced μ hμ
  have hr : KR ⊆ K := fun x hx => hK (Finset.mem_union.mpr (Or.inl hx))
  have hm : KM ⊆ K := fun x hx => hK (Finset.mem_union.mpr (Or.inr hx))
  have hm' := (hM K hm sharp advanced μ hμ).2.2.2.2
  refine ⟨?_,?_,?_⟩
  · intro w
    have he := hR K hr (candidateTest dual f) (Or.inl rfl) sharp advanced μ hμ w
    refine ⟨he,?_⟩
    rw [he]
    exact smul_ne_zero (inv_ne_zero (fun hz =>
      causal_line_nonreal advanced μ w hμ (by rw [hz]; rfl))) hne
  · simpa only [actual_candidate_test_norm] using hm'
  · rw [hm',ENNReal.ofReal_pos]
    exact mul_pos (div_pos Real.pi_pos hμ) (sq_pos_of_pos (norm_pos_iff.mpr hne))

end LowEnergy.MixedSpectatorCandidate
