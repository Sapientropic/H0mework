import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceOriginalHardyParticular
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRetardedSourceJet

/-! The generated Hardy particular has a full-frequency retarded tail before the source filter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceHardyRetardedTail
open Filter MeasureTheory GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory
open SourceRelativePowerTail SourceCornerForcing SourceRetardedForcingTail
open SourceOriginalHardyParticular SourceActualResolventEnergy SourceRetardedSourceJet
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped Topology InnerProductSpace

def coefficientSolver (sharp : Bool) : H →L[ℂ] H := solver.comp (coefficientMap sharp)
def cutoffSolver (sharp : Bool) (m ell : ℕ) : H →L[ℂ] H :=
  (coefficientSolver sharp).comp (relativeTail m ell)

def particular (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g : H) : H :=
  cutoffSolver sharp m ell (finiteResolvent F z g)

theorem original_relative_tail (x : H) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖relativeTail m ell x‖<ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := whole_history_relative_tail (inclusion x) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  simpa only [reader_inclusion,LinearIsometry.norm_map] using hN m hm ell hell

theorem bounded_original_tail (A : H →L[ℂ] H) (x : H) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖A (relativeTail m ell x)‖<ε := by
  intro ε hε
  have hC : 0<‖A‖+1 := by positivity
  obtain ⟨N,hN⟩ := original_relative_tail x (ε/(‖A‖+1)) (div_pos hε hC)
  refine ⟨N,fun m hm ell hell => ?_⟩
  have ht := hN m hm ell hell
  have hn := A.le_opNorm (relativeTail m ell x)
  have he := (mul_lt_mul_of_pos_left ht hC)
  rw [mul_div_cancel₀ ε (ne_of_gt hC)] at he
  nlinarith [norm_nonneg (relativeTail m ell x)]

theorem fixed_forcing_uniform_energy_tail (μ : ℝ) (hμ : 0<μ)
    (A : H →L[ℂ] H) (g : H) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
      (∫⁻ t : ℝ, ENNReal.ofReal
        (‖finiteResolvent F (line μ t) (A (relativeTail m ell g))‖^2))≤ENNReal.ofReal ε := by
  intro ε hε
  let C := Real.pi/μ
  have hC : 0<C := div_pos Real.pi_pos hμ
  obtain ⟨N,hN⟩ := bounded_original_tail A g (Real.sqrt (ε/C))
    (Real.sqrt_pos.mpr (div_pos hε hC))
  refine ⟨N,fun m hm ell hell F => ?_⟩
  have he : (∫⁻ t : ℝ, ENNReal.ofReal
      (‖finiteResolvent F (line μ t) (A (relativeTail m ell g))‖^2))=
        ENNReal.ofReal (C*‖A (relativeTail m ell g)‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using
      actual_square_lintegral F μ hμ (A (relativeTail m ell g))
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have ht := hN m hm ell hell
  have hs := Real.sq_sqrt (div_pos hε hC).le
  have hb : ‖A (relativeTail m ell g)‖^2≤ε/C := by
    nlinarith [norm_nonneg (A (relativeTail m ell g)),Real.sqrt_nonneg (ε/C)]
  exact (mul_le_mul_of_nonneg_left hb hC.le).trans_eq (mul_div_cancel₀ ε hC.ne')

private theorem three_square (x y z : H) :
    ‖x+(y-z)‖^2≤3*(‖x‖^2+(‖y‖^2+‖z‖^2)) := by
  have hn := (norm_add_le x (y-z)).trans
    (add_le_add le_rfl (norm_sub_le y z))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖x‖-‖y‖),sq_nonneg (‖x‖-‖z‖),sq_nonneg (‖y‖-‖z‖)]

private theorem three_lintegral (f a b c : ℝ → H) (ha : Continuous a) (hb : Continuous b)
    (he : ∀ t, f t=a t+(b t-c t)) :
    (∫⁻ t, ENNReal.ofReal (‖f t‖^2))≤ENNReal.ofReal 3*
      ((∫⁻ t, ENNReal.ofReal (‖a t‖^2))+
        ((∫⁻ t, ENNReal.ofReal (‖b t‖^2))+(∫⁻ t, ENNReal.ofReal (‖c t‖^2)))) := by
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal 3*(ENNReal.ofReal (‖a t‖^2)+
        (ENNReal.ofReal (‖b t‖^2)+ENNReal.ofReal (‖c t‖^2))) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_add (sq_nonneg _) (by positivity),←ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by rw [he]; exact three_square _ _ _)
    _ = ENNReal.ofReal 3*(∫⁻ t, ENNReal.ofReal (‖a t‖^2)+
        (ENNReal.ofReal (‖b t‖^2)+ENNReal.ofReal (‖c t‖^2))) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      have hma : Measurable (fun t => ENNReal.ofReal (‖a t‖^2)) := by
        simpa only [Pi.pow_apply] using (ha.norm.pow 2).measurable.ennreal_ofReal
      have hmb : Measurable (fun t => ENNReal.ofReal (‖b t‖^2)) := by
        simpa only [Pi.pow_apply] using (hb.norm.pow 2).measurable.ennreal_ofReal
      rw [lintegral_add_left hma,lintegral_add_left hmb]

private theorem outer_energy_le (μ : ℝ) (hμ : 0<μ) (F : Index) (x : ℝ → H) :
    (∫⁻ t, ENNReal.ofReal (‖finiteResolvent F (line μ t) (x t)‖^2))≤
      ENNReal.ofReal (μ⁻¹^2)*(∫⁻ t, ENNReal.ofReal (‖x t‖^2)) := by
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (μ⁻¹^2)*ENNReal.ofReal (‖x t‖^2) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hn := (finiteResolvent F (line μ t)).le_opNorm (x t)
      have hr := line_resolvent_norm (GaussGradedCompression.compression F)
        (GaussGradedCompression.compression_selfAdjoint F) μ hμ t
      have hb := hn.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The original two-term source jet pays the frequency factor; integration precedes the filter. -/
theorem bounded_source_jet_full_frequency_tail (μ : ℝ) (hμ : 0<μ)
    (A : H →L[ℂ] H) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ t, ENNReal.ofReal (‖A (relativeTail m ell (finiteResolvent F (line μ t) (g : H)))+
          line μ t • finiteResolvent F (line μ t)
            (A (relativeTail m ell (finiteResolvent F (line μ t) (g : H))))‖^2))≤ENNReal.ofReal ε := by
  intro ε hε
  let C := 1+μ⁻¹^2
  let δ := ε/(6*C)
  have hC : 0<C := by dsimp [C]; positivity
  have hδ : 0<δ := div_pos hε (by positivity)
  let dg : diagonal.domain := ⟨diagonal g,diagonal_invariant g⟩
  obtain ⟨N₁,h₁⟩ := bounded_forcing_full_frequency_tail μ hμ A g δ hδ
  obtain ⟨N₂,h₂⟩ := bounded_forcing_full_frequency_tail μ hμ A dg δ hδ
  obtain ⟨N₃,h₃⟩ := fixed_forcing_uniform_energy_tail μ hμ A (g : H) (ε/6) (by positivity)
  refine ⟨max N₁ (max N₂ N₃),fun m hm ell hell => ?_⟩
  have hm₁ : N₁ ≤ m := (le_max_left _ _).trans hm
  have hm₂ : N₂ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm₃ : N₃ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  filter_upwards [h₁ m hm₁ ell hell,h₂ m hm₂ ell hell,actual_source_jet g] with F hF₁ hF₂ hjet
  have hF₃ := h₃ m hm₃ ell hell F
  have houter : (∫⁻ t, ENNReal.ofReal
      (‖finiteResolvent F (line μ t) (A (relativeTail m ell
        (finiteResolvent F (line μ t) (diagonal g))))‖^2))≤
          ENNReal.ofReal (μ⁻¹^2)*ENNReal.ofReal δ := by
    apply (outer_energy_le μ hμ F
      (fun t => A (relativeTail m ell (finiteResolvent F (line μ t) (diagonal g))))).trans
    gcongr
  have he (t : ℝ) :
      A (relativeTail m ell (finiteResolvent F (line μ t) (g : H)))+
          line μ t • finiteResolvent F (line μ t)
            (A (relativeTail m ell (finiteResolvent F (line μ t) (g : H))))=
      A (relativeTail m ell (finiteResolvent F (line μ t) (g : H)))+
        (finiteResolvent F (line μ t) (A (relativeTail m ell (finiteResolvent F (line μ t) (diagonal g))))-
          finiteResolvent F (line μ t) (A (relativeTail m ell (g : H)))) := by
    exact congrArg (fun x => A (relativeTail m ell (finiteResolvent F (line μ t) (g : H)))+x)
      (hjet (line μ t) (by simpa only [line_im] using hμ.ne') (A.comp (relativeTail m ell)))
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hcont (x : H) : Continuous (fun t =>
      A (relativeTail m ell (finiteResolvent F (line μ t) x))) :=
    A.continuous.comp ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const))
  apply (three_lintegral _ _ _ _ (hcont (g : H)) (hr.clm_apply (hcont (diagonal g))) he).trans
  calc
    _ ≤ ENNReal.ofReal 3*(ENNReal.ofReal δ+
        (ENNReal.ofReal (μ⁻¹^2)*ENNReal.ofReal δ+ENNReal.ofReal (ε/6))) := by
      gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (sq_nonneg _),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add hδ.le (by positivity),←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [δ,C]
      field_simp
      ring

theorem actual_hardy_retarded_tail (μ : ℝ) (hμ : 0<μ) (sharp : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ t, ENNReal.ofReal (‖particular sharp m ell F (line μ t) (g : H)+
          line μ t • finiteResolvent F (line μ t) (particular sharp m ell F (line μ t) (g : H))‖^2))≤
          ENNReal.ofReal ε :=
  bounded_source_jet_full_frequency_tail μ hμ (coefficientSolver sharp) g

private theorem actual_increment_core (sharp : Bool) (m ell : ℕ) (g : diagonal.domain) :
    SourceEscapeSeedTail.actualIncrement sharp m ell (g : H)∈diagonal.domain := by
  cases sharp
  · exact (SourceRetardedIncrement.incrementCore m ell g).property
  · exact diagonal.domain.sub_mem
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem ell g)
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem m g)

def incrementTest (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : GaussCoreDifferential.QuantumTest :=
  coreEquiv.symm ⟨SourceEscapeSeedTail.actualIncrement sharp m ell
    (finiteResolvent F z (g : H)),
    actual_increment_core sharp m ell (SourceEscapeCurrent.sourceCore F z hz g)⟩

theorem increment_test_embed (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : embed (incrementTest sharp m ell F z hz g)=
      SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H)) := by
  exact congrArg (fun x : diagonal.domain => (x : H)) (coreEquiv.apply_symm_apply _)

theorem particular_forcing (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : particular sharp m ell F z (g : H)=
      solver (embed (SourceCornerWeight.forcingAction (incrementTest sharp m ell F z hz g))) := by
  have hw := congrArg (fun T : H →L[ℂ] H => T (finiteResolvent F z (g : H)))
    (weighted_increment sharp m ell)
  change weighted (SourceEscapeSeedTail.actualIncrement sharp m ell
    (finiteResolvent F z (g : H)))=
      coefficientMap sharp (relativeTail m ell (finiteResolvent F z (g : H))) at hw
  change solver (coefficientMap sharp (relativeTail m ell (finiteResolvent F z (g : H))))=_
  rw [←hw,←increment_test_embed sharp m ell F z hz g]
  change solver (SourceCornerWeight.multiplier (GaussRadialDomain.inverseRadius
    (embed (incrementTest sharp m ell F z hz g))))=_
  rw [SourceCornerWeight.multiplier_inverse_core]

/-- The actual localized increment meets the generated particular; the full residual is retained. -/
theorem actual_localized_increment_splice (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (k : H) (finiteResolvent F z
      (embed (SourcePhysicalHardyWeight.localizedAction (incrementTest sharp m ell F z hz g))))=
      inner ℂ (k : H) (particular sharp m ell F z (g : H)+
        z • finiteResolvent F z (particular sharp m ell F z (g : H)))+
      inner ℂ (SourceKineticTranspose.outerResidual F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (particular sharp m ell F z (g : H)) := by
  rw [particular_forcing sharp m ell F z hz g]
  exact actual_localized_retarded_splice F z hz k (incrementTest sharp m ell F z hz g)

end LowEnergy.SourceHardyRetardedTail
