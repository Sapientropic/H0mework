import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaNormalizedResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialNormalizedMixedTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaOperator
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaTail
open SourceClockYukawaRadialMixedGamma SourceRelativePowerTail SourceRetardedForcingTail SourceHardyRetardedTail
open SourceClockYukawaRadialMixedBudget SourceClockYukawaNormalizedCurrent SourceCutoffDilationWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev Op := H →L[ℂ] H
attribute [local irreducible] fullAction state compressionCore defectAction inverseRadius sourceB
  SourceClockYukawaRadialMixedGamma.mixedResponse

private theorem left_cancel_source {A : Type*} [Ring A] (L R S X B M : A)
    (hL : L*R=1) (hSX : S*X=B)
    (h : R*X*R*S=R^2*B-R*S*R*X+R*B*R-R*M) :
    S*M=S*R*B-S^2*R*X-B*R*S+S*B*R := by
  have hf : R*M=R*(R*B-S*R*X+B*R-X*R*S) := by
    linear_combination (norm := noncomm_ring) h
  have hm := congrArg (fun T : A => L*T) hf
  simp only [←mul_assoc,hL,one_mul] at hm
  rw [hm]
  linear_combination (norm := noncomm_ring) -hSX*R*S

private theorem inverse_increment (sharp : Bool) (m ell : ℕ) :
    inverseRadius*actualIncrement sharp m ell=sourceB sharp*relativeTail m ell := by
  apply GaussYukawaGrade.core_ext
  intro f
  change inverseRadius (actualIncrement sharp m ell (embed f))=
    sourceB sharp (relativeTail m ell (embed f))
  rw [literal_increment_core,literal_full_return,Module.End.mul_apply,inverse_core,
    SourceMixedNativeReturn.theta_core]
  simpa only [normalizedAction,Module.End.mul_apply] using
    (original_normalized_core sharp (thetaAction m ell f)).symm

/-- Multiplying the actual whole M by its own source inverse-radius exits every unbounded outer Y leg. -/
theorem actual_normalized_mixed_operator (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) :
    inverseRadius*mixedResponse sharp m ell F z=
      inverseRadius*finiteResolvent F z*(sourceB sharp*relativeTail m ell)-
      inverseRadius^2*finiteResolvent F z*actualIncrement sharp m ell-
      (sourceB sharp*relativeTail m ell)*finiteResolvent F z*inverseRadius+
      inverseRadius*(sourceB sharp*relativeTail m ell)*finiteResolvent F z := by
  have hL : (GaussGradedCompression.compression F-z • 1)*finiteResolvent F z=1 := by
    simpa only [finiteResolvent] using resolvent_right (GaussGradedCompression.compression F)
      (GaussGradedCompression.compression_selfAdjoint F) z hz
  exact left_cancel_source _ _ _ _ _ _ hL (inverse_increment sharp m ell)
    (actual_mixed_gamma_operator sharp m ell F z hz)

private theorem radius_source_inverse (g : diagonal.domain) : inverseRadius (radiusSource g:H)=(g:H) := by
  change inverseRadius (embed (radiusAction (coreEquiv.symm g)))=_
  rw [inverse_core,inverse_radius_action]
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply g)

private theorem increment_fixed (sharp : Bool) (m ell : ℕ) (h : diagonal.domain) :
    actualIncrement sharp m ell (h:H)=relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp h:H) := by
  have hy : Commute (fullAction sharp) inverseAction := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes
    · exact GaussRadialHamiltonian.adjoint_commutes
  have ht : Commute (fullAction sharp) (thetaAction m ell) := by
    unfold thetaAction
    exact (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _).sub_right
      (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _)
  have he : embed (coreEquiv.symm h)=(h:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply h)
  have hc := LinearMap.congr_fun ht.eq (coreEquiv.symm h)
  change fullAction sharp (thetaAction m ell (coreEquiv.symm h))=
    thetaAction m ell (fullAction sharp (coreEquiv.symm h)) at hc
  rw [←he,literal_increment_core,literal_full_return,Module.End.mul_apply,hc,←SourceMixedNativeReturn.theta_core]
  rfl

def normalizedMixedVector (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (g : diagonal.domain) : H :=
  inverseRadius (mixedResponse sharp m ell F z (radiusSource g:H))

private theorem actual_fixed_normalized_mixed (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    normalizedMixedVector sharp m ell F z g=
      inverseRadius (finiteResolvent F z (sourceB sharp (relativeTail m ell (radiusSource g:H))))-
      (inverseRadius^2) (finiteResolvent F z
        (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H)))-
      sourceB sharp (relativeTail m ell (finiteResolvent F z (g:H)))+
      inverseRadius (sourceB sharp (relativeTail m ell (finiteResolvent F z (radiusSource g:H)))) := by
  have h := congrArg (fun T : Op => T (radiusSource g:H))
    (actual_normalized_mixed_operator sharp m ell F z hz)
  simp only [mul_apply_eq_comp,sub_apply,add_apply,radius_source_inverse,increment_fixed] at h
  exact h

attribute [local irreducible] normalizedMixedVector

private theorem two_square (x y : H) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private theorem four_square (x y z t : H) :
    ‖x-y-z+t‖^2 ≤ 4*‖x‖^2+4*‖y‖^2+4*‖z‖^2+4*‖t‖^2 := by
  have he : x-y-z+t=(x-y)-(z-t) := by abel
  rw [he]
  nlinarith only [two_square (x-y) (z-t),two_square x y,two_square z t]

private def firstPrice : ℝ := 4*‖inverseRadius‖^2
private def secondPrice : ℝ := 4*‖inverseRadius^2‖^2

attribute [local irreducible] firstPrice secondPrice

private theorem ofReal_four (p q x y z t : ℝ) (hp : 0≤p) (hq : 0≤q) :
    ENNReal.ofReal (p*x+q*y+4*z+p*t) ≤
      ENNReal.ofReal p*ENNReal.ofReal x+ENNReal.ofReal q*ENNReal.ofReal y+
      ENNReal.ofReal (4:ℝ)*ENNReal.ofReal z+ENNReal.ofReal p*ENNReal.ofReal t := by
  apply (ENNReal.ofReal_add_le.trans (add_le_add
    (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le (le_refl _))) (le_refl _))).trans
  rw [ENNReal.ofReal_mul hp,ENNReal.ofReal_mul hq,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),
    ENNReal.ofReal_mul hp]

private theorem vector_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖normalizedMixedVector sharp m ell F z g‖^2 ≤
      firstPrice*‖finiteResolvent F z (sourceB sharp (relativeTail m ell (radiusSource g:H)))‖^2+
      secondPrice*‖finiteResolvent F z (relativeTail m ell
        (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H))‖^2+
      4*‖sourceB sharp (relativeTail m ell (finiteResolvent F z (g:H)))‖^2+
      firstPrice*‖sourceB sharp (relativeTail m ell (finiteResolvent F z (radiusSource g:H)))‖^2 := by
  let X := finiteResolvent F z (sourceB sharp (relativeTail m ell (radiusSource g:H)))
  let Y := finiteResolvent F z (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H))
  let Z := sourceB sharp (relativeTail m ell (finiteResolvent F z (g:H)))
  let T := sourceB sharp (relativeTail m ell (finiteResolvent F z (radiusSource g:H)))
  have h := four_square (inverseRadius X) ((inverseRadius^2) Y) Z (inverseRadius T)
  have hX := pow_le_pow_left₀ (norm_nonneg _) (inverseRadius.le_opNorm X) 2
  have hY := pow_le_pow_left₀ (norm_nonneg _) ((inverseRadius^2).le_opNorm Y) 2
  have hT := pow_le_pow_left₀ (norm_nonneg _) (inverseRadius.le_opNorm T) 2
  simp only [mul_pow] at hX hY hT
  rw [actual_fixed_normalized_mixed sharp m ell F z hz]
  change ‖inverseRadius X-(inverseRadius^2) Y-Z+inverseRadius T‖^2 ≤ _
  unfold firstPrice secondPrice
  nlinarith only [h,hX,hY,hT]

private theorem normalized_mixed_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖normalizedMixedVector sharp m ell F (line μ w) g‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := 2*firstPrice+secondPrice+4
  have hP : 0 ≤ firstPrice := by unfold firstPrice;positivity
  have hQ : 0 ≤ secondPrice := by unfold secondPrice;positivity
  have hC : 0 ≤ C := by dsimp only [C];positivity
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨N₁,h₁⟩ := fixed_forcing_uniform_energy_tail μ hμ (sourceB sharp) (radiusSource g:H) δ hδ
  obtain ⟨N₂,h₂⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:Op)
    (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H) δ hδ
  obtain ⟨N₃,h₃⟩ := bounded_forcing_full_frequency_tail μ hμ (sourceB sharp) g δ hδ
  obtain ⟨N₄,h₄⟩ := bounded_forcing_full_frequency_tail μ hμ (sourceB sharp) (radiusSource g) δ hδ
  refine ⟨max N₁ (max N₂ (max N₃ N₄)),fun m hm ell hml => ?_⟩
  filter_upwards [h₃ m (by omega) ell hml,h₄ m (by omega) ell hml] with F hz ht
  have hx := h₁ m (by omega) ell hml F
  have hy := h₂ m (by omega) ell hml F
  simp only [one_apply_eq_self] at hy
  let X (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w)
    (sourceB sharp (relativeTail m ell (radiusSource g:H)))‖^2)
  let Y (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w)
    (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp (radiusSource g):H))‖^2)
  let Z (w : ℝ) := ENNReal.ofReal (‖sourceB sharp (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))‖^2)
  let T (w : ℝ) := ENNReal.ofReal (‖sourceB sharp (relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H)))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hymeas : Measurable (fun w => ENNReal.ofReal secondPrice*Y w) :=
    ((((hr.clm_apply continuous_const).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  have hzmeas : Measurable (fun w => ENNReal.ofReal (4:ℝ)*Z w) :=
    (((((sourceB sharp).continuous.comp ((relativeTail m ell).continuous.comp
      (hr.clm_apply continuous_const))).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  have htmeas : Measurable (fun w => ENNReal.ofReal firstPrice*T w) :=
    (((((sourceB sharp).continuous.comp ((relativeTail m ell).continuous.comp
      (hr.clm_apply continuous_const))).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal firstPrice*X w+ENNReal.ofReal secondPrice*Y w+
        ENNReal.ofReal (4:ℝ)*Z w+ENNReal.ofReal firstPrice*T w := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y,Z,T]
      apply (ENNReal.ofReal_le_ofReal (vector_bound sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)).trans
      exact ofReal_four firstPrice secondPrice _ _ _ _ hP hQ
    _ = ENNReal.ofReal firstPrice*(∫⁻ w : ℝ,X w)+ENNReal.ofReal secondPrice*(∫⁻ w : ℝ,Y w)+
        ENNReal.ofReal (4:ℝ)*(∫⁻ w : ℝ,Z w)+ENNReal.ofReal firstPrice*(∫⁻ w : ℝ,T w) := by
      rw [lintegral_add_right _ htmeas,lintegral_add_right _ hzmeas,lintegral_add_right _ hymeas,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal firstPrice*ENNReal.ofReal δ+ENNReal.ofReal secondPrice*ENNReal.ofReal δ+
        ENNReal.ofReal (4:ℝ)*ENNReal.ofReal δ+ENNReal.ofReal firstPrice*ENNReal.ofReal δ := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have he : firstPrice*δ+secondPrice*δ+4*δ+firstPrice*δ=C*(ε/(C+1)) := by dsimp only [C,δ];ring
      rw [he,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<C+1)).mpr
      nlinarith

/-- The complete original mixed response has a source inverse-radius tail on both sharp branches at one cutoff. -/
theorem actual_normalized_mixed_response_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        (∫⁻ w : ℝ,ENNReal.ofReal (‖normalizedMixedVector sharp m ell F (line μ w) g‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := normalized_mixed_common_tail false μ hμ g ε hε
  obtain ⟨N₁,h₁⟩ := normalized_mixed_common_tail true μ hμ g ε hε
  refine ⟨max N₀ N₁,fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hf ht sharp
  cases sharp
  · exact hf
  · exact ht

end LowEnergy.SourceClockYukawaRadialNormalizedMixedTail
