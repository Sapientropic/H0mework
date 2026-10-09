import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedWardPolarization
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard SourceScalarVirialBulk
open SourceScalarGaugeScale SourceClockPhiSecondBulk SourceResolventBandLimit
open FullYSourceResolventGraphSplice ActualMixedCovarianceTail ActualMixedWindowGram
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail SourceNativeCutoffContact
open ActualMixedContactReturn ActualMixedWardTail ActualMixedWardSource
open SourceMixedNativeReturn (sourceRead source_read_resolvent)
open ActualVectorJointCost SourceRelativePowerTail
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace ENNReal

elab "paid_whole_ward%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardTail 0) "LowEnergy") "ActualMixedWardTail"
  let name:=Name.str ns field.getId.eraseMacroScopes.toString
  unless (←getEnv).contains name do throwError "Missing actual whole Ward proof"
  mkConstWithFreshMVarLevels name

attribute [local irreducible] resolventCore deltaPhi deltaGauge secondJet coreWindow

private theorem causal_nonreal (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using hμ.ne'

/-- Hermitian polarization of the whole source Ward current, retaining both
ordered second-jet legs and every complex interference term. -/
def wardPair (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest) : ℂ :=
  let R:=resolventCore F z hz
  sourcePair (thetaAction m ell (deltaGauge R g)) (thetaAction m ell (deltaGauge R h))+
    sourcePair (thetaAction m ell ((deltaPhi R-deltaGauge R) g))
      (thetaAction m ell ((deltaPhi R-deltaGauge R) h))-
    sourcePair (thetaAction m ell (deltaPhi R g)) (thetaAction m ell (deltaPhi R h))+
    sourcePair (coreWindow m ell F z hz g) (thetaAction m ell (secondJet R h))+
    sourcePair (thetaAction m ell (secondJet R g)) (coreWindow m ell F z hz h)

theorem actual_pair_diagonal (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest) :
    wardPair m ell F z hz g g=(wardCurrent m ell F z hz g:ℂ) := by
  have hc (u v:H) : inner ℂ u v+inner ℂ v u=(2*(inner ℂ u v).re:ℝ) := by
    have hv:inner ℂ v u=star (inner ℂ u v) := (inner_conj_symm (𝕜:=ℂ) v u).symm
    calc
      _=inner ℂ u v+star (inner ℂ u v) := congrArg (fun x:ℂ=>inner ℂ u v+x) hv
      _=_ := Complex.add_conj _
  have hd (u:H):inner ℂ u u=(‖u‖^2:ℝ) := by
    calc
      _=((inner ℂ u u).re:ℂ) := (inner_self_ofReal_re (𝕜:=ℂ) u).symm
      _=_ := congrArg (fun x:ℝ=>(x:ℂ)) (inner_self_eq_norm_sq (𝕜:=ℂ) u)
  unfold wardPair wardCurrent sourcePair
  simp only [hd]
  rw [add_assoc (_-_) _ _,hc]
  push_cast
  ring

theorem actual_pair_hermitian (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest) :
    star (wardPair m ell F z hz h g)=wardPair m ell F z hz g h := by
  have hs (u v:H):star (inner ℂ u v)=inner ℂ v u := inner_conj_symm (𝕜:=ℂ) v u
  simp only [wardPair,sourcePair,star_add,star_sub,hs]
  ring

private theorem pair_add_left (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h k:QuantumTest):
    wardPair m ell F z hz (g+h) k=wardPair m ell F z hz g k+wardPair m ell F z hz h k := by
  simp only [wardPair,sourcePair,map_add,inner_add_left]
  ring
private theorem pair_add_right (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h k:QuantumTest):
    wardPair m ell F z hz g (h+k)=wardPair m ell F z hz g h+wardPair m ell F z hz g k := by
  simp only [wardPair,sourcePair,map_add,inner_add_right]
  ring
private theorem pair_sub_left (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h k:QuantumTest):
    wardPair m ell F z hz (g-h) k=wardPair m ell F z hz g k-wardPair m ell F z hz h k := by
  simp only [wardPair,sourcePair,map_sub,inner_sub_left]
  ring
private theorem pair_sub_right (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h k:QuantumTest):
    wardPair m ell F z hz g (h-k)=wardPair m ell F z hz g h-wardPair m ell F z hz g k := by
  simp only [wardPair,sourcePair,map_sub,inner_sub_right]
  ring
private theorem pair_smul_left (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(c:ℂ)(g h:QuantumTest):
    wardPair m ell F z hz (c • g) h=star c*wardPair m ell F z hz g h := by
  simp only [wardPair,sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
  ring
private theorem pair_smul_right (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(c:ℂ)(g h:QuantumTest):
    wardPair m ell F z hz g (c • h)=c*wardPair m ell F z hz g h := by
  simp only [wardPair,sourcePair,map_smul,inner_smul_right]
  ring

attribute [local irreducible] wardPair wardCurrent

/-- All four source superpositions are chosen before the moving cutoff and F. -/
theorem actual_pair_polarization (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest) :
    wardPair m ell F z hz g h=
      ((wardCurrent m ell F z hz (g+h):ℂ)-(wardCurrent m ell F z hz (g-h):ℂ)-
        Complex.I*((wardCurrent m ell F z hz (g+Complex.I • h):ℂ)-
          (wardCurrent m ell F z hz (g-Complex.I • h):ℂ)))/4 := by
  simp_rw [←actual_pair_diagonal]
  simp only [pair_add_left,pair_add_right,pair_sub_left,pair_sub_right,
    pair_smul_left,pair_smul_right,Complex.star_def,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem four_norm (a b c d:ℝ) :
    ‖((a:ℂ)-(b:ℂ)-Complex.I*((c:ℂ)-(d:ℂ)))/4‖ ≤ (|a|+|b|+|c|+|d|)/4 := by
  rw [norm_div]
  have h:=norm_sub_le ((a:ℂ)-(b:ℂ)) (Complex.I*((c:ℂ)-(d:ℂ)))
  have h₀:=norm_sub_le (a:ℂ) (b:ℂ)
  have h₁:=norm_sub_le (c:ℂ) (d:ℂ)
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at h h₀ h₁
  norm_num only [Complex.norm_ofNat]
  nlinarith only [h,h₀,h₁]

theorem actual_pair_price (m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g h:QuantumTest) :
    ‖wardPair m ell F z hz g h‖ ≤
      (|wardCurrent m ell F z hz (g+h)|+|wardCurrent m ell F z hz (g-h)|+
        |wardCurrent m ell F z hz (g+Complex.I • h)|+
        |wardCurrent m ell F z hz (g-Complex.I • h)|)/4 := by
  rw [actual_pair_polarization]
  exact four_norm _ _ _ _

private theorem ward_continuous (advanced:Bool)(μ:ℝ)(hμ:0 < μ)(m ell:ℕ)(F:Index)(g:QuantumTest) :
    Continuous (fun w:ℝ=>wardCurrent m ell F (causalFrequency advanced μ w)
      (causal_nonreal advanced μ hμ w) g) := by
  have hw (f:QuantumTest):Continuous (fun w:ℝ=>window m ell F (causalFrequency advanced μ w) f) :=
    (relativeTail m ell).continuous.comp
      (((paid_mixed_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const)
  have ha (f:QuantumTest):Continuous (fun w:ℝ=>embed (affineCutoff m ell
      (resolventCore F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) f))) := by
    have h:Continuous (fun w:ℝ=>sourceRead F (coreEquiv f) (affineCutoff m ell)
        (finiteResolvent F (causalFrequency advanced μ w) (embed f))) :=
      (sourceRead F (coreEquiv f) (affineCutoff m ell)).continuous.comp
        (((paid_mixed_tail% frequency_continuous) advanced μ hμ F).clm_apply continuous_const)
    convert h using 1
    funext w
    have he:(coreEquiv f:H)=embed f := rfl
    simpa only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,state,he] using
      (source_read_resolvent F (coreEquiv f) (affineCutoff m ell) _
        (causal_nonreal advanced μ hμ w)).symm
  have hcontact:=Complex.continuous_re.comp
    ((hw g).inner (𝕜:=ℂ) (ha ((2:ℂ) • g+(4:ℂ) • Gauge g)))
  have hcov:Continuous (fun w:ℝ=>mixedCovariance m ell F (causalFrequency advanced μ w) g) :=
    (paid_whole_ward% covariance_continuous) advanced μ hμ m ell F g
  refine (hcov.sub hcontact).congr (fun w=>?_)
  rw [actual_ward_source_return]
  simp only [Pi.sub_apply,Function.comp_def,contactRead,sourcePair,coreWindow,Module.End.mul_apply,
    (paid_mixed_core% window_core)]

theorem actual_pair_causal_tail (μ:ℝ)(hμ:0 < μ)(g h:QuantumTest) :
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        (∫⁻w:ℝ,ENNReal.ofReal ‖wardPair m ell F (causalFrequency advanced μ w)
          (causal_nonreal advanced μ hμ w) g h‖) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩:=actual_ward_causal_tail μ hμ (g+h) ε hε
  obtain ⟨N₁,h₁⟩:=actual_ward_causal_tail μ hμ (g-h) ε hε
  obtain ⟨N₂,h₂⟩:=actual_ward_causal_tail μ hμ (g+Complex.I • h) ε hε
  obtain ⟨N₃,h₃⟩:=actual_ward_causal_tail μ hμ (g-Complex.I • h) ε hε
  refine ⟨max (max N₀ N₁) (max N₂ N₃),fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml,
    h₂ m (by omega) ell hml,h₃ m (by omega) ell hml] with F hF₀ hF₁ hF₂ hF₃
  intro advanced
  let j (f:QuantumTest)(w:ℝ):=|wardCurrent m ell F (causalFrequency advanced μ w)
    (causal_nonreal advanced μ hμ w) f|
  have hj (f:QuantumTest):Measurable (fun w:ℝ=>ENNReal.ofReal (j f w)) :=
    ENNReal.measurable_ofReal.comp (ward_continuous advanced μ hμ m ell F f).abs.measurable
  have hp:=lintegral_mono (μ:=volume) (fun w:ℝ=>ENNReal.ofReal_le_ofReal
    (actual_pair_price m ell F (causalFrequency advanced μ w) (causal_nonreal advanced μ hμ w) g h))
  change _ ≤ ∫⁻w:ℝ,ENNReal.ofReal
    ((j (g+h) w+j (g-h) w+j (g+Complex.I • h) w+j (g-Complex.I • h) w)/4) at hp
  have hsum (w:ℝ):ENNReal.ofReal
      ((j (g+h) w+j (g-h) w+j (g+Complex.I • h) w+j (g-Complex.I • h) w)/4)=
      (ENNReal.ofReal (j (g+h) w)+ENNReal.ofReal (j (g-h) w)+
        ENNReal.ofReal (j (g+Complex.I • h) w)+ENNReal.ofReal (j (g-Complex.I • h) w))*
        ENNReal.ofReal ((4:ℝ)⁻¹) := by
    dsimp only [j]
    rw [div_eq_mul_inv,ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  simp_rw [hsum] at hp
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_right _ (hj _),lintegral_add_right _ (hj _),lintegral_add_right _ (hj _)] at hp
  apply hp.trans
  calc
    _ ≤ (ENNReal.ofReal ε+ENNReal.ofReal ε+ENNReal.ofReal ε+ENNReal.ofReal ε)*ENNReal.ofReal ((4:ℝ)⁻¹) := by
      gcongr <;> first | exact hF₀ advanced | exact hF₁ advanced | exact hF₂ advanced | exact hF₃ advanced
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add hε.le hε.le,←ENNReal.ofReal_add (by positivity) hε.le,
        ←ENNReal.ofReal_add (by positivity) hε.le,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end LowEnergy.ActualMixedWardPolarization
