import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourcePairedMomentumFlux
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCurrentEndpointEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarDoubleEndpoint
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussDiagonalHistory GaussUnitaryHistory SourceMixedNativeReturn
open SourceCutoffDilationWard SourceRelativePowerTail SourceCurrentEndpointEnergy
open SourceRetardedIncrement FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceHardyRetardedTail SourceFixedJetBudget SourceEscapeCurrent SourceJointScaleBudget
open scoped Topology InnerProductSpace

abbrev CoreEnd := SourceCoframeVolumeCurrent.CoreEnd

def fullInsertion (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  SourceMixedNativeReturn.fullAction sharp*SourceMixedNativeReturn.thetaAction m ell

def doubleResponse (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) : ℂ :=
  let C := GaussGradedCompression.compression F
  let X := sourceRead F g (fullInsertion sharp m ell)
  inner ℂ (k : H) (finiteResolvent F z
    ((C*(C*X-X*C)-(C*X-X*C)*C) (finiteResolvent F z (g : H))))

private theorem source_read_full (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) :
    sourceRead F g (fullInsertion sharp m ell)=
      SourceEscapeSeedTail.actualIncrement sharp m ell*(inputSpan F g).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  let q := coreEquiv.symm (Submodule.inclusion (input_span_core F g)
    ((inputSpan F g).orthogonalProjectionOnto x))
  have h := literal_increment_core sharp m ell q
  have hf := congrArg embed (LinearMap.congr_fun (literal_full_return sharp m ell) q)
  have hq : embed q=(inputSpan F g).starProjection x :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply
      (Submodule.inclusion (input_span_core F g) ((inputSpan F g).orthogonalProjectionOnto x)))
  change embed (fullInsertion sharp m ell q)=
    SourceEscapeSeedTail.actualIncrement sharp m ell ((inputSpan F g).starProjection x)
  rw [←hq]
  exact hf.symm.trans h.symm

private theorem relative_power_commute {R : Type*} [Ring R] (a u : R) (m ell : ℕ)
    (h : Commute a u) : Commute a ((1-u)^(m+1)-(1-u)^(ell+1)) :=
  (((Commute.one_right a).sub_right h).pow_right (m+1)).sub_right
    (((Commute.one_right a).sub_right h).pow_right (ell+1))

private theorem full_theta_commute (sharp : Bool) (m ell : ℕ) :
    Commute (SourceMixedNativeReturn.fullAction sharp) (SourceMixedNativeReturn.thetaAction m ell) := by
  have h : Commute (SourceMixedNativeReturn.fullAction sharp) GaussRadialDomain.inverseAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    cases sharp
    · change GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z)
        ((GaussRadialDomain.reciprocal z : ℂ) • f z)=
        (GaussRadialDomain.reciprocal z : ℂ) • GaussYukawaCoefficient.sourceMap
          (GaussNativePotential.scalarField z) (f z)
      exact map_smul _ _ _
    · change GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z)
        ((GaussRadialDomain.reciprocal z : ℂ) • f z)=
        (GaussRadialDomain.reciprocal z : ℂ) • GaussFullHamiltonian.adjointMap
          (GaussNativePotential.scalarField z) (f z)
      exact map_smul _ _ _
  exact relative_power_commute (R := SourceCoframeVolumeCurrent.CoreEnd) _ _ m ell h

/-- The original literal insertion tail is paid on each fixed original source. -/
theorem actual_full_fixed_tail (sharp : Bool) (f : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖SourceEscapeSeedTail.actualIncrement sharp m ell (embed f)‖<ε := by
  have he (m ell : ℕ) : SourceEscapeSeedTail.actualIncrement sharp m ell (embed f)=
      relativeTail m ell (embed (SourceMixedNativeReturn.fullAction sharp f)) := by
    rw [literal_increment_core]
    have h := LinearMap.congr_fun ((literal_full_return sharp m ell).trans
      (full_theta_commute sharp m ell).eq) f
    exact (congrArg embed h).trans (theta_core m ell _).symm
  simpa only [he] using! original_relative_tail (embed (SourceMixedNativeReturn.fullAction sharp f))

private theorem double_projection {R : Type*} [Ring R] (c b p : R)
    (hpc : p*c=c) (hcp : c*p=c) :
    c*(c*(b*p)-(b*p)*c)-(c*(b*p)-(b*p)*c)*c=
      (c*(c*b-b*c)-(c*b-b*c)*c)*p := by
  have hcpc : c*p*c=c*c := by rw [hcp]
  noncomm_ring [hpc,hcp,hcpc]

private theorem double_endpoint {R : Type*} [Ring R] (c r a z : R)
    (hcr : c*r=r*c) (hz : Commute z a)
    (hl : r*(c-z)=1) (hr : (c-z)*r=1) :
    r*(c*(c*a-a*c)-(c*a-a*c)*c)*r=
      c*a*r-c*r*a-a*r*c+r*a*c := by
  have h0 : c*a-a*c=(c-z)*a-a*(c-z) := by rw [sub_mul,mul_sub,hz.eq]; abel
  have h1 : r*(c*a-a*c)*r=a*r-r*a := by
    calc
      _ = (r*(c-z))*a*r-r*a*((c-z)*r) := by rw [h0]; noncomm_ring
      _ = _ := by rw [hl,hr,one_mul,mul_one]
  calc
    _ = (r*c)*(c*a-a*c)*r-(r*(c*a-a*c))*(c*r) := by noncomm_ring
    _ = (c*r)*(c*a-a*c)*r-(r*(c*a-a*c))*(r*c) :=
      congrArg₂ (fun x y : R => x-y)
        (congrArg (fun x : R => x*(c*a-a*c)*r) hcr.symm)
        (congrArg (fun x : R => (r*(c*a-a*c))*x) hcr)
    _ = c*(r*(c*a-a*c)*r)-(r*(c*a-a*c)*r)*c := by noncomm_ring
    _ = _ := by rw [h1]; noncomm_ring

private theorem projection_compression (F : Index) (g : diagonal.domain) :
    (inputSpan F g).starProjection*GaussGradedCompression.compression F=
      GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  change ((inputSpan F g).orthogonalProjectionOnto
    (GaussGradedCompression.compression F x) : H)=GaussGradedCompression.compression F x
  exact congrArg Subtype.val ((inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,
      Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F x)⟩)

private theorem compression_projection (F : Index) (g : diagonal.domain) :
    GaussGradedCompression.compression F*(inputSpan F g).starProjection=
      GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have hy : GaussGradedCompression.compression F y∈inputSpan F g :=
    Submodule.mem_sup_left (SourceRetardedIncrement.compression_mem_support F y)
  exact (GaussGradedCompression.compression_pair F y _).symm.trans
    ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨GaussGradedCompression.compression F y,hy⟩ x).trans
        (GaussGradedCompression.compression_pair F y x))

private theorem increment_adjoint (sharp : Bool) (m ell : ℕ) :
    (SourceEscapeSeedTail.actualIncrement sharp m ell).adjoint=
      SourceEscapeSeedTail.actualIncrement (!sharp) m ell := by
  cases sharp <;> simp [SourceEscapeSeedTail.actualIncrement,
    SourceEscapeSeedTail.sharpIncrement,SourceRetardedIncrement.increment,map_sub]

private theorem resolvent_commutes (F : Index) (z : ℂ) (hz : z.im≠0) :
    GaussGradedCompression.compression F*finiteResolvent F z=
      finiteResolvent F z*GaussGradedCompression.compression F := by
  have h := resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz
  rw [sub_mul,smul_mul_assoc,one_mul] at h
  exact (sub_eq_iff_eq_add.mp h).trans
    (resolvent_compression _ (GaussGradedCompression.compression_selfAdjoint F) z hz).symm

private theorem projected_endpoints {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (c r b p : E →L[ℂ] E) (g k : E) (z : ℂ)
    (hpc : p*c=c) (hcp : c*p=c) (hp : p (r g)=r g) (hcr : c*r=r*c)
    (hl : r*(c-z • 1)=1) (hr : (c-z • 1)*r=1)
    (hc : ∀ x y : E, inner ℂ (c x) y=inner ℂ x (c y)) :
    inner ℂ k (r ((c*(c*(b*p)-(b*p)*c)-(c*(b*p)-(b*p)*c)*c) (r g)))=
      inner ℂ (b.adjoint (c k)) (r g)-inner ℂ (c k) (r (b g))-
      inner ℂ (b.adjoint k) (r (c g))+inner ℂ k (r (b (c g))) := by
  have hd := congrArg (fun A : E →L[ℂ] E => A (r g)) (double_projection c b p hpc hcp)
  change _=(c*(c*b-b*c)-(c*b-b*c)*c) (p (r g)) at hd
  rw [hp] at hd
  have he := congrArg (fun A : E →L[ℂ] E => inner ℂ k (A g))
    (double_endpoint c r b (z • 1) hcr ((Commute.one_left b).smul_left z) hl hr)
  change inner ℂ k (r ((c*(c*b-b*c)-(c*b-b*c)*c) (r g)))=
    inner ℂ k (c (b (r g))-c (r (b g))-b (r (c g))+r (b (c g))) at he
  rw [inner_add_right,inner_sub_right,inner_sub_right] at he
  have h1 : inner ℂ k (c (b (r g)))=inner ℂ (b.adjoint (c k)) (r g) :=
    (hc k (b (r g))).symm.trans (ContinuousLinearMap.adjoint_inner_left b (r g) (c k)).symm
  have h2 : inner ℂ k (c (r (b g)))=inner ℂ (c k) (r (b g)) := (hc k (r (b g))).symm
  have h3 : inner ℂ k (b (r (c g)))=inner ℂ (b.adjoint k) (r (c g)) :=
    (ContinuousLinearMap.adjoint_inner_left b (r (c g)) k).symm
  have ht := congrArg (fun a : ℂ => a+inner ℂ k (r (b (c g))))
    (congrArg₂ (fun a b : ℂ => a-b) (congrArg₂ (fun a b : ℂ => a-b) h1 h2) h3)
  exact (congrArg (fun x : E => inner ℂ k (r x)) hd).trans (he.trans ht)

/-- The full literal insertion returns to four source endpoints, including both compression jets. -/
theorem actual_double_endpoints (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    doubleResponse sharp m ell F g k z=
      inner ℂ (SourceEscapeSeedTail.actualIncrement (!sharp) m ell
        (GaussGradedCompression.compression F (k : H))) (finiteResolvent F z (g : H))-
      inner ℂ (GaussGradedCompression.compression F (k : H))
        (finiteResolvent F z (SourceEscapeSeedTail.actualIncrement sharp m ell (g : H)))-
      inner ℂ (SourceEscapeSeedTail.actualIncrement (!sharp) m ell (k : H))
        (finiteResolvent F z (GaussGradedCompression.compression F (g : H)))+
      inner ℂ (k : H) (finiteResolvent F z (SourceEscapeSeedTail.actualIncrement sharp m ell
        (GaussGradedCompression.compression F (g : H)))) := by
  let C := GaussGradedCompression.compression F
  let R := finiteResolvent F z
  let B := SourceEscapeSeedTail.actualIncrement sharp m ell
  let P := (inputSpan F g).starProjection
  have hp : P (R (g : H))=R (g : H) := by
    exact congrArg Subtype.val ((inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self
      ⟨R (g : H),resolvent_input_span F z hz g⟩)
  have h0 := congrArg (fun A : H →L[ℂ] H => inner ℂ (k : H)
    (R ((C*(C*A-A*C)-(C*A-A*C)*C) (R (g : H))))) (source_read_full sharp m ell F g)
  have h1 := projected_endpoints (E := H) C R B P (g : H) (k : H) z
    (projection_compression F g) (compression_projection F g) hp (resolvent_commutes F z hz)
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    (GaussGradedCompression.compression_pair F)
  have h2 := congrArg (fun A : H →L[ℂ] H =>
    inner ℂ (A (C (k : H))) (R (g : H))-inner ℂ (C (k : H)) (R (B (g : H)))-
      inner ℂ (A (k : H)) (R (C (g : H)))+inner ℂ (k : H) (R (B (C (g : H)))))
    (increment_adjoint sharp m ell)
  exact (h0.trans h1).trans h2

private theorem profile_lintegral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (r : ℝ → E →L[ℂ] E) (x y : E) (K : ℝ)
    (hr : (∫⁻ w : ℝ, ENNReal.ofReal (‖r w y‖^2))=ENNReal.ofReal (K*‖y‖^2)) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖inner ℂ x (r w y)‖^2)) ≤
      ENNReal.ofReal (K*‖x‖^2*‖y‖^2) := by
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal (‖x‖^2)*
        ENNReal.ofReal (‖r w y‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ) x (r w y)) 2
    _ = ENNReal.ofReal (‖x‖^2)*ENNReal.ofReal (K*‖y‖^2) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hr]
    _ = _ := by rw [←ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring

private theorem four_square (a b c d : ℂ) :
    ‖a-b-c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have h : ‖a-b-c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    linarith [norm_add_le (a-b-c) d,norm_sub_le (a-b) c,norm_sub_le a b]
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (‖b‖-‖c‖),sq_nonneg (‖b‖-‖d‖),sq_nonneg (‖c‖-‖d‖)]

private theorem profile_measurable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (r : ℝ → E →L[ℂ] E) (x y : E) (hr : Continuous r) :
    Measurable (fun w : ℝ => ENNReal.ofReal
      (‖inner ℂ x (r w y)‖^2)) :=
  ((continuous_const.inner (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal

private theorem four_profile_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : ℝ → E →L[ℂ] E) (f : ℝ → ℂ) (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : E) (K : ℝ)
    (hK : 0 ≤ K) (hr : Continuous r)
    (hn : ∀ y : E, (∫⁻ w : ℝ, ENNReal.ofReal (‖r w y‖^2))=ENNReal.ofReal (K*‖y‖^2))
    (he : ∀ w, f w=inner ℂ x₁ (r w y₁)-inner ℂ x₂ (r w y₂)-
      inner ℂ x₃ (r w y₃)+inner ℂ x₄ (r w y₄)) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖f w‖^2)) ≤
      ENNReal.ofReal ((4*K)*(‖x₁‖^2*‖y₁‖^2+‖x₂‖^2*‖y₂‖^2+
        ‖x₃‖^2*‖y₃‖^2+‖x₄‖^2*‖y₄‖^2)) := by
  let e (x y : E) (w : ℝ) := ENNReal.ofReal (‖inner ℂ x (r w y)‖^2)
  have hm (x y : E) : Measurable (e x y) := profile_measurable r x y hr
  have hb (x y : E) := profile_lintegral r x y K (hn y)
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 4*(e x₁ y₁ w+e x₂ y₂ w+e x₃ y₃ w+e x₄ y₄ w) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [he w]
      dsimp only [e]
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_add (by positivity) (sq_nonneg _),
        ←ENNReal.ofReal_add (by positivity) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      exact ENNReal.ofReal_le_ofReal (four_square _ _ _ _)
    _ = ENNReal.ofReal 4*((∫⁻ w : ℝ, e x₁ y₁ w)+(∫⁻ w : ℝ, e x₂ y₂ w)+
        (∫⁻ w : ℝ, e x₃ y₃ w)+(∫⁻ w : ℝ, e x₄ y₄ w)) := by
      have hm12 : Measurable (fun w => e x₁ y₁ w+e x₂ y₂ w) := (hm x₁ y₁).add (hm x₂ y₂)
      have hm123 : Measurable (fun w => e x₁ y₁ w+e x₂ y₂ w+e x₃ y₃ w) := hm12.add (hm x₃ y₃)
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left hm123,lintegral_add_left hm12,lintegral_add_left (hm x₁ y₁)]
    _ ≤ ENNReal.ofReal 4*(ENNReal.ofReal (K*‖x₁‖^2*‖y₁‖^2)+
        ENNReal.ofReal (K*‖x₂‖^2*‖y₂‖^2)+ENNReal.ofReal (K*‖x₃‖^2*‖y₃‖^2)+
        ENNReal.ofReal (K*‖x₄‖^2*‖y₄‖^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add
        (hb x₁ y₁) (hb x₂ y₂)) (hb x₃ y₃)) (hb x₄ y₄)) (by positivity)
    _ = _ := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

/-- The frequency integral is paid before any cofinal limit; each compression is on a source endpoint. -/
theorem actual_double_energy (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖doubleResponse sharp m ell F g k (line μ w)‖^2)) ≤
      ENNReal.ofReal ((4*(Real.pi/μ))*(
        ‖SourceEscapeSeedTail.actualIncrement (!sharp) m ell
          (GaussGradedCompression.compression F (k : H))‖^2*‖(g : H)‖^2+
        ‖GaussGradedCompression.compression F (k : H)‖^2*
          ‖SourceEscapeSeedTail.actualIncrement sharp m ell (g : H)‖^2+
        ‖SourceEscapeSeedTail.actualIncrement (!sharp) m ell (k : H)‖^2*
          ‖GaussGradedCompression.compression F (g : H)‖^2+
        ‖(k : H)‖^2*‖SourceEscapeSeedTail.actualIncrement sharp m ell
          (GaussGradedCompression.compression F (g : H))‖^2)) := by
  let x₁ := SourceEscapeSeedTail.actualIncrement (!sharp) m ell (GaussGradedCompression.compression F (k : H))
  let y₁ := (g : H)
  let x₂ := GaussGradedCompression.compression F (k : H)
  let y₂ := SourceEscapeSeedTail.actualIncrement sharp m ell (g : H)
  let x₃ := SourceEscapeSeedTail.actualIncrement (!sharp) m ell (k : H)
  let y₃ := GaussGradedCompression.compression F (g : H)
  let x₄ := (k : H)
  let y₄ := SourceEscapeSeedTail.actualIncrement sharp m ell (GaussGradedCompression.compression F (g : H))
  have hn (y : H) : (∫⁻ w : ℝ, ENNReal.ofReal (‖finiteResolvent F (line μ w) y‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖y‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ y
  exact four_profile_energy (E := H) (fun w => finiteResolvent F (line μ w))
    (fun w => doubleResponse sharp m ell F g k (line μ w)) x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄
    (Real.pi/μ) (by positivity) (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F) hn
    (fun w => actual_double_endpoints sharp m ell F g k _ (by simpa only [line_im] using hμ.ne'))

/-- A single cutoff threshold pays every upper cutoff and the original whole-frequency double current. -/
theorem actual_double_tail (sharp : Bool) (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖doubleResponse sharp m ell F g k (line μ w)‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  let B := 4*(Real.pi/μ)
  let C := B*(1+‖(g : H)‖^2+‖diagonal k‖^2+‖diagonal g‖^2+‖(k : H)‖^2)
  have hB : 0<B := by dsimp [B]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  let δ := Real.sqrt (ε/C)
  have hδ : 0<δ := Real.sqrt_pos.mpr (div_pos hε hC)
  have hδ2 : δ^2=ε/C := Real.sq_sqrt (div_pos hε hC).le
  let hk : diagonal.domain := ⟨diagonal k,diagonal_invariant k⟩
  let hg : diagonal.domain := ⟨diagonal g,diagonal_invariant g⟩
  have core_embed (f : diagonal.domain) : embed (coreEquiv.symm f)=(f : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply f)
  obtain ⟨N₁,h₁⟩ := actual_full_fixed_tail (!sharp) (coreEquiv.symm hk) δ hδ
  obtain ⟨N₂,h₂⟩ := actual_full_fixed_tail sharp (coreEquiv.symm g) δ hδ
  obtain ⟨N₃,h₃⟩ := actual_full_fixed_tail (!sharp) (coreEquiv.symm k) δ hδ
  obtain ⟨N₄,h₄⟩ := actual_full_fixed_tail sharp (coreEquiv.symm hg) δ hδ
  refine ⟨max (max N₁ N₂) (max N₃ N₄),fun m hm ell hell => ?_⟩
  have h1 := pow_le_pow_left₀ (norm_nonneg _)
    (h₁ m (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hm) ell hell).le 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _)
    (h₂ m (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hm) ell hell).le 2
  have h3 := pow_le_pow_left₀ (norm_nonneg _)
    (h₃ m (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hm) ell hell).le 2
  have h4 := pow_le_pow_left₀ (norm_nonneg _)
    (h₄ m (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hm) ell hell).le 2
  simp only [core_embed] at h1 h2 h3 h4
  filter_upwards [GaussGradedCompression.eventually_exact g,
    GaussGradedCompression.eventually_exact k] with F hFg hFk
  apply (actual_double_energy sharp m ell F g k μ hμ).trans
  apply ENNReal.ofReal_le_ofReal
  rw [hFg,hFk]
  calc
    _ ≤ B*(δ^2*‖(g : H)‖^2+‖diagonal k‖^2*δ^2+
        δ^2*‖diagonal g‖^2+‖(k : H)‖^2*δ^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
        (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)))
        (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left h4 (sq_nonneg _))) hB.le
    _ ≤ C*δ^2 := by dsimp [C]; nlinarith [mul_nonneg hB.le (sq_nonneg δ)]
    _ = ε := by rw [hδ2,mul_div_cancel₀ ε hC.ne']

end LowEnergy.SourceScalarDoubleEndpoint
