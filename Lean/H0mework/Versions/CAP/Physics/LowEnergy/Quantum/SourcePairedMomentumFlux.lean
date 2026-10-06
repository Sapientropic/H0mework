import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourcePairedRadialFlux
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceMovingJetFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourcePairedMomentumFlux
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussHistoryHilbert
open GaussYukawaCoefficient GaussRadialDomain SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceScalarPairedTransport SourcePairedRadialFlux SourceMixedNativeReturn SourceMovingJetFlux
open SourceGammaNativeBudget SourceEscapeCurrent SourceMinimalGraphParticular SourceClosedCostNativeProbe
open SourceCurrentEndpointEnergy SourceDilationRemainder SourceHamiltonianScaleJet
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace BigOperators Topology

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

private theorem end_sum_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (d : Module.End ℂ V) (a : ι → Module.End ℂ V)
    (h : ∀ i, Commute d (a i)) : Commute d (∑ i,a i) :=
  Commute.sum_right Finset.univ a d (fun i _ => h i)

private theorem end_mul_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    (d a b : Module.End ℂ V) (ha : Commute d a) (hb : Commute d b) : Commute d (a*b) := ha.mul_right hb

/-- Both actual scalar momenta are invariant under the original coframe generator. -/
theorem scalar_momentum_dilation (sharp : Bool) : Commute dilation (scalarMomentum sharp) :=
  end_sum_commute dilation _ (fun a => end_mul_commute dilation _ _
    (constant_dilation sharp (scalarBasis a))
    (sub_eq_zero.mp (SourceDilationMomentum.native_momentum_current (scalarDirection a))))

theorem scalar_momentum_adjoint_dilation (sharp : Bool) : Commute dilation (scalarMomentumAdjoint sharp) :=
  end_sum_commute dilation _ (fun a => end_mul_commute dilation _ _
    (sub_eq_zero.mp (SourceDilationMomentum.native_adjoint_current (scalarDirection a)))
    (constant_dilation (!sharp) (scalarBasis a)))

theorem scalar_momentum_scale (sharp : Bool) :
    scaleDerivative (scalarMomentum sharp)=0 ∧ scaleDerivative (scalarMomentumAdjoint sharp)=0 := by
  constructor
  · change (3*Complex.I/2) • (dilation*scalarMomentum sharp-scalarMomentum sharp*dilation)=0
    rw [(scalar_momentum_dilation sharp).eq,sub_self,smul_zero]
  · change (3*Complex.I/2) • (dilation*scalarMomentumAdjoint sharp-scalarMomentumAdjoint sharp*dilation)=0
    rw [(scalar_momentum_adjoint_dilation sharp).eq,sub_self,smul_zero]

private theorem constant_weight (sharp : Bool) (v : Scalar) :
    Commute (constantAction sharp v) SourceCurrentEndpointEnergy.weightAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (branchMap sharp v) (GaussCoframeForm.inverseVolume z : ℂ) (f z)

private theorem factor_weight {R : Type*} [Ring R] {ι : Type*} [Fintype ι]
    (c p : ι → R) (w t : R) (hc : ∀ a, Commute (c a) w) :
    (∑ a,c a*(w*p a)*t)=w*(∑ a,c a*p a)*t := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [←mul_assoc (c a) w,(hc a).eq]
  noncomm_ring

/-- The old primitive is literally the same weighted L, with the same theta and source branch. -/
theorem actual_primitive_momentum_factor (sharp : Bool) (m ell : ℕ) :
    primitive sharp m ell=SourceCurrentEndpointEnergy.weightAction*scalarMomentum sharp*
      SourceMixedNativeReturn.thetaAction m ell :=
  factor_weight (fun a => constantAction sharp (scalarBasis a))
    (fun a => covariantMomentum (scalarDirection a)) SourceCurrentEndpointEnergy.weightAction
    (SourceMixedNativeReturn.thetaAction m ell) (fun a => constant_weight sharp (scalarBasis a))

/-- This is the original full-force producer, now consuming the same L as momentumResponse. -/
theorem actual_weighted_momentum_force (sharp : Bool) (m ell : ℕ) :
    shiftedProjected (force diagonalAction (SourceCurrentEndpointEnergy.weightAction*scalarMomentum sharp*
      SourceMixedNativeReturn.thetaAction m ell))=
      (-96*(sourceTime 0 : ℂ)^2) • (scalarAction sharp*SourceMixedNativeReturn.thetaAction m ell) := by
  rw [←actual_primitive_momentum_factor]
  exact source_mixed_force sharp m ell

private theorem star_im_ne (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

private theorem core_embed (g : OriginalCore) : embed (coreEquiv.symm g)=Subtype.val g :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) (star_im_ne z hz))
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k=k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f)-
    z • FullYSourceResolventGraphSplice.resolvent C z f=f at hf
  have hs : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
      star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (C (FullYSourceResolventGraphSplice.resolvent C z f)-z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,hs,
        starRingEnd_apply,star_star]
    _ = _ := congrArg (fun x => inner ℂ _ x) hf

def sandwichedMomentum (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0) (f : OriginalCore) : H :=
  finiteResolvent F z (embed (scalarMomentum sharp (coreEquiv.symm (sourceCore F z hz f))))

/-- b acts only on two fixed original sources; RLR remains the actual middle source action. -/
def externalMomentum (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : ℂ :=
  inner ℂ (Subtype.val k) (sandwichedMomentum sharp F z hz
    (coreEquiv (potentialAction m ell (coreEquiv.symm g))))-
  inner ℂ (embed (potentialAction m ell (coreEquiv.symm k))) (sandwichedMomentum sharp F z hz g)

private theorem regroup {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b c e h j : E) :
    (inner ℂ a c-inner ℂ e h)+(inner ℂ b c-inner ℂ e j)=
      inner ℂ (a+b) c-inner ℂ e (h+j) := by
  rw [inner_add_left,inner_add_right]
  ring

/-- All momentum corrections are returned before applying any fixed-source cutoff estimate. -/
theorem actual_momentum_external_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    fixedProfiles sharp m ell F z g k+momentumResponse sharp m ell F z hz g k=
      externalMomentum sharp m ell F z hz g k := by
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  let bg : OriginalCore := coreEquiv (potentialAction m ell (coreEquiv.symm g))
  let qb := coreEquiv.symm (sourceCore F z hz bg)
  have hl := actual_relative_transport F (scalarMomentumAdjoint sharp) (star z) (star_im_ne z hz) k
  have hr := actual_relative_transport F (scalarMomentum sharp) z hz g
  have hb : embed qb=finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))) := core_embed _
  have hp : embed p=finiteResolvent F (star z) (Subtype.val k) := core_embed _
  have h0 := regroup
    (finiteResolvent F (star z) (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))))
    (finiteResolvent F (star z) (transportCorrection F (scalarMomentumAdjoint sharp) p))
    (finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))))
    (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k))))
    (finiteResolvent F z (embed (scalarMomentum sharp (coreEquiv.symm g))))
    (finiteResolvent F z (transportCorrection F (scalarMomentum sharp) q))
  have h1 : fixedProfiles sharp m ell F z g k+momentumResponse sharp m ell F z hz g k=
      inner ℂ (embed (scalarMomentumAdjoint sharp p))
        (finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))))-
      inner ℂ (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k))))
        (embed (scalarMomentum sharp q)) :=
    h0.trans (congrArg₂ (fun a b : ℂ => a-b)
      (congrArg (fun x : H => inner ℂ x (finiteResolvent F z
        (embed (potentialAction m ell (coreEquiv.symm g))))) hl.symm)
      (congrArg (fun x : H => inner ℂ
        (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k)))) x) hr.symm))
  have ht := (congrArg (fun x : H => inner ℂ (embed (scalarMomentumAdjoint sharp p)) x) hb.symm).trans
    (scalar_momentum_pair sharp p qb).symm
  have ha := ht.trans (congrArg (fun x : H => inner ℂ x (embed (scalarMomentum sharp qb))) hp)
  have ha' := ha.trans (resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz
    (Subtype.val k) (embed (scalarMomentum sharp qb))).symm
  have hb' := (resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz
    (embed (potentialAction m ell (coreEquiv.symm k))) (embed (scalarMomentum sharp q))).symm
  exact h1.trans (congrArg₂ (fun a b : ℂ => a-b) ha' hb')

def explicitInverseWord (F : Index) (z : ℂ) : H →L[ℂ] H :=
  inverseFlux3 (finiteResolvent F z) (compressionJet F 1) (compressionJet F 2)
    (compressionCorrection F 1) (compressionCorrection F 2) (compressionCorrection F 3)+
  3*inverseFlux2 (finiteResolvent F z) (compressionJet F 1)
    (compressionCorrection F 1) (compressionCorrection F 2)-
  inverseFlux1 (finiteResolvent F z) (compressionCorrection F 1)

/-- B1, B2, B3 are the actual finite moving-projection jets, including all inverse-flux cross terms. -/
theorem actual_inverse_word (F : Index) (z : ℂ) (hz : z.im≠0) :
    correctionWord F z=explicitInverseWord F z := by
  have h := generated_inverse_corrections F z hz
  simp only [correctionWord,jetWord,h.1,h.2.1,h.2.2.1,h.2.2.2,mul_zero,sub_zero,explicitInverseWord]

def movingCurrent (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : OriginalCore) : ℂ :=
  inner ℂ (Subtype.val k) ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
    orbitWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g))

def inverseCurrent (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : OriginalCore) : ℂ :=
  inner ℂ (Subtype.val k) ((sourceRead F g (primitive sharp m ell)*explicitInverseWord F z-
    explicitInverseWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g))

def coefficient : ℂ := -96*(sourceTime 0 : ℂ)^2

def commonMomentum (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : ℂ :=
  coefficient*Complex.I*momentumResponse sharp m ell F z hz g k-Complex.I*movingCurrent sharp m ell F z g k

private theorem endpoint_pair_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E →L[ℂ] E) (g k : E) :
    inner ℂ k ((Complex.I • A+Complex.I • B) g)=Complex.I*inner ℂ k (A g)+Complex.I*inner ℂ k (B g) := by
  rw [add_apply,smul_apply,smul_apply,inner_add_right,inner_smul_right,inner_smul_right]

private theorem endpoint_split (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    inner ℂ (Subtype.val k) (endpointPolynomial sharp m ell F g z (Subtype.val g))=
      Complex.I*movingCurrent sharp m ell F z g k+Complex.I*inverseCurrent sharp m ell F z g k := by
  have h := original_endpoint_moving_return sharp m ell F g z
  let T := sourceRead F g (primitive sharp m ell)
  have hc := congrArg (fun A : H →L[ℂ] H => Complex.I • (T*A-A*T)) (actual_inverse_word F z hz)
  have ha := congrArg (fun A : H →L[ℂ] H => Complex.I • (T*orbitWord F z-orbitWord F z*T)+A) hc
  exact (congrArg (fun A : H →L[ℂ] H => inner ℂ (Subtype.val k) (A (Subtype.val g)))
    (h.trans ha)).trans (endpoint_pair_split _ _ _ _)

/-- Original fixed-F endpoint and every generated projection flux remain in the common return. -/
theorem actual_common_full_jet_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    commonMomentum sharp m ell F z hz g k=
      coefficient*Complex.I*externalMomentum sharp m ell F z hz g k-
      coefficient*Complex.I*fixedProfiles sharp m ell F z g k-
      inner ℂ (Subtype.val k) (endpointPolynomial sharp m ell F g z (Subtype.val g))+
      Complex.I*inverseCurrent sharp m ell F z g k := by
  have he := actual_momentum_external_return sharp m ell F z hz g k
  have hj := endpoint_split sharp m ell F z hz g k
  unfold commonMomentum
  rw [←he,hj]
  ring

def paidMomentumEndpoints (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (g k : OriginalCore) : ℂ :=
  coefficient*Complex.I*fixedProfiles sharp m ell F z g k+
    Complex.I*fixedEndpointProfile sharp m ell F g k z

/-- Only the original cofinal source-containment removes the primitive projection shadow. -/
theorem actual_common_cofinal_return (sharp : Bool) (m ell : ℕ) (g k : OriginalCore) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0,
      commonMomentum sharp m ell F z hz g k=
        coefficient*Complex.I*externalMomentum sharp m ell F z hz g k-
          paidMomentumEndpoints sharp m ell F z g k := by
  filter_upwards [actual_endpoint_cofinal_return sharp m ell g k] with F hF
  intro z hz
  have hi : inner ℂ (Subtype.val k) ((sourceRead F g (primitive sharp m ell)*correctionWord F z-
      correctionWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g))=
      inverseCurrent sharp m ell F z g k :=
    congrArg (fun A : H →L[ℂ] H => inner ℂ (Subtype.val k)
      ((sourceRead F g (primitive sharp m ell)*A-A*sourceRead F g (primitive sharp m ell)) (Subtype.val g)))
        (actual_inverse_word F z hz)
  have h := (hF z hz).trans
    (congrArg (fun a : ℂ => Complex.I*(fixedEndpointProfile sharp m ell F g k z+a)) hi)
  have he := actual_common_full_jet_return sharp m ell F z hz g k
  rw [he,h]
  unfold paidMomentumEndpoints
  ring

private def EnergyTail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
    (∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2)) ≤ ENNReal.ofReal ε

private theorem scaled_target (C ε : ℝ) (hC : 0 ≤ C) (hε : 0<ε) :
    ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) ≤ ENNReal.ofReal ε := by
  rw [←ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hpos : 0<C+1 := by linarith
  calc
    _ ≤ (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hε.le hpos.le)
    _ = ε := mul_div_cancel₀ ε hpos.ne'

private theorem energy_smul (f : ℕ → ℕ → Index → ℝ → ℂ) (c : ℂ)
    (hf : EnergyTail f) : EnergyTail (fun m ell F w => c*f m ell F w) := by
  intro ε hε
  have hc : 0<‖c‖^2+1 := by positivity
  obtain ⟨N,hN⟩ := hf (ε/(‖c‖^2+1)) (div_pos hε hc)
  refine ⟨N,fun m hm ell hell F => ?_⟩
  simp only [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact (mul_le_mul_of_nonneg_left (hN m hm ell hell F) (by positivity)).trans
    (scaled_target (‖c‖^2) ε (sq_nonneg _) hε)

private theorem energy_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : EnergyTail f) (hg : EnergyTail g) : EnergyTail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell F => ?_⟩
  have hl := h₁ m ((Nat.le_max_left _ _).trans hm) ell hell F
  have hr := h₂ m ((Nat.le_max_right _ _).trans hm) ell hell F
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ, ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) := by
        simpa only [Pi.pow_apply] using! ((hc m ell F).norm.pow 2).measurable.ennreal_ofReal
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x) (lintegral_add_left hmeas _)
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/4) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

private theorem paired_profiles_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : OriginalCore) : Continuous (fun w => fixedProfiles sharp m ell F (line μ w) g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc (x y : H) : Continuous (fun w => inner ℂ x
      (finiteResolvent F (line μ w) (finiteResolvent F (line μ w) y))) :=
    continuous_const.inner (hr.clm_apply (hr.clm_apply continuous_const))
  have h := (hc (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k)))
    (embed (potentialAction m ell (coreEquiv.symm g)))).sub
    (hc (embed (potentialAction m ell (coreEquiv.symm k)))
      (embed (scalarMomentum sharp (coreEquiv.symm g))))
  have he : (fun w => fixedProfiles sharp m ell F (line μ w) g k)=
      (fun w => inner ℂ (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k)))
        (finiteResolvent F (line μ w) (finiteResolvent F (line μ w)
          (embed (potentialAction m ell (coreEquiv.symm g)))))-
      inner ℂ (embed (potentialAction m ell (coreEquiv.symm k)))
        (finiteResolvent F (line μ w) (finiteResolvent F (line μ w)
          (embed (scalarMomentum sharp (coreEquiv.symm g)))))) := by
    funext w
    exact congrArg₂ (fun a b : ℂ => a-b)
      (resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) (line μ w)
        (by simpa only [line_im] using hμ.ne') _ _).symm
      (resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) (line μ w)
        (by simpa only [line_im] using hμ.ne') _ _).symm
  rw [he]
  exact h

/-- The directly consumed paired and third-coframe fixed profiles have one all-F full-frequency tail. -/
theorem actual_paid_momentum_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : OriginalCore) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖paidMomentumEndpoints sharp m ell F (line μ w) g k‖^2)) ≤
        ENNReal.ofReal ε := by
  have hf : EnergyTail (fun m ell F w => fixedProfiles sharp m ell F (line μ w) g k) :=
    actual_fixed_profiles_tail sharp μ hμ g k
  have hg : EnergyTail (fun m ell F w => fixedEndpointProfile sharp m ell F g k (line μ w)) :=
    actual_fixed_endpoint_tail sharp μ hμ g k
  have h1 := energy_smul _ (coefficient*Complex.I) hf
  have h2 := energy_smul _ Complex.I hg
  exact energy_add _ _ (fun m ell F => continuous_const.mul
    (paired_profiles_continuous sharp m ell F μ hμ g k)) h1 h2

/-- The common current returns its fixed external b pairing modulo an actually paid cofinal tail. -/
theorem actual_common_corrected_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : OriginalCore) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖commonMomentum sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k-
          coefficient*Complex.I*externalMomentum sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_paid_momentum_tail sharp μ hμ g k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [actual_common_cofinal_return sharp m ell g k] with F hF
  have he (w : ℝ) : commonMomentum sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k-
      coefficient*Complex.I*externalMomentum sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k=
      -paidMomentumEndpoints sharp m ell F (line μ w) g k := by
    rw [hF (line μ w) (by simpa only [line_im] using hμ.ne')]
    ring
  simp_rw [he,norm_neg]
  exact hN m hm ell hell F

/-- In the literal Gamma return, the paired fixed profiles cancel exactly against momentum transport. -/
theorem actual_gamma_external_cofinal (sharp : Bool) (m ell : ℕ) (g k : OriginalCore) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ hz : z.im≠0,
      sourceGamma sharp m ell F g k z=
        coefficient*Complex.I*(radialResponse sharp m ell F z hz g k+
          externalMomentum sharp m ell F z hz g k)-Complex.I*fixedEndpointProfile sharp m ell F g k z := by
  filter_upwards [actual_common_cofinal_return sharp m ell g k] with F hF
  intro z hz
  have hg := actual_gamma_radial_return sharp m ell F z hz g k
  have hs : sourceGamma sharp m ell F g k z=
      coefficient*Complex.I*(fixedProfiles sharp m ell F z g k+radialResponse sharp m ell F z hz g k)+
        commonMomentum sharp m ell F z hz g k := by
    exact hg.trans (by unfold commonMomentum movingCurrent coefficient; ring)
  exact hs.trans (by rw [hF z hz]; unfold paidMomentumEndpoints; ring)

/-- The remaining Gamma difference is the already-paid original coframe endpoint, on the same filter. -/
theorem actual_gamma_external_endpoint_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : OriginalCore) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖sourceGamma sharp m ell F g k (line μ w)-
          coefficient*Complex.I*(radialResponse sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g k+
          externalMomentum sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g k)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_fixed_endpoint_tail sharp μ hμ g k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [actual_gamma_external_cofinal sharp m ell g k] with F hF
  have he (w : ℝ) : sourceGamma sharp m ell F g k (line μ w)-
      coefficient*Complex.I*(radialResponse sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k+
      externalMomentum sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k)=
      -Complex.I*fixedEndpointProfile sharp m ell F g k (line μ w) := by
    rw [hF (line μ w) (by simpa only [line_im] using hμ.ne')]
    ring
  simp_rw [he,norm_mul,norm_neg,Complex.norm_I,one_mul]
  exact hN m hm ell hell F

end LowEnergy.SourcePairedMomentumFlux
