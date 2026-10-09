import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarPositiveBulkEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarBulkResidualBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm GaussLiveMomentum GaussMomentumAdjoint
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume
open SourceScalarVirialBulk SourceScalarPositiveBulkWard SourceScalarPositiveBulkEndpoint
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRetardedBandCurrent
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
abbrev End := SourceScalarGaugeScale.End
abbrev T := SourceNativeCutoffContact.thetaAction
abbrev C := SourceNativeCutoffContact.contactAction

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (T m ell g)=sourcePair (T m ell f) g := multiply_pair _ _ _ _
private theorem theta_real_commute (m ell : ℕ) (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart,ContDiffAt ℝ ∞ a z.val) : Commute (T m ell) (multiply a ha) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ) (a z : ℂ) (f z)
private theorem theta_volume (m ell : ℕ) : Commute (T m ell) volumeAction := theta_real_commute m ell _ _
private theorem contact_theta (v : Ambient) (m ell : ℕ) : Commute (C v m ell) (T m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative v m ell z : ℂ))
    (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)

private theorem row_ims (P T C : End)
    (hT : ∀ f g,sourcePair f (T g)=sourcePair (T f) g)
    (hPT : ∀ f,P (T f)=T (P f)+C f) (hCT : Commute C T) (p q : QuantumTest) :
    sourcePair (P (T p)) (P (T q))=
      (1/2 : ℂ)*(sourcePair (P (T (T p))) (P q)+sourcePair (P p) (P (T (T q))))+
        sourcePair (C p) (C q) := by
  have hTT (f : QuantumTest) : P (T (T f))=T (T (P f))+T (C f)+T (C f) := by
    rw [hPT,hPT,map_add,show C (T f)=T (C f) from LinearMap.congr_fun hCT.eq f]
  have hL : sourcePair (P (T (T p))) (P q)=sourcePair (T (P p)) (T (P q))+
      sourcePair (C p) (T (P q))+sourcePair (C p) (T (P q)) := by
    rw [hTT]
    simp only [sourcePair,map_add,inner_add_left]
    change sourcePair (T (T (P p))) (P q)+sourcePair (T (C p)) (P q)+sourcePair (T (C p)) (P q)=_
    rw [←hT (T (P p)) (P q),←hT (C p) (P q)]
    rfl
  have hR : sourcePair (P p) (P (T (T q)))=sourcePair (T (P p)) (T (P q))+
      sourcePair (T (P p)) (C q)+sourcePair (T (P p)) (C q) := by
    rw [hTT]
    simp only [sourcePair,map_add,inner_add_right]
    change sourcePair (P p) (T (T (P q)))+sourcePair (P p) (T (C q))+sourcePair (P p) (T (C q))=_
    rw [hT (P p) (T (P q)),hT (P p) (C q)]
    rfl
  rw [hL,hR,hPT,hPT]
  simp only [sourcePair,map_add,inner_add_left,inner_add_right]
  ring

private theorem volume_weight (f : QuantumTest) :
    volumeAction (multiply scalarWeight scalarWeight_smooth f)=(-sourceTime 0 : ℂ) • f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change (volume z : ℂ) • ((scalarWeight z : ℂ) • f z)=(-sourceTime 0 : ℂ) • f z
    rw [smul_smul]
    apply congrArg (fun c : ℂ => c • f z)
    rw [scalarWeight]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne']
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    change (volume z : ℂ) • ((scalarWeight z : ℂ) • f z)=(-sourceTime 0 : ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero]

private theorem volume_sandwich (v : Ambient) (p q : QuantumTest) :
    sourcePair p (volumeAction (sandwich v v scalarWeight scalarWeight_smooth q))=
      (-sourceTime 0 : ℂ)*sourcePair (covariantMomentum v p) (covariantMomentum v q) := by
  have hc := LinearMap.congr_fun (native_adjoint_volume v).eq
    (multiply scalarWeight scalarWeight_smooth (covariantMomentum v q))
  change sourcePair p (volumeAction (GaussMomentumAdjoint.adjoint v
    (multiply scalarWeight scalarWeight_smooth (covariantMomentum v q))))=_
  change GaussMomentumAdjoint.adjoint v (volumeAction _) =volumeAction (GaussMomentumAdjoint.adjoint v _) at hc
  rw [←hc,volume_weight,adjoint_pair]
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem scalar_volume_pair (p q : QuantumTest) :
    sourcePair p (volumeAction (scalarKinetic q))=
      (-sourceTime 0/2 : ℂ)*∑ i : ScalarIndex,sourcePair
        (covariantMomentum (scalarDirection i) p) (covariantMomentum (scalarDirection i) q) := by
  have he : sourcePair p (volumeAction (scalarKinetic q))=
      (1/2 : ℂ)*∑ i : ScalarIndex,sourcePair p
        (volumeAction (sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth q)) := by
    simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
      sourcePair,inner_smul_right,inner_sum]
  rw [he]
  simp only [volume_sandwich,←Finset.mul_sum]
  ring

private theorem contact_gauge_zero (v : Ambient) (hv : v.1=0) (m ell : ℕ) : C v m ell=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hd : SourceNativeCutoffContact.thetaDerivative v m ell z=0 := by
    simp only [SourceNativeCutoffContact.thetaDerivative,GaussRadialMomentum.radialDerivative,hv,
      inner_zero_right,neg_zero,zero_div,mul_zero]
  change ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative v m ell z : ℂ)) • f z=0
  rw [hd,Complex.ofReal_zero,mul_zero,zero_smul]
private theorem gauge_theta (m ell : ℕ) : Commute gaugeKinetic (T m ell) := by
  have hp (v : Ambient) (hv : v.1=0) : Commute (covariantMomentum v) (T m ell) := by
    apply LinearMap.ext
    intro f
    have h := SourceNativeCutoffContact.native_core_contact v m ell f
    simpa only [contact_gauge_zero v hv,LinearMap.zero_apply,add_zero] using! h
  have ha (v : Ambient) (hv : v.1=0) : Commute (GaussMomentumAdjoint.adjoint v) (T m ell) := by
    apply LinearMap.ext
    intro f
    have h := SourceNativeCutoffContact.sharp_core_contact v m ell f
    simpa only [contact_gauge_zero v hv,LinearMap.zero_apply,add_zero] using! h
  have hm (i j : Fin 3) : Commute (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) (T m ell) :=
    (theta_real_commute m ell _ _).symm
  have hs (a : LieIndex) (i j : Fin 3) :
      Commute (sandwich (gaugeDirection i a) (gaugeDirection j a)
        (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)) (T m ell) :=
    (ha _ rfl).mul_left ((hm i j).mul_left (hp _ rfl))
  exact (Commute.sum_left Finset.univ _ _ (fun a _ => Commute.sum_left Finset.univ _ _ (fun i _ =>
    Commute.sum_left Finset.univ _ _ (fun j _ => hs a i j)))).smul_left (1/2 : ℂ)

private theorem commuting_ims (A T : End)
    (hT : ∀ f g,sourcePair f (T g)=sourcePair (T f) g) (hAT : Commute A T) (p q : QuantumTest) :
    sourcePair (T p) (A (T q))=(1/2 : ℂ)*(
      sourcePair (T (T p)) (A q)+sourcePair p (A (T (T q)))) := by
  have he (f : QuantumTest) : A (T f)=T (A f) := LinearMap.congr_fun hAT.eq f
  rw [he,he,he,hT,hT,hT]
  ring

def contactPair (m ell : ℕ) (p q : QuantumTest) : ℂ :=
  (4*(sourceTime 0 : ℂ))*∑ i : ScalarIndex,sourcePair (C (scalarDirection i) m ell p) (C (scalarDirection i) m ell q)

/-- Full native70, electric, and shifted-potential IMS, before taking a real part or splitting the actual p/q legs. -/
theorem original_bulk_bilinear_ims (m ell : ℕ) (p q : QuantumTest) :
    sourcePair (T m ell p) (volumeAction (positiveBulk (T m ell q)))=
      (1/2 : ℂ)*(sourcePair (T m ell (T m ell p)) (volumeAction (positiveBulk q))+
        sourcePair p (volumeAction (positiveBulk (T m ell (T m ell q)))))+contactPair m ell p q := by
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset ScalarIndex)) rfl (fun i _ =>
    row_ims (covariantMomentum (scalarDirection i)) (T m ell) (C (scalarDirection i) m ell)
      (theta_pair m ell) (SourceNativeCutoffContact.native_core_contact (scalarDirection i) m ell)
      (contact_theta (scalarDirection i) m ell) p q)
  simp only [mul_add,Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hg := commuting_ims (volumeAction*gaugeKinetic) (T m ell) (theta_pair m ell)
    ((theta_volume m ell).symm.mul_left (gauge_theta m ell)) p q
  have hp := commuting_ims (volumeAction*shiftedAction) (T m ell) (theta_pair m ell)
    ((theta_volume m ell).symm.mul_left ((theta_real_commute m ell _ _).symm)) p q
  have split (f h : QuantumTest) : sourcePair f (volumeAction (positiveBulk h))=
      (4*(sourceTime 0 : ℂ))*∑ i : ScalarIndex,sourcePair
        (covariantMomentum (scalarDirection i) f) (covariantMomentum (scalarDirection i) h)+
      (36 : ℂ)*sourcePair f (volumeAction (gaugeKinetic h))+
      (8 : ℂ)*sourcePair f (volumeAction (shiftedAction h)) := by
    rw [original_positive_bulk]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,sourcePair,inner_add_right,inner_smul_right]
    change (-8 : ℂ)*sourcePair f (volumeAction (scalarKinetic h))+
      (36 : ℂ)*sourcePair f (volumeAction (gaugeKinetic h))+
      (8 : ℂ)*sourcePair f (volumeAction (shiftedAction h))=_
    rw [scalar_volume_pair]
    simp only [sourcePair]
    ring
  rw [split,split,split]
  change _=_ at hg hp
  dsimp only [contactPair]
  linear_combination (4*(sourceTime 0 : ℂ))*hs+36*hg+8*hp

private theorem fixed_theta_balanced (m ell : ℕ) (F : Index) (zl zr : ℂ)
    (hl : zl.im≠0) (hr : zr.im≠0) (g k : diagonal.domain) :
    fixedBulk F zl zr hl hr g k (T m ell) (T m ell)=
      (1/2 : ℂ)*(fixedBulk F zl zr hl hr g k (T m ell*T m ell) 1+
        fixedBulk F zl zr hl hr g k 1 (T m ell*T m ell)) := by
  rw [actual_fixed_bulk_collapse]
  have hc (f : QuantumTest) : volumeAction (T m ell f)=T m ell (volumeAction f) :=
    LinearMap.congr_fun (theta_volume m ell).symm.eq f
  dsimp only [Pi.smul_apply,smul_eq_mul,fixedPair,Module.End.mul_apply,Module.End.one_apply]
  simp only [hc]
  simp_rw [theta_pair]
  ring

def residualLocalization (m ell : ℕ) (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : ℂ :=
  defectBulk F zl zr hl hr g k (T m ell) (T m ell)-
    (1/2 : ℂ)*(defectBulk F zl zr hl hr g k (T m ell*T m ell) 1+
      defectBulk F zl zr hl hr g k 1 (T m ell*T m ell))

/-- All affine/gauge/coframe raised-defect crosses localize together; their fixed-source and complex-frequency terms cancel exactly. -/
theorem actual_residual_localization (m ell : ℕ) (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : residualLocalization m ell F zl zr hl hr g k=
      contactPair m ell (state F zl hl k) (state F zr hr g) := by
  have h0 := actual_positive_bulk_normal F zl zr hl hr g k (T m ell) (T m ell)
  have hL := actual_positive_bulk_normal F zl zr hl hr g k (T m ell*T m ell) 1
  have hR := actual_positive_bulk_normal F zl zr hl hr g k 1 (T m ell*T m ell)
  have hI := original_bulk_bilinear_ims m ell (state F zl hl k) (state F zr hr g)
  have hF := fixed_theta_balanced m ell F zl zr hl hr g k
  have hU := commuting_ims volumeAction (T m ell) (theta_pair m ell) (theta_volume m ell).symm
    (state F zl hl k) (state F zr hr g)
  simp only [Module.End.mul_apply,Module.End.one_apply] at hL hR hF
  dsimp only [residualLocalization]
  linear_combination -h0+(1/2 : ℂ)*hL+(1/2 : ℂ)*hR+hI-hF+
    (3*(vacuumJetCoefficient : ℂ)*(star zl+zr))*hU


/-- Full original defect/frequency response. The term is kept as a signed whole. -/
def signedResidual (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : PairMatrix := fun A B =>
  defectBulk F zl zr hl hr g k A B-
    (3*(vacuumJetCoefficient : ℂ)*(star zl+zr))*
      sourcePair (A (state F zl hl k)) (volumeAction (B (state F zr hr g)))

def signedLocalization (m ell : ℕ) (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : ℂ :=
  signedResidual F zl zr hl hr g k (T m ell) (T m ell)-
    (1/2 : ℂ)*(signedResidual F zl zr hl hr g k (T m ell*T m ell) 1+
      signedResidual F zl zr hl hr g k 1 (T m ell*T m ell))

/-- The complex spectral term is cancelled in the complete localization word, together with both fixed-source terms. -/
theorem actual_signed_localization (m ell : ℕ) (F : Index) (zl zr : ℂ) (hl : zl.im≠0) (hr : zr.im≠0)
    (g k : diagonal.domain) : signedLocalization m ell F zl zr hl hr g k=
      contactPair m ell (state F zl hl k) (state F zr hr g) := by
  have h := actual_residual_localization m ell F zl zr hl hr g k
  have hU := commuting_ims volumeAction (T m ell) (theta_pair m ell) (theta_volume m ell).symm
    (state F zl hl k) (state F zr hr g)
  dsimp only [signedLocalization,signedResidual,Module.End.mul_apply,Module.End.one_apply]
  dsimp only [residualLocalization] at h
  linear_combination h-(3*(vacuumJetCoefficient : ℂ)*(star zl+zr))*hU

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem native_contact_bound (i : ScalarIndex) (m ell : ℕ) (hell : m ≤ ell) (f : QuantumTest) :
    ‖embed (C (scalarDirection i) m ell f)‖ ≤ (2/(m+2 : ℝ))*‖embed f‖ := by
  have h := SourceNativeCutoffContact.bounded_contact_bound (scalarDirection i) m ell hell (embed f)
  rw [SourceNativeCutoffContact.bounded_contact_core] at h
  have hi : ‖(scalarDirection i).1‖=1 := scalarBasis.orthonormal.norm_eq_one i
  simpa only [hi,mul_one] using! h

/-- All seventy native source contacts are bounded together; the estimate is independent of the upper cutoff. -/
theorem original_contact_pair_bound (m ell : ℕ) (hell : m ≤ ell) (p q : QuantumTest) :
    ‖contactPair m ell p q‖ ≤ (1120*sourceTime 0/(m+2 : ℝ)^2)*‖embed p‖*‖embed q‖ := by
  have hr (i : ScalarIndex) :
      ‖sourcePair (C (scalarDirection i) m ell p) (C (scalarDirection i) m ell q)‖ ≤
        ((2/(m+2 : ℝ))*‖embed p‖)*((2/(m+2 : ℝ))*‖embed q‖) := by
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (native_contact_bound i m ell hell p)
      (native_contact_bound i m ell hell q) (norm_nonneg _) (by positivity))
  have hn : ‖(4*(sourceTime 0 : ℂ))‖=4*sourceTime 0 := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos lapse_pos]
  rw [contactPair,norm_mul,hn]
  have hs := (norm_sum_le (Finset.univ : Finset ScalarIndex) _).trans (Finset.sum_le_sum (fun i _ => hr i))
  have hcard : Fintype.card ScalarIndex=70 := by
    simp only [ScalarIndex,Fintype.card_fin,SourceQuantumNativeDimensions.scalar_finrank]
  simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at hs
  apply (mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) lapse_pos.le)).trans_eq
  field_simp
  ring

private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)
private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := core_embed _

def retardedLocalization (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) : ℂ :=
  signedLocalization m ell F (star (line μ w)) (line μ w)
    (by simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne')
    (by simpa only [line_im] using hμ.ne') g k

private theorem retarded_bound (m ell : ℕ) (hell : m ≤ ell) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) (w : ℝ) :
    ‖retardedLocalization m ell F μ hμ g k w‖^2 ≤
      ((1120*sourceTime 0/(m+2 : ℝ)^2)^2*‖(k : H)‖^2/μ^2)*
        ‖finiteResolvent F (line μ w) (g : H)‖^2 := by
  have hz : (line μ w).im≠0 := by simpa only [line_im] using hμ.ne'
  have hs : (star (line μ w)).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hp : ‖finiteResolvent F (star (line μ w)) (k : H)‖ ≤ (1/μ)*‖(k : H)‖ := by
    have hn : ‖finiteResolvent F (star (line μ w))‖ ≤ 1/μ := by
      simpa only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] using!
        finite_resolvent_norm F (star (line μ w)) hs
    exact ((finiteResolvent F _).le_opNorm _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have h := original_contact_pair_bound m ell hell (state F (star (line μ w)) hs k) (state F (line μ w) hz g)
  rw [state_embed,state_embed] at h
  have hb : 0 ≤ 1120*sourceTime 0/(m+2 : ℝ)^2 :=
    div_nonneg (mul_nonneg (by norm_num) lapse_pos.le) (sq_nonneg _)
  have h2 := h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hb) (norm_nonneg _))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h2 2
  change ‖signedLocalization m ell F (star (line μ w)) (line μ w) hs hz g k‖^2 ≤ _
  rw [actual_signed_localization]
  exact hsq.trans_eq (by ring)

/-- The complete signed flux localization, not an individual defect leg, has an explicit all-F full-frequency bound. -/
theorem actual_signed_localization_energy (m ell : ℕ) (hell : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖retardedLocalization m ell F μ hμ g k w‖^2)) ≤
      ENNReal.ofReal (((1120*sourceTime 0)^2/(m+2 : ℝ)^4)*(Real.pi/μ^3)*‖(k : H)‖^2*‖(g : H)‖^2) := by
  let A := (1120*sourceTime 0/(m+2 : ℝ)^2)^2*‖(k : H)‖^2/μ^2
  have hA : 0 ≤ A := by dsimp [A];positivity
  have he : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖(g : H)‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ (g : H)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal A*ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal (retarded_bound m ell hell F μ hμ g k w)
    _=ENNReal.ofReal A*∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _=_ := by
      rw [he,←ENNReal.ofReal_mul hA]
      congr 1
      dsimp [A]
      field_simp

/-- One common threshold handles every F and upper cutoff in the original retarded signed localization word. -/
theorem actual_signed_localization_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖retardedLocalization m ell F μ hμ g k w‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let A := (1120*sourceTime 0)^2*(Real.pi/μ^3)*‖(k : H)‖^2*‖(g : H)‖^2
  obtain ⟨N,hN⟩ := exists_nat_gt (A/ε)
  refine ⟨N,fun m hm ell hell F => (actual_signed_localization_energy m ell hell F μ hμ g k).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hmR : (N : ℝ) ≤ m := Nat.cast_le.mpr hm
  have hd : 0<(m+2 : ℝ) := by positivity
  have hdiv : A/ε<(m+2 : ℝ) := by linarith
  have hc : A<ε*(m+2 : ℝ) := by nlinarith [(div_lt_iff₀ hε).mp hdiv]
  have hpow : (m+2 : ℝ) ≤ (m+2 : ℝ)^4 := by
    have hm0 := Nat.cast_nonneg (α := ℝ) m
    nlinarith [sq_nonneg ((m+2 : ℝ)^2-1)]
  have hb : A/(m+2 : ℝ)^4 ≤ ε := (div_le_iff₀ (pow_pos hd 4)).mpr
    (hc.le.trans (mul_le_mul_of_nonneg_left hpow hε.le))
  convert hb using 1
  dsimp [A]
  ring

end LowEnergy.SourceScalarBulkResidualBudget
