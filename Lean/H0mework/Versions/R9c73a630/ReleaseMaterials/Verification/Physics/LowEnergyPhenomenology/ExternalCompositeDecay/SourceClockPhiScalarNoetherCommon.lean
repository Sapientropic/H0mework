import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarNoetherPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarInverseNativeEnergy SourceScalarEssentialBudget SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusNormalizedFluxBudget SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceScalarPairedTransport SourceResolventBandLimit SourceScalarPositiveBulkWard
open SourceLocalizedInverseFormPayment SourceClockYukawaCubicCurrent FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology
private abbrev n : ℝ := sourceTime 0
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair embed normalizedState normalizedForcing phiResponseCore

def sourceNoetherFrequency (half : Bool) : ℝ := if half then sourceMu/2 else sourceMu
private theorem n_pos : 0 < n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem n_lt_one : n<1 := by
  change sourceTime 0<1
  rw [source_time_generated]
  change SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse < 1
  have hp:=SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hs:=SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_sq
  nlinarith
private theorem source_mu_lower : 37<sourceMu := by
  change 37<1+(2*Real.pi)^2
  nlinarith [Real.pi_gt_three]
theorem actual_source_noether_gap (half : Bool) : 15<sourceNoetherFrequency half-2*n := by
  cases half <;> simp only [sourceNoetherFrequency,Bool.false_eq_true,ite_false,ite_true]
  all_goals nlinarith [source_mu_lower,n_lt_one,n_pos]
private theorem frequency_pos (half : Bool) : 0<sourceNoetherFrequency half := by
  linarith [actual_source_noether_gap half,n_pos]
def scalarNoetherFactor (half : Bool) : ℝ := 5/(sourceNoetherFrequency half-2*n)
theorem actual_scalar_noether_fraction (half : Bool) :
    0<scalarNoetherFactor half ∧ scalarNoetherFactor half<1/3 := by
  have hg:=actual_source_noether_gap half
  have hp:0<sourceNoetherFrequency half-2*n:=by linarith
  refine ⟨div_pos (by norm_num) hp,?_⟩
  unfold scalarNoetherFactor
  apply (div_lt_iff₀ hp).mpr
  linarith
private theorem factor_cancel (half : Bool) :
    scalarNoetherFactor half*(sourceNoetherFrequency half-2*n)=5 := by
  unfold scalarNoetherFactor
  exact div_mul_cancel₀ _ (ne_of_gt (lt_trans (by norm_num) (actual_source_noether_gap half)))
private theorem frequency_nonreal (half advanced : Bool) (x : ℝ) :
    (actualFrequency advanced (sourceNoetherFrequency half) x).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using (frequency_pos half).ne'

def scalarNoetherNormCost (half : Bool) : ℝ :=
  (394/15:ℝ)*n*‖vacuum‖^2+scalarNoetherFactor half*n^2*‖vacuum‖^2
private theorem norm_cost_nonnegative (half : Bool) : 0 ≤ scalarNoetherNormCost half := by
  unfold scalarNoetherNormCost
  have hn:=n_pos
  have hk:=(actual_scalar_noether_fraction half).1
  positivity

def scalarNoetherGap (half advanced : Bool) (m ell : ℕ) (F : Index) (x : ℝ) (g : diagonal.domain) : ℝ :=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=normalizedState m ell F z hz g
  scalarNativePrice w-scalarNoetherFactor half*scalarPrice m ell F z hz g advanced+
    13*n*inverseNativeEnergy w+6*n*scalarPaymentSquare w

/-- The unused original scalar squares remain as debits after the full source Noether price is consumed. -/
theorem actual_scalar_noether_point_payment (half advanced : Bool)
    (m ell : ℕ) (F : Index) (x : ℝ) (g : diagonal.domain) :
    scalarNoetherGap half advanced m ell F x g ≤ scalarNoetherNormCost half*
      ‖embed (normalizedState m ell F (actualFrequency advanced (sourceNoetherFrequency half) x)
        (frequency_nonreal half advanced x) g)‖^2 := by
  let z:=actualFrequency advanced (sourceNoetherFrequency half) x
  let hz:=frequency_nonreal half advanced x
  let w:=normalizedState m ell F z hz g
  have hW:=actual_normalized_scalar_source m ell F (sourceNoetherFrequency half)
    (frequency_pos half) g advanced x
  change (sourceNoetherFrequency half-2*n)*scalarEnergy w ≤
    scalarPrice m ell F z hz g advanced+n^2*‖vacuum‖^2*‖embed w‖^2 at hW
  have hM:=mul_le_mul_of_nonneg_left hW (actual_scalar_noether_fraction half).1.le
  rw [←mul_assoc,factor_cancel] at hM
  have hS:=actual_scalar_native_joint_square w
  dsimp only [scalarNoetherGap,scalarNoetherNormCost]
  change scalarNativePrice w-scalarNoetherFactor half*scalarPrice m ell F z hz g advanced+
    13*n*inverseNativeEnergy w+6*n*scalarPaymentSquare w ≤ _
  nlinarith only [hM,hS]

private abbrev S : End :=SourceClockPhiRadiusSourceCurrent.phiInverseAction
private abbrev r : End :=SourceClockPhiRadiusSourceCurrent.phiRadiusAction
private abbrev T (m ell : ℕ) : End :=phiThetaAction m ell
private theorem normalized_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=S (phiResponseCore m ell F z hz g):=by
  let Q : End := (1:End)-S
  have hQ(f:QuantumTest):S (Q f)=Q (S f):=by
    change S (f-S f)=S f-S (S f)
    rw [map_sub]
  have hp(k:ℕ)(f:QuantumTest):S ((Q^k) f)=(Q^k) (S f):=by
    induction k with
    | zero => simp only [pow_zero,Module.End.one_apply]
    | succ k ih =>
      rw [pow_succ']
      change S (Q ((Q^k) f))=Q ((Q^k) (S f))
      rw [hQ,ih]
  have hc : Commute S (T m ell) := by
    change S*(Q^(m+1)-Q^(ell+1))=(Q^(m+1)-Q^(ell+1))*S
    apply LinearMap.ext
    intro f
    simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub,hp]
  have hi(f:QuantumTest):S (r f)=f:=by
    apply DFunLike.ext
    intro q
    change (phiReciprocal q:ℂ) • ((phiRadius q:ℂ) • f q)=f q
    rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have he(f:QuantumTest):S (T m ell f)=T m ell (S f):=LinearMap.congr_fun hc.eq f
  unfold normalizedState phiResponseCore
  change T m ell (resolventCore F z hz (coreEquiv.symm g))-
    S (T m ell (resolventCore F z hz (r (coreEquiv.symm g))))=
    S (T m ell (r (resolventCore F z hz (coreEquiv.symm g))-
      resolventCore F z hz (r (coreEquiv.symm g))))
  simp only [map_sub,he,hi]

/-- One source-owned N pays the whole scalar block less a strict fraction of the original signed
Noether source, while retaining its unused actual momentum and shifted-field squares. -/
theorem actual_scalar_noether_common_payment (half : Bool) (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index), ∀ advanced : Bool,
      (∫⁻x:ℝ,ENNReal.ofReal (scalarNoetherGap half advanced m ell F x g))≤ENNReal.ofReal ε := by
  intro ε hε
  let c:=scalarNoetherNormCost half
  have hc:0≤c:=norm_cost_nonnegative half
  have hd:0<ε/(c+1):=div_pos hε (by positivity)
  obtain ⟨N,hN⟩:=actual_normalized_response_common_tail (sourceNoetherFrequency half)
    (frequency_pos half) g (ε/(c+1)) hd
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have hn:=hF advanced
  have hp(x:ℝ):‖embed (normalizedState m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)‖^2=
      normalizedEnergy m ell F (actualFrequency advanced (sourceNoetherFrequency half) x)
        (frequency_nonreal half advanced x) g := by
    rw [normalized_return]
    rfl
  calc
    _ ≤ ∫⁻x:ℝ,ENNReal.ofReal (c*normalizedEnergy m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal ((actual_scalar_noether_point_payment half advanced m ell F x g).trans_eq (by rw [hp]))
    _ = ENNReal.ofReal c*(∫⁻x:ℝ,ENNReal.ofReal (normalizedEnergy m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) x) (frequency_nonreal half advanced x) g)) := by
      simp_rw [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c*ENNReal.ofReal (ε/(c+1)) := mul_le_mul_of_nonneg_left hn zero_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show 0<c+1 by positivity)).mpr
      nlinarith only [hc,hε]
end LowEnergy.FirstCurrentJointBudget
