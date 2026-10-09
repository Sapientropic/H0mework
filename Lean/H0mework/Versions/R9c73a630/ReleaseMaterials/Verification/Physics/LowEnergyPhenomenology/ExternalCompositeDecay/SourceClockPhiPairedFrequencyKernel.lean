import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointInputScalarPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.InputForceFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceScalarPositiveBulkWard SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ReverseNativeFrequencyWard MeasureTheory Filter SourceFourPoleEnergyClosed SourceJointResidualEnergy
open scoped Topology
private abbrev P(advanced:Bool)(μ a q:ℝ):ℂ:=((a:ℂ)-actualFrequency advanced μ q)⁻¹
private abbrev signedMu(advanced:Bool)(μ:ℝ):ℝ:=if advanced then -μ else μ
private theorem physical_line(advanced:Bool)(μ q:ℝ):
    actualFrequency advanced μ q=(q:ℂ)+(signedMu advanced μ:ℂ)*Complex.I:=by
  cases advanced <;> simp [actualFrequency,line,signedMu]
private theorem pole_ne(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    (a:ℂ)-actualFrequency advanced μ q≠0:=by
  intro h
  apply reverse_frequency_nonreal advanced μ hμ q
  rw [←sub_eq_zero.mp h]
  rfl
private theorem pole_bound(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):‖P advanced μ a q‖ ≤ μ⁻¹:=by
  have hb:μ ≤ ‖(a:ℂ)-actualFrequency advanced μ q‖:=by
    have h:=Complex.abs_im_le_norm ((a:ℂ)-actualFrequency advanced μ q)
    cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,Complex.star_def,
      Complex.sub_im,Complex.ofReal_im,Complex.conj_im,line_im,zero_sub,abs_neg,abs_of_pos hμ] using h
  exact (norm_inv _).trans_le ((inv_le_inv₀ (norm_pos_iff.mpr (pole_ne advanced μ hμ a q)) hμ).mpr hb)
private theorem pole_measurable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a:ℝ):
    AEStronglyMeasurable (P advanced μ a):=
  (continuous_iff_continuousAt.mpr (fun q=>(actual_physical_pole_derivative advanced μ hμ a q).continuousAt)).aestronglyMeasurable
private theorem pole_pair_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (P advanced μ a q)*P advanced μ b q):=by
  cases advanced
  · simpa only [P,actualFrequency,Bool.false_eq_true,ite_false,pole] using! two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (two_pole_integrable μ a b hμ)
    have he(q:ℝ):star (P true μ a q)*P true μ b q=star (star (pole μ a q)*pole μ b q):=by
      simp only [P,actualFrequency,ite_true,pole,star_mul,star_inv₀,star_sub,
        Complex.star_def,Complex.conj_ofReal]
      ring
    simpa only [he] using! h
private theorem pole_top(advanced:Bool)(μ a:ℝ):Tendsto (P advanced μ a) atTop (𝓝 0):=by
  have h:=tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atTop_cobounded ℂ))
  convert! h using 1
  funext q
  unfold P
  rw [physical_line]
  change ((a:ℂ)-((q:ℂ)+(signedMu advanced μ:ℂ)*Complex.I))⁻¹=
    (((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)-(q:ℂ))⁻¹
  congr 1
  ring
private theorem pole_bot(advanced:Bool)(μ a:ℝ):Tendsto (P advanced μ a) atBot (𝓝 0):=by
  have h:=tendsto_inv₀_cobounded.comp
    ((tendsto_const_sub_cobounded ((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)).comp
      (RCLike.tendsto_ofReal_atBot_cobounded ℂ))
  convert! h using 1
  funext q
  unfold P
  rw [physical_line]
  change ((a:ℂ)-((q:ℂ)+(signedMu advanced μ:ℂ)*Complex.I))⁻¹=
    (((a:ℂ)-(signedMu advanced μ:ℂ)*Complex.I)-(q:ℂ))⁻¹
  congr 1
  ring

def pairedFrequencyKernel(advanced:Bool)(μ a b q:ℝ):ℂ:=
  star (actualFrequency advanced μ q*P advanced μ a q)*P advanced μ b q
def forcingFrequencyKernel(advanced:Bool)(μ a b q:ℝ):ℂ:=
  star (actualFrequency advanced μ q*(P advanced μ a q)^2)*P advanced μ b q
def inputFrequencyKernel(advanced:Bool)(μ a b q:ℝ):ℂ:=
  star (actualFrequency advanced μ q*P advanced μ a q)*(P advanced μ b q)^2
private theorem z_pole(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a q:ℝ):
    actualFrequency advanced μ q*P advanced μ a q=(a:ℂ)*P advanced μ a q-1:=by
  have h:=mul_inv_cancel₀ (pole_ne advanced μ hμ a q)
  change ((a:ℂ)-actualFrequency advanced μ q)*P advanced μ a q=1 at h
  linear_combination (norm:=ring) -h
private theorem star_z(advanced:Bool)(μ q:ℝ):
    star (actualFrequency advanced μ q)=actualFrequency advanced μ q-2*(signedMu advanced μ:ℂ)*Complex.I:=by
  rw [physical_line]
  simp only [star_add,star_mul,Complex.star_def,Complex.conj_ofReal,Complex.conj_I]
  ring
private theorem forcing_return(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b q:ℝ):
    forcingFrequencyKernel advanced μ a b q=
      (a:ℂ)*(star (P advanced μ a q)*P advanced μ b q*star (P advanced μ a q))-
        star (P advanced μ a q)*P advanced μ b q:=by
  have h:=congrArg star (z_pole advanced μ hμ a q)
  simp only [star_mul,star_sub,star_one,Complex.star_def,Complex.conj_ofReal] at h
  unfold forcingFrequencyKernel
  simp only [star_mul,star_pow,Complex.star_def]
  linear_combination (norm:=(simp only [Complex.star_def];ring)) star (P advanced μ a q)*P advanced μ b q*h
private theorem input_return(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b q:ℝ):
    inputFrequencyKernel advanced μ a b q=
      ((b:ℂ)-2*(signedMu advanced μ:ℂ)*Complex.I)*
        (star (P advanced μ a q)*P advanced μ b q*P advanced μ b q)-
          star (P advanced μ a q)*P advanced μ b q:=by
  have h:=z_pole advanced μ hμ b q
  unfold inputFrequencyKernel
  rw [star_mul,star_z]
  linear_combination (norm:=(simp only [Complex.star_def];ring)) star (P advanced μ a q)*P advanced μ b q*h

theorem actual_frequency_kernel_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (P advanced μ a q)*P advanced μ b q) ∧
      Integrable (forcingFrequencyKernel advanced μ a b) ∧ Integrable (inputFrequencyKernel advanced μ a b):=by
  have h0:=pole_pair_integrable advanced μ hμ a b
  have ha:=h0.mul_bdd (c:=μ⁻¹) (pole_measurable advanced μ hμ a).star
    (Eventually.of_forall (fun q=>by
      change ‖star (P advanced μ a q)‖≤μ⁻¹
      simpa only [norm_star] using pole_bound advanced μ hμ a q))
  have hb:=h0.mul_bdd (pole_measurable advanced μ hμ b)
    (Eventually.of_forall (fun q=>pole_bound advanced μ hμ b q))
  exact ⟨h0,((ha.const_mul (a:ℂ)).sub h0).congr (Eventually.of_forall (fun q=>(forcing_return advanced μ hμ a b q).symm)),
    ((hb.const_mul ((b:ℂ)-2*(signedMu advanced μ:ℂ)*Complex.I)).sub h0).congr
      (Eventually.of_forall (fun q=>(input_return advanced μ hμ a b q).symm))⟩
private theorem paired_derivative(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b q:ℝ):
    HasDerivAt (pairedFrequencyKernel advanced μ a b)
      (star (P advanced μ a q)*P advanced μ b q+forcingFrequencyKernel advanced μ a b q+
        inputFrequencyKernel advanced μ a b q) q:=by
  have h:=(((actual_physical_frequency_derivative advanced μ q).mul
    (actual_physical_pole_derivative advanced μ hμ a q)).star).mul
      (actual_physical_pole_derivative advanced μ hμ b q)
  convert! h using 1
  simp only [forcingFrequencyKernel,inputFrequencyKernel,one_mul,star_add,star_mul,Pi.mul_apply]
  ring
private theorem paired_boundary(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Tendsto (pairedFrequencyKernel advanced μ a b) atTop (𝓝 0) ∧
      Tendsto (pairedFrequencyKernel advanced μ a b) atBot (𝓝 0):=by
  have he(q:ℝ):pairedFrequencyKernel advanced μ a b q=
      ((a:ℂ)*star (P advanced μ a q)-1)*P advanced μ b q:=by
    unfold pairedFrequencyKernel
    rw [z_pole advanced μ hμ a q]
    simp only [star_sub,star_mul,star_one,Complex.star_def,Complex.conj_ofReal]
    ring
  constructor
  · simpa only [mul_zero,sub_zero,zero_mul] using
      ((((pole_top advanced μ a).star.const_mul (a:ℂ)).sub_const 1).mul (pole_top advanced μ b)).congr'
        (Eventually.of_forall (fun q=>(he q).symm))
  · simpa only [mul_zero,sub_zero,zero_mul] using
      ((((pole_bot advanced μ a).star.const_mul (a:ℂ)).sub_const 1).mul (pole_bot advanced μ b)).congr'
        (Eventually.of_forall (fun q=>(he q).symm))

/-- The actual two-cause frequency factor has a paired integration-by-parts law. Neither z times a single pole nor its corresponding source leg is assumed square-integrable. -/
theorem actual_paired_frequency_integral(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    (∫q:ℝ,forcingFrequencyKernel advanced μ a b q)=
      -(∫q:ℝ,star (P advanced μ a q)*P advanced μ b q)-
        (∫q:ℝ,inputFrequencyKernel advanced μ a b q):=by
  have hi:=actual_frequency_kernel_integrable advanced μ hμ a b
  have hb:=paired_boundary advanced μ hμ a b
  have h:(∫q:ℝ,star (P advanced μ a q)*P advanced μ b q+
      forcingFrequencyKernel advanced μ a b q+inputFrequencyKernel advanced μ a b q)=0:=by
    simpa only [sub_self] using integral_of_hasDerivAt_of_tendsto
      (fun q=>paired_derivative advanced μ hμ a b q) ((hi.1.add hi.2.1).add hi.2.2) hb.2 hb.1
  have h01:Integrable (fun q:ℝ=>star (P advanced μ a q)*P advanced μ b q+forcingFrequencyKernel advanced μ a b q):=hi.1.add hi.2.1
  rw [integral_add h01 hi.2.2,integral_add hi.1 hi.2.1] at h
  linear_combination h

def forcingDerivativeKernel(advanced:Bool)(μ a b q:ℝ):ℂ:=
  forcingFrequencyKernel advanced μ a b q*P advanced μ b q
def inputDerivativeKernel(advanced:Bool)(μ a b q:ℝ):ℂ:=
  2*inputFrequencyKernel advanced μ a b q*P advanced μ b q

theorem actual_derivative_kernel_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (P advanced μ a q)*(P advanced μ b q)^2) ∧
      Integrable (forcingDerivativeKernel advanced μ a b) ∧ Integrable (inputDerivativeKernel advanced μ a b):=by
  have hi:=actual_frequency_kernel_integrable advanced μ hμ a b
  have hb(q:ℝ):‖P advanced μ b q‖≤μ⁻¹:=pole_bound advanced μ hμ b q
  have h0:=hi.1.mul_bdd (pole_measurable advanced μ hμ b) (Eventually.of_forall hb)
  have h1:=hi.2.1.mul_bdd (pole_measurable advanced μ hμ b) (Eventually.of_forall hb)
  have h2:=(hi.2.2.mul_bdd (pole_measurable advanced μ hμ b) (Eventually.of_forall hb)).const_mul (2:ℂ)
  refine ⟨h0.congr (Eventually.of_forall (fun q=>by dsimp only;ring)),h1,?_⟩
  exact h2.congr (Eventually.of_forall (fun q=>by unfold inputDerivativeKernel;ring))

/-- The differentiated right response has the same paired frequency transport, with its actual second derivative and both ordered pole legs. -/
theorem actual_paired_derivative_integral(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    (∫q:ℝ,forcingDerivativeKernel advanced μ a b q)=
      -(∫q:ℝ,star (P advanced μ a q)*(P advanced μ b q)^2)-
        (∫q:ℝ,inputDerivativeKernel advanced μ a b q):=by
  have hi:=actual_derivative_kernel_integrable advanced μ hμ a b
  have hb:=paired_boundary advanced μ hμ a b
  have hd(q:ℝ):HasDerivAt (fun q:ℝ=>pairedFrequencyKernel advanced μ a b q*P advanced μ b q)
      (star (P advanced μ a q)*(P advanced μ b q)^2+forcingDerivativeKernel advanced μ a b q+
        inputDerivativeKernel advanced μ a b q) q:=by
    have h:=(paired_derivative advanced μ hμ a b q).mul (actual_physical_pole_derivative advanced μ hμ b q)
    convert! h using 1
    simp only [pairedFrequencyKernel,forcingFrequencyKernel,inputFrequencyKernel,forcingDerivativeKernel,inputDerivativeKernel,
      star_mul,star_pow]
    ring
  have htop:Tendsto (fun q:ℝ=>pairedFrequencyKernel advanced μ a b q*P advanced μ b q) atTop (𝓝 0):=by
    simpa only [mul_zero] using hb.1.mul (pole_top advanced μ b)
  have hbot:Tendsto (fun q:ℝ=>pairedFrequencyKernel advanced μ a b q*P advanced μ b q) atBot (𝓝 0):=by
    simpa only [mul_zero] using hb.2.mul (pole_bot advanced μ b)
  have h01:Integrable (fun q:ℝ=>star (P advanced μ a q)*(P advanced μ b q)^2+forcingDerivativeKernel advanced μ a b q):=hi.1.add hi.2.1
  have h:(∫q:ℝ,star (P advanced μ a q)*(P advanced μ b q)^2+
      forcingDerivativeKernel advanced μ a b q+inputDerivativeKernel advanced μ a b q)=0:=by
    simpa only [sub_self] using integral_of_hasDerivAt_of_tendsto hd (h01.add hi.2.2) hbot htop
  rw [integral_add h01 hi.2.2,integral_add hi.1 hi.2.1] at h
  linear_combination h

/-- Positive pole powers retain ordinary L1 for every ordered finite-source pair. The power costs are paid internally at the fixed original frequency. -/
theorem actual_pole_power_pair_integrable(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ)(r s:ℕ):
    Integrable (fun q:ℝ=>star ((P advanced μ a q)^(r+1))*(P advanced μ b q)^(s+1)):=by
  have h0:=pole_pair_integrable advanced μ hμ a b
  have ha:=h0.mul_bdd (c:=(μ⁻¹)^r) ((pole_measurable advanced μ hμ a).star.pow r)
    (Eventually.of_forall (fun q=>by
      simp only [Pi.pow_apply,Pi.star_apply,norm_pow,norm_star]
      exact pow_le_pow_left₀ (norm_nonneg _) (pole_bound advanced μ hμ a q) r))
  have hb:=ha.mul_bdd (c:=(μ⁻¹)^s) ((pole_measurable advanced μ hμ b).pow s)
    (Eventually.of_forall (fun q=>by
      simp only [Pi.pow_apply,norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (pole_bound advanced μ hμ b q) s))
  exact hb.congr (Eventually.of_forall (fun q=>by
    simp only [Pi.pow_apply,Pi.star_apply,star_pow,pow_succ,star_mul]
    ring))
end LowEnergy.InputForceFrequencyPayment
