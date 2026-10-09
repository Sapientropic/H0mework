import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedForceRetardedPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPairedFrequencyKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualLocalizedJointFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy SourceScalarPairedTransport SourceClockYukawaCubicCurrent
open SourceJointResidualEnergy SourceResolventBandLimit SourceRetardedGraph
open ActualSylvesterChannels ActualSylvesterCore ActualSylvesterKernels ActualVectorJointCost
open ActualBalancedForceRetardedPayment ReverseNativeFrequencyWard InputForceFrequencyPayment
open SourceFourPoleEnergyClosed MeasureTheory Filter Lean Meta Elab Term
open SourceLocalizedInverseFormPayment SourceNativeCutoffContact FullYSourceResolventGraphSplice
open SourceScalarPositiveBulkWard
open SourceInverseNoetherChannelGap
open SourceScalarEssentialBudget SourceScalarShiftedBulk ScalarInputJointNoether
open SourceQuantumScalarChart SourceScalarVolumePressure SourceCoframeVolume
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private def P(advanced:Bool)(μ a w:ℝ):ℂ := ((a:ℂ)-actualFrequency advanced μ w)⁻¹
attribute [local irreducible] sourcePair resolventCore localizedPressureReader thetaAction
  ActualSecondPressureMagneticPayment.nonmagneticSecondField sourceMu
  scalarBulkComplete diagonalAction volumeAction

elab "paid_joint_pole%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPairedFrequencyKernel 0) "LowEnergy") "InputForceFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem opposite_pole(advanced:Bool)(μ a w:ℝ):
    P (!advanced) μ a w=star (P advanced μ a w) := by
  cases advanced
  · change ((a:ℂ)-star (line μ w))⁻¹=star (((a:ℂ)-line μ w)⁻¹)
    rw [star_inv₀,star_sub]
    simp only [Complex.star_def,Complex.conj_ofReal]
  · change ((a:ℂ)-line μ w)⁻¹=star (((a:ℂ)-star (line μ w))⁻¹)
    rw [star_inv₀,star_sub,star_star]
    simp only [Complex.star_def,Complex.conj_ofReal]

private theorem four_poles_integrable(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(a b c d:ℝ):
    Integrable (fun w:ℝ=>star (P (!advanced) μ a w*P advanced μ b w)*
      (P (!advanced) μ c w*P advanced μ d w)) := by
  have h0:Integrable (fun w:ℝ=>star (P advanced μ b w)*P advanced μ d w):=
    (paid_joint_pole% pole_pair_integrable) advanced μ hμ b d
  have ha:=h0.mul_bdd (c:=μ⁻¹)
    ((paid_joint_pole% pole_measurable) advanced μ hμ a)
    (Eventually.of_forall (fun w=>(paid_joint_pole% pole_bound) advanced μ hμ a w))
  have hc:=ha.mul_bdd (c:=μ⁻¹)
    ((paid_joint_pole% pole_measurable) advanced μ hμ c).star
    (Eventually.of_forall (fun w=>by
      simpa only [Pi.star_apply,norm_star] using (paid_joint_pole% pole_bound) advanced μ hμ c w))
  exact hc.congr (Eventually.of_forall (fun w=>by
    change star (P advanced μ b w)*P advanced μ d w*P advanced μ a w*star (P advanced μ c w)=
      star (P (!advanced) μ a w*P advanced μ b w)*(P (!advanced) μ c w*P advanced μ d w)
    rw [opposite_pole,opposite_pole,star_mul,star_star]
    ring))

private theorem three_poles_integrable(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(a b c:ℝ):
    Integrable (fun w:ℝ=>star (P advanced μ a w)*
      (P (!advanced) μ b w*P advanced μ c w)) := by
  have h0:Integrable (fun w:ℝ=>star (P advanced μ a w)*P advanced μ c w):=
    (paid_joint_pole% pole_pair_integrable) advanced μ hμ a c
  have hb:=h0.mul_bdd (c:=μ⁻¹)
    ((paid_joint_pole% pole_measurable) advanced μ hμ b).star
    (Eventually.of_forall (fun w=>by
      simpa only [Pi.star_apply,norm_star] using (paid_joint_pole% pole_bound) advanced μ hμ b w))
  exact hb.congr (Eventually.of_forall (fun w=>by
    change star (P advanced μ a w)*P advanced μ c w*star (P advanced μ b w)=
      star (P advanced μ a w)*(P (!advanced) μ b w*P advanced μ c w)
    rw [opposite_pole]
    ring))

private theorem nonreal(advanced:Bool)(μ:ℝ)(hμ:0 < μ)(w:ℝ):
    (actualFrequency advanced μ w).im≠0 := reverse_frequency_nonreal advanced μ hμ w

private theorem core_channels(advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(w:ℝ)(g:QuantumTest):
    resolventCore F (actualFrequency advanced μ w) (nonreal advanced μ hμ w) g=
      ∑i:Channel F,P advanced μ (channelValue F i) w • channelCore F i g := by
  unfold resolventCore
  change state F (actualFrequency advanced μ w) (nonreal advanced μ hμ w) (coreEquiv g)=_
  rw [actual_state_channels]
  apply Finset.sum_congr rfl
  intro i _
  cases advanced <;> rfl

private def doubleCore(advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(T:End)(g:QuantumTest)(w:ℝ):QuantumTest :=
  resolventCore F (actualFrequency (!advanced) μ w) (nonreal (!advanced) μ hμ w)
    (T (resolventCore F (actualFrequency advanced μ w) (nonreal advanced μ hμ w) g))

private theorem double_channels(advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)(T:End)(g:QuantumTest)(w:ℝ):
    doubleCore advanced F μ hμ T g w=
      ∑i:Channel F,∑j:Channel F,(P (!advanced) μ (channelValue F i) w*
        P advanced μ (channelValue F j) w) • channelCore F i (T (channelCore F j g)) := by
  unfold doubleCore
  rw [core_channels (!advanced) F μ hμ w,core_channels advanced F μ hμ w]
  simp only [map_sum,map_smul,Finset.smul_sum,smul_smul]

private theorem double_pair_integrable(advanced:Bool)(F:Index)(μ:ℝ)(hμ:0 < μ)
    (T L M:End)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourcePair (L (doubleCore advanced F μ hμ T g w))
      (M (doubleCore advanced F μ hμ T g w))) := by
  simp_rw [double_channels]
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro k _
  apply integrable_finsetSum Finset.univ
  intro l _
  have hi:=(four_poles_integrable advanced μ hμ (channelValue F k) (channelValue F l)
    (channelValue F i) (channelValue F j)).mul_const
      (sourcePair (L (channelCore F k (T (channelCore F l g))))
        (M (channelCore F i (T (channelCore F j g)))))
  apply hi.congr
  apply Eventually.of_forall
  intro w
  simp only [sourcePair]
  ring

private theorem opposite_frequency(advanced:Bool)(μ w:ℝ):
    star (actualFrequency advanced μ w)=actualFrequency (!advanced) μ w := by
  cases advanced <;> simp only [actualFrequency,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,star_star]

private theorem source_mu_positive:0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large

private theorem resolvent_congr(F:Index)(z u:ℂ)(hz:z.im≠0)(hu:u.im≠0)(he:z=u):
    resolventCore F z hz=resolventCore F u hu := by
  subst u
  rfl

private theorem localized_reader_double(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):
    localizedPressureReader m ell F (actualFrequency advanced sourceMu w)
      (nonreal advanced sourceMu source_mu_positive w) g=
      doubleCore advanced F sourceMu source_mu_positive
        (ActualSecondPressureMagneticPayment.nonmagneticSecondField*thetaAction m ell) g w := by
  have hz:(star (actualFrequency advanced sourceMu w)).im≠0 := by
    simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using
      nonreal advanced sourceMu source_mu_positive w
  have he:=resolvent_congr F (star (actualFrequency advanced sourceMu w))
    (actualFrequency (!advanced) sourceMu w) hz (nonreal (!advanced) sourceMu source_mu_positive w)
    (opposite_frequency advanced sourceMu w)
  unfold localizedPressureReader doubleCore
  simp only [Module.End.mul_apply]
  rw [he]

/-- Every unbounded native word is evaluated on the actual double-resolvent
source orbit, with the escape channel retained; no graph budget is supplied. -/
theorem actual_localized_reader_pair_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)
    (L M:End):
    Integrable (fun w:ℝ=>sourcePair
      (L (localizedPressureReader m ell F (actualFrequency advanced sourceMu w)
        (nonreal advanced sourceMu source_mu_positive w) g))
      (M (localizedPressureReader m ell F (actualFrequency advanced sourceMu w)
        (nonreal advanced sourceMu source_mu_positive w) g))) := by
  simp_rw [localized_reader_double]
  exact double_pair_integrable advanced F sourceMu source_mu_positive _ L M g

/-- The same original two-resolvent orbit supplies every source operator
pair, including both ordered compensated readers. -/
theorem actual_two_resolvent_source_pair_integrable(advanced:Bool)(F:Index)(T L M:End)(g:QuantumTest):
    let u:=fun w:ℝ=>resolventCore F (actualFrequency (!advanced) sourceMu w)
      (nonreal (!advanced) sourceMu source_mu_positive w)
      (T (resolventCore F (actualFrequency advanced sourceMu w)
        (nonreal advanced sourceMu source_mu_positive w) g))
    Integrable (fun w:ℝ=>sourcePair (L (u w)) (M (u w))) := by
  exact double_pair_integrable advanced F sourceMu source_mu_positive T L M g

private theorem scalar_pair_im_zero(d:QuantumTest):
    (sourcePair d (scalarBulkComplete d)).im=0 := by
  have hs:=original_scalar_pair d d
  have hc:=congrArg Complex.im (pair_conjugate d (scalarBulkComplete d))
  rw [←hs] at hc
  simp only [Complex.conj_im] at hc
  linarith only [hc]

/-- Real-frequency forcing is cancelled inside the actual selfadjoint
scalar Ward pair before any term is integrated. -/
theorem actual_reader_noether_frequency_cancel(advanced:Bool)(μ w:ℝ)(d:QuantumTest):
    inputScalarWardPrice advanced d (diagonalAction d-actualFrequency advanced μ w • d)=
      inputCausalSign advanced*(sourcePair (diagonalAction d) (scalarBulkComplete d)).im-
      (inputCausalSign advanced/2)*(sourcePair d (geometricScalarCurrent d)).im+
      μ*(sourcePair d (scalarBulkComplete d)).re+
      (sourceTime 0)^2*‖vacuum‖^2*‖embed d‖^2 := by
  have hz:=scalar_pair_im_zero d
  unfold inputScalarWardPrice
  change inputCausalSign advanced*((sourcePair
    (diagonalAction d-actualFrequency advanced μ w • d) (scalarBulkComplete d)).im-
      (sourcePair d (geometricScalarCurrent d)).im/2)+
    (sourceTime 0)^2*‖vacuum‖^2*‖embed d‖^2=_
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left]
  rw [starRingEnd_apply]
  simp only [Complex.sub_im,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  simp only [sourcePair] at hz
  simp only [hz,mul_zero,zero_add]
  cases advanced <;>
    simp only [inputCausalSign,actualFrequency,Bool.false_eq_true,ite_false,ite_true,
      Complex.star_def,Complex.conj_im,line_im]
  · ring
  · ring

/-- The actual reader's source Noether current is ordinary L1 on the whole
frequency line, including every finite and escape source column. -/
theorem actual_two_resolvent_source_noether_integrable(advanced:Bool)(F:Index)(T:End)(g:QuantumTest):
    let u:=fun w:ℝ=>resolventCore F (actualFrequency (!advanced) sourceMu w)
      (nonreal (!advanced) sourceMu source_mu_positive w)
      (T (resolventCore F (actualFrequency advanced sourceMu w)
        (nonreal advanced sourceMu source_mu_positive w) g))
    let d:=fun w:ℝ=>volumeAction (u w)
    Integrable (fun w:ℝ=>inputScalarWardPrice (!advanced) (d w)
      (diagonalAction (d w)-actualFrequency (!advanced) sourceMu w • d w)) := by
  dsimp only
  simp_rw [actual_reader_noether_frequency_cancel]
  have hH:=double_pair_integrable advanced F sourceMu source_mu_positive T
    (diagonalAction*volumeAction) (scalarBulkComplete*volumeAction) g
  have hG:=double_pair_integrable advanced F sourceMu source_mu_positive T
    volumeAction (geometricScalarCurrent*volumeAction) g
  have hB:=double_pair_integrable advanced F sourceMu source_mu_positive T
    volumeAction (scalarBulkComplete*volumeAction) g
  have hN:=double_pair_integrable advanced F sourceMu source_mu_positive T volumeAction volumeAction g
  have hn:Integrable (fun w:ℝ=>‖embed (volumeAction (doubleCore advanced F sourceMu source_mu_positive T g w))‖^2) := by
    have hi:=hN.re
    have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2 := by
      simpa only [sourcePair,RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
    exact hi.congr (Eventually.of_forall (fun w=>he _))
  simp only [Module.End.mul_apply] at hH hG hB
  exact (((hH.im.const_mul (inputCausalSign (!advanced))).sub
    (hG.im.const_mul (inputCausalSign (!advanced)/2))).add (hB.re.const_mul sourceMu)).add
      (hn.const_mul ((sourceTime 0)^2*‖vacuum‖^2))

end LowEnergy.ActualLocalizedJointFrequencyPayment
