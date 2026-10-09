import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedJointFrequencyPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedNativeWorkReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualRestReaderFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy SourceScalarPairedTransport SourceClockYukawaCubicCurrent
open SourceScalarPositiveBulkWard SourceJointResidualEnergy SourceResolventBandLimit SourceRetardedGraph
open ActualSylvesterChannels ActualSylvesterCore ActualVectorJointCost
open ActualBalancedForceRetardedPayment ActualLocalizedNativeWorkReturn ActualLocalizedJointFrequencyPayment
open SourceLocalizedInverseFormPayment SourceNativeCutoffContact SourceScalarNativeComparison
open SourceScalarEssentialBudget SourceScalarShiftedBulk ScalarInputJointNoether SourceQuantumScalarChart
open SourcePhysicalKineticSquare
open ActualScalarPhaseJet ActualSecondPressureMagneticPayment SourceCoframeVolume
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair resolventCore sourceMu restReader volumeAction
  diagonalAction scalarBulkComplete nonmagneticSecondField phaseCoefficient

elab "paid_rest_frequency%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedJointFrequencyPayment 0) "LowEnergy") "ActualLocalizedJointFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem single_pair_integrable(advanced:Bool)(F:Index)(L M:End)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourcePair
      (L (resolventCore F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))
      (M (resolventCore F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))) := by
  simp_rw [((paid_rest_frequency% core_channels) advanced F sourceMu
    (paid_rest_frequency% source_mu_positive))]
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hi:=(InputForceFrequencyPayment.actual_frequency_kernel_integrable advanced sourceMu
    (paid_rest_frequency% source_mu_positive) (channelValue F j) (channelValue F i)).1.mul_const
      (sourcePair (L (channelCore F j g)) (M (channelCore F i g)))
  exact hi.congr (Eventually.of_forall (fun w=>by
    simp only [sourcePair]
    have hp(a:ℝ):(paid_rest_frequency% P) advanced sourceMu a w=
      ((a:ℂ)-actualFrequency advanced sourceMu w)⁻¹:=rfl
    rw [hp,hp]
    ring))

private theorem mixed_pair_integrable(advanced:Bool)(F:Index)(T L M:End)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourcePair
      (L (resolventCore F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))
      (M ((paid_rest_frequency% doubleCore) advanced F sourceMu
        (paid_rest_frequency% source_mu_positive) T g w))) := by
  simp_rw [((paid_rest_frequency% double_channels) advanced F sourceMu
    (paid_rest_frequency% source_mu_positive) T g),
    ((paid_rest_frequency% core_channels) advanced F sourceMu (paid_rest_frequency% source_mu_positive))]
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro k _
  have hi:=((paid_rest_frequency% three_poles_integrable) advanced sourceMu
    (paid_rest_frequency% source_mu_positive) (channelValue F k) (channelValue F i) (channelValue F j)).mul_const
      (sourcePair (L (channelCore F k g)) (M (channelCore F i (T (channelCore F j g)))))
  exact hi.congr (Eventually.of_forall (fun w=>by
    simp only [sourcePair]
    ring))

private theorem affine_pair_integrable(advanced:Bool)(F:Index)(T K L M:End)(g:QuantumTest):
    let v:=fun w:ℝ=>(paid_rest_frequency% doubleCore) advanced F sourceMu
      (paid_rest_frequency% source_mu_positive) T g w-
      K (resolventCore F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g)
    Integrable (fun w:ℝ=>sourcePair (L (v w)) (M (v w))) := by
  dsimp only
  have hDD:=(paid_rest_frequency% double_pair_integrable) advanced F sourceMu
    (paid_rest_frequency% source_mu_positive) T L M g
  have hSD:=mixed_pair_integrable advanced F T (L*K) M g
  have hDS:=mixed_pair_integrable advanced F T (M*K) L g
  have hSS:=single_pair_integrable advanced F (L*K) (M*K) g
  have hc:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hDS
  simp only [Module.End.mul_apply] at hSD hDS hSS hc
  apply ((hDD.sub hSD).sub hc).add hSS |>.congr
  apply Eventually.of_forall
  intro w
  let d:QuantumTest:=(paid_rest_frequency% doubleCore) advanced F sourceMu
    (paid_rest_frequency% source_mu_positive) T g w
  let q:QuantumTest:=resolventCore F (actualFrequency advanced sourceMu w)
    ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g
  change sourcePair (L d) (M d)-sourcePair (L (K q)) (M d)-
    star (sourcePair (M (K q)) (L d))+sourcePair (L (K q)) (M (K q))=
    sourcePair (L (d-K q)) (M (d-K q))
  have he(a b:QuantumTest):star (sourcePair a b)=sourcePair b a := by
    unfold sourcePair
    simpa only [starRingEnd_apply] using inner_conj_symm (𝕜:=ℂ) (embed b) (embed a)
  rw [he]
  simp only [sourcePair,map_sub,inner_sub_left,inner_sub_right]
  ring

/-- The source remainder is a single actual one-plus-two-resolvent family.
Both independent complex mixed terms are paid before Noether is integrated. -/
theorem actual_rest_reader_pair_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(L M:End):
    Integrable (fun w:ℝ=>sourcePair
      (L (restReader m ell F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))
      (M (restReader m ell F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))) := by
  have he(w:ℝ):restReader m ell F (actualFrequency advanced sourceMu w)
      ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g=
      (paid_rest_frequency% doubleCore) advanced F sourceMu (paid_rest_frequency% source_mu_positive)
        (nonmagneticSecondField*thetaAction m ell) g w-
      (((4*(phaseCoefficient:ℂ)) • (SourcePhysicalKineticSquare.inverseVolumeAction*thetaAction m ell))
        (resolventCore F (actualFrequency advanced sourceMu w)
          ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g)) := by
    have hp:=actual_localized_reader_principal_return m ell F (actualFrequency advanced sourceMu w)
      ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g
    rw [(paid_rest_frequency% localized_reader_double)] at hp
    simp only [Module.End.mul_apply,LinearMap.smul_apply]
    linear_combination (norm:=module) -hp
  simp_rw [he]
  exact affine_pair_integrable advanced F _ _ L M g

private theorem rest_square_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(L:End):
    Integrable (fun w:ℝ=>‖embed (L (restReader m ell F (actualFrequency advanced sourceMu w)
      ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))‖^2) := by
  have hi:=(actual_rest_reader_pair_integrable advanced m ell F g L L).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2 := by
    simpa only [sourcePair,RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  exact hi.congr (Eventually.of_forall (fun w=>he _))

/-- The complete original scalar Noether price for the actual remainder is
ordinary L1; its real-frequency term is cancelled before integration. -/
theorem actual_rest_reader_noether_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>nativeReaderWard advanced w
      (restReader m ell F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g)) := by
  unfold nativeReaderWard
  simp only [((paid_rest_frequency% opposite_frequency) advanced sourceMu)]
  simp_rw [actual_reader_noether_frequency_cancel]
  have hH:=actual_rest_reader_pair_integrable advanced m ell F g
    (diagonalAction*volumeAction) (scalarBulkComplete*volumeAction)
  have hG:=actual_rest_reader_pair_integrable advanced m ell F g
    volumeAction (geometricScalarCurrent*volumeAction)
  have hB:=actual_rest_reader_pair_integrable advanced m ell F g
    volumeAction (scalarBulkComplete*volumeAction)
  have hN:=rest_square_integrable advanced m ell F g volumeAction
  simp only [Module.End.mul_apply] at hH hG hB
  exact (((hH.im.const_mul (inputCausalSign (!advanced))).sub
    (hG.im.const_mul (inputCausalSign (!advanced)/2))).add (hB.re.const_mul sourceMu)).add
      (hN.const_mul ((sourceTime 0)^2*‖vacuum‖^2))

/-- All seventy source native rows receive the same actual remainder
frequency integral, without a supplied moving-graph price. -/
theorem actual_rest_reader_native_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>nativeScalarEnergy
      (restReader m ell F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g)) := by
  unfold nativeScalarEnergy
  exact integrable_finsetSum Finset.univ (fun i _=>rest_square_integrable advanced m ell F g
    (covariantMomentum (scalarDirection i)))

/-- The source Noether debit is consumed as a genuine whole-frequency
invoice on the original remainder, with its internally generated gap. -/
theorem actual_rest_reader_native_noether_integral(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    sourceTime 0*(∫w:ℝ,nativeScalarEnergy
      (restReader m ell F (actualFrequency advanced sourceMu w)
        ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g)) ≤
      (∫w:ℝ,nativeReaderWard advanced w
        (restReader m ell F (actualFrequency advanced sourceMu w)
          ((paid_rest_frequency% nonreal) advanced sourceMu (paid_rest_frequency% source_mu_positive) w) g))/
          (4*(sourceMu-2*sourceTime 0)) := by
  have hN:=actual_rest_reader_native_integrable advanced m ell F g
  have hW:=actual_rest_reader_noether_integrable advanced m ell F g
  have hi:=integral_mono (hN.const_mul (sourceTime 0)) (hW.div_const (4*(sourceMu-2*sourceTime 0)))
    (fun w=>actual_native_reader_noether_payment advanced w _)
  simpa only [integral_const_mul,integral_div] using hi

end LowEnergy.ActualRestReaderFrequencyPayment
