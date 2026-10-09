import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureWardPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRestReaderFrequencyPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedPressureFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceClockYukawaCubicCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceNativeCutoffContact SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceQuantumScalarChart
open GaussNativeEnergy SourceRetardedGraph
open SourceJointResidualEnergy
open ActualSylvesterChannels ActualSylvesterCore ActualVectorJointCost
open ActualBalancedPressureWardPayment ActualBalancedForceRetardedPayment
open ActualNonmagneticPressureStorage ActualSecondPressureMagneticPayment
open ActualLocalizedNativeWorkReturn ActualBalancedLocalizationContactReturn
open ActualNativeOwnSquareWardPayment ActualScalarPhaseJet
open MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair resolventCore sourceMu thetaAction
  sourceSquareField nonmagneticSecondField phaseCoefficient sourceTime
  balancedPressureJet balancedPressurePrice nonmagneticStorage

elab "paid_pressure_frequency%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualLocalizedJointFrequencyPayment 0) "LowEnergy") "ActualLocalizedJointFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_pressure_single%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualRestReaderFrequencyPayment 0) "LowEnergy") "ActualRestReaderFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns "single_pair_integrable")
elab "paid_pressure_pole%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPairedFrequencyKernel 0) "LowEnergy") "InputForceFrequencyPayment"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem nonreal(advanced:Bool)(w:ℝ):(actualFrequency advanced sourceMu w).im≠0 :=
  (paid_pressure_frequency% nonreal) advanced sourceMu (paid_pressure_frequency% source_mu_positive) w
private def q(advanced:Bool)(F:Index)(g:QuantumTest)(w:ℝ):QuantumTest :=
  resolventCore F (actualFrequency advanced sourceMu w) (nonreal advanced w) g
private def doubleSame(advanced:Bool)(F:Index)(T:End)(g:QuantumTest)(w:ℝ):QuantumTest :=
  resolventCore F (actualFrequency advanced sourceMu w) (nonreal advanced w) (T (q advanced F g w))

private theorem triple_integrable(advanced:Bool)(a b c:ℝ):
    Integrable (fun w:ℝ=>star ((paid_pressure_frequency% P) advanced sourceMu a w)*
      ((paid_pressure_frequency% P) advanced sourceMu b w*(paid_pressure_frequency% P) advanced sourceMu c w)) := by
  have h0:=(InputForceFrequencyPayment.actual_frequency_kernel_integrable advanced sourceMu
    (paid_pressure_frequency% source_mu_positive) a c).1
  have hi:=h0.mul_bdd (c:=sourceMu⁻¹)
    ((paid_pressure_pole% pole_measurable) advanced sourceMu (paid_pressure_frequency% source_mu_positive) b)
    (Eventually.of_forall (fun w=>(paid_pressure_pole% pole_bound) advanced sourceMu
      (paid_pressure_frequency% source_mu_positive) b w))
  exact hi.congr (Eventually.of_forall (fun w=>by
    change star (((a:ℂ)-actualFrequency advanced sourceMu w)⁻¹)*
      (((c:ℂ)-actualFrequency advanced sourceMu w)⁻¹)*(((b:ℂ)-actualFrequency advanced sourceMu w)⁻¹)=
      star (((a:ℂ)-actualFrequency advanced sourceMu w)⁻¹)*
        ((((b:ℂ)-actualFrequency advanced sourceMu w)⁻¹)*(((c:ℂ)-actualFrequency advanced sourceMu w)⁻¹))
    ring))

private theorem mixed_integrable(advanced:Bool)(F:Index)(T L M:End)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourcePair (L (q advanced F g w)) (M (doubleSame advanced F T g w))) := by
  unfold doubleSame q
  simp_rw [((paid_pressure_frequency% core_channels) advanced F sourceMu
    (paid_pressure_frequency% source_mu_positive))]
  simp only [map_sum,map_smul,Finset.smul_sum,smul_smul,sourcePair,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,starRingEnd_apply,Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro k _
  have hi:=(triple_integrable advanced (channelValue F k) (channelValue F i) (channelValue F j)).mul_const
    (sourcePair (L (channelCore F k g)) (M (channelCore F i (T (channelCore F j g)))))
  exact hi.congr (Eventually.of_forall (fun w=>by simp only [sourcePair];ring))

private theorem norm_integrable(advanced:Bool)(F:Index)(L:End)(g:QuantumTest):
    Integrable (fun w:ℝ=>‖embed (L (q advanced F g w))‖^2) := by
  have hi:=((paid_pressure_single%) advanced F L L g).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2 := by
    simpa only [sourcePair,RCLike.re_to_complex] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  exact hi.congr (Eventually.of_forall (fun w=>he _))

/-- The genuine A-pressure and its vacuum return are ordinary L1 on the
original finite-plus-escape source orbit. -/
theorem actual_balanced_pressure_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>balancedPressurePrice (thetaAction m ell (q advanced F g w))) := by
  have hi:=((paid_pressure_single%) advanced F (thetaAction m ell)
    (balancedPressureJet nonmagneticSecondField*thetaAction m ell) g).re
  have hn:=norm_integrable advanced F (thetaAction m ell) g
  simp only [Module.End.mul_apply] at hi
  unfold balancedPressurePrice
  exact (hi.const_mul (-(1/(2*phaseCoefficient)))).add
    (hn.const_mul (3*sourceTime 0*‖vacuum‖^2/2))

theorem actual_nonmagnetic_storage_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>nonmagneticStorage (thetaAction m ell (q advanced F g w))) := by
  have hi:=((paid_pressure_single%) advanced F (thetaAction m ell)
    (nonmagneticSecondField*thetaAction m ell) g).re
  have hn:=norm_integrable advanced F (thetaAction m ell) g
  simp only [Module.End.mul_apply] at hi
  simp_rw [actual_nonmagnetic_storage_source]
  exact (hi.const_mul (-(1/(2*phaseCoefficient)))).add
    (hn.const_mul (sourceTime 0*‖vacuum‖^2/2))

/-- The actual whole Native/Own insertion has three genuine resolvent poles;
the source square and complete CF commutator stay in the source coefficient. -/
theorem actual_native_own_flux_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>nativeOwnFlux m ell F (actualFrequency advanced sourceMu w)
      (nonreal advanced w) g) := by
  have hi:=mixed_integrable advanced F
    (compressionCore F*sourceSquareField-sourceSquareField*compressionCore F)
    (thetaAction m ell) (thetaAction m ell) g
  exact hi.congr (Eventually.of_forall (fun _=>rfl))

private theorem balanced_pair_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>balancedPressure m ell F (actualFrequency advanced sourceMu w)
      (nonreal advanced w) g) := by
  have h1:=mixed_integrable advanced F (ReverseScalarGaugeWard.balancedCompressionForce F)
    (thetaAction m ell*nonmagneticSecondField) (thetaAction m ell) g
  have h2:=mixed_integrable advanced F (ReverseScalarGaugeWard.balancedCompressionForce F)
    (thetaAction m ell) (thetaAction m ell*nonmagneticSecondField) g
  have hs(a b:QuantumTest):(sourcePair a b).re=(sourcePair b a).re := by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  simp only [Module.End.mul_apply] at h1 h2
  apply ((h1.re.add h2.re).const_mul (1/12:ℝ)).congr
  apply Eventually.of_forall
  intro w
  unfold balancedPressure
  dsimp only
  rw [hs]
  rfl

/-- This source invoice is paid as a complete ordered real function before
its BF fixed-contact tail or further moment tails are consumed. -/
theorem actual_source_native_invoice_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (fun w:ℝ=>sourceNativeInvoice m ell F (actualFrequency advanced sourceMu w)
      (nonreal advanced w) g) := by
  have hi:=actual_native_own_flux_integrable advanced m ell F g
  have hp:=balanced_pair_integrable advanced m ell F g
  apply (hi.re.sub hp).congr
  apply Eventually.of_forall
  intro w
  change (nativeOwnFlux m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g).re-
    balancedPressure m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g=
      sourceNativeInvoice m ell F (actualFrequency advanced sourceMu w) (nonreal advanced w) g
  have he:=actual_whole_source_native_invoice m ell F
    (actualFrequency advanced sourceMu w) (nonreal advanced w) g
  linarith only [he]

/-- The actual generated pressure price directly transports its three-storage
coercivity into the whole-frequency integral with no integral hypothesis. -/
theorem actual_balanced_pressure_storage_integral(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    3*(∫w:ℝ,nonmagneticStorage (thetaAction m ell (q advanced F g w))) ≤
      ∫w:ℝ,balancedPressurePrice (thetaAction m ell (q advanced F g w)) := by
  have hs:=actual_nonmagnetic_storage_integrable advanced m ell F g
  have hp:=actual_balanced_pressure_integrable advanced m ell F g
  rw [←integral_const_mul]
  exact integral_mono (hs.const_mul 3) hp (fun w=>actual_balanced_pressure_storage_price _)

/-- The complete physical source return is integrated as one signed
responsibility. The positive pressure stays on the same left side. -/
theorem actual_whole_native_pressure_integral(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    let returnSource:=fun ω:ℝ=>
      let z:=actualFrequency advanced sourceMu ω
      let hz:=nonreal advanced ω
      let w:=thetaAction m ell (q advanced F g ω)
      let u:=compensatedReader m ell F z hz g
      sourceNativeInvoice m ell F z hz g+
        (1/6:ℝ)*((sourcePair (thetaAction m ell (resolventCore F z hz (balancedGenerator g)))
          (nonmagneticSecondField w)).re-18*(sourcePair u (compressionCore F (q advanced F g ω))).re+
          (sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) (q advanced F g ω))
            (nonmagneticSecondField w)).re+
          (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed w‖^2)+
        radialBalancedContact m ell F z hz g
    Integrable returnSource ∧
      (∫ω:ℝ,(nativeOwnFlux m ell F (actualFrequency advanced sourceMu ω) (nonreal advanced ω) g).re)+
        (phaseCoefficient/6)*(∫ω:ℝ,balancedPressurePrice (thetaAction m ell (q advanced F g ω)))=
        ∫ω:ℝ,returnSource ω := by
  dsimp only
  have hn:Integrable (fun ω:ℝ=>(nativeOwnFlux m ell F (actualFrequency advanced sourceMu ω)
      (nonreal advanced ω) g).re) := by
    simpa only [RCLike.re_to_complex] using (actual_native_own_flux_integrable advanced m ell F g).re
  have hp:=(actual_balanced_pressure_integrable advanced m ell F g).const_mul (phaseCoefficient/6)
  have he(ω:ℝ):
      (nativeOwnFlux m ell F (actualFrequency advanced sourceMu ω) (nonreal advanced ω) g).re+
        (phaseCoefficient/6)*balancedPressurePrice (thetaAction m ell (q advanced F g ω))=_ :=
    actual_whole_native_pressure_return m ell F (actualFrequency advanced sourceMu ω) (nonreal advanced ω) g
  refine ⟨(hn.add hp).congr (Eventually.of_forall he),?_⟩
  rw [←integral_const_mul,←integral_add hn hp]
  exact integral_congr_ae (Eventually.of_forall he)

end LowEnergy.ActualBalancedPressureFrequencyPayment
