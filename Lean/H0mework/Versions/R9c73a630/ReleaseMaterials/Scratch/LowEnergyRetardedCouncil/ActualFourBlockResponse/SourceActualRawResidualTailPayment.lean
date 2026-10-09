import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualExactSylvesterRawFrequencyBalance
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardPositivePrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualRawResidualTailPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeEnergy GaussNativeForm SourceQuantumScalarChart SourceCutoffDilationWard
open SourceClockYukawaCubicCurrent SourceJointResidualEnergy
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarInverseNativeEnergy
open SourceMixedNativeReturn SourcePhysicalKineticSquare SourceScalarVirialBulk SourceRetardedGraph
open ActualTwoResolventCascade ActualMixedWardPositivePrice ActualTwoResolventSylvester
open ActualVectorJointCost SourceResolventBandLimit FullYSourceResolventGraphSplice MeasureTheory
open ActualExactSylvesterRawFrequencyBalance ActualSylvesterMixedFrequency
open Lean Meta Elab Term
open scoped InnerProductSpace BigOperators

private theorem lapse_positive : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem source_mu_positive : 0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large
private theorem coefficient_nonnegative (sharp : Bool) : 0 ≤ coefficientCost sharp :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem asymmetric_square {V : Type*} [NormedAddCommGroup V] (x y : V) :
    ‖x+y‖^2 ≤ 3*‖x‖^2+(3/2:ℝ)*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖/2)]

/-- The literal half-vacuum completion uses half of the old shifted-field reserve. -/
theorem actual_half_vacuum_shifted_price (sharp : Bool) (f : QuantumTest) :
    ‖embed (fullAction sharp f)‖^2 ≤
      (3/2:ℝ)*coefficientCost sharp*shiftedMoment f+
      (3/4:ℝ)*‖constantBounded sharp vacuum‖^2*‖embed f‖^2 := by
  have hv := pow_le_pow_left₀ (norm_nonneg _) ((constantBounded sharp vacuum).le_opNorm (embed f)) 2
  rw [mul_pow,constant_bounded_core] at hv
  have hx : ‖embed ((1/2:ℂ) • constantAction sharp vacuum f)‖^2 ≤
      (1/4:ℝ)*‖constantBounded sharp vacuum‖^2*‖embed f‖^2 := by
    simp only [map_smul,norm_smul,mul_pow]
    norm_num
    nlinarith only [hv]
  have hy := actual_shifted_Y_price sharp f
  have ha := asymmetric_square (embed ((1/2:ℂ) • constantAction sharp vacuum f))
    (embed (shiftedY sharp f))
  rw [actual_half_vacuum_split,LinearMap.add_apply,LinearMap.smul_apply,map_add]
  nlinarith only [hx,hy,ha]

/-- All positive native and gauge slots of the actual inverse source remain in one reserve. -/
def sourceReserve (sharp : Bool) (m ell : ℕ) (f : QuantumTest) : ℝ :=
  let t := SourceNativeCutoffContact.thetaAction m ell f
  (3/4:ℝ)*coefficientCost sharp*inverseNativeEnergy t+
    (27*coefficientCost sharp/(4*sourceTime 0))*
      (sourcePair (inverseRootAction t) (gaugeKinetic (inverseRootAction t))).re+
    ((3/8:ℝ)*coefficientCost sharp*‖vacuum‖^2+(3/2:ℝ)*sourceMu^2)*‖embed t‖^2

private theorem actual_Q_reserve_identity (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    (3/2:ℝ)*sourceMu^2*sourceQ sharp m ell f = sourceReserve sharp m ell f+
      (3/2:ℝ)*coefficientCost sharp*shiftedMoment (SourceNativeCutoffContact.thetaAction m ell f)+
      (3/4:ℝ)*‖constantBounded sharp vacuum‖^2*
        ‖embed (SourceNativeCutoffContact.thetaAction m ell f)‖^2 := by
  unfold sourceQ bulkCoefficient normCoefficient sourceReserve
  dsimp only
  rw [original_inverse_energy]
  field_simp [lapse_positive.ne',source_mu_positive.ne']
  ring

/-- Actual CAR, half-vacuum, and the exact inverse source internally pay the stronger Q budget. -/
theorem actual_increment_source_reserve (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    ‖embed (literalIncrementAction sharp m ell f)‖^2+sourceReserve sharp m ell f ≤
      (3/2:ℝ)*sourceMu^2*sourceQ sharp m ell f := by
  rw [actual_increment_core,actual_Q_reserve_identity]
  have h := actual_half_vacuum_shifted_price sharp (SourceNativeCutoffContact.thetaAction m ell f)
  linarith only [h]

theorem actual_source_reserve_nonnegative (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    (3/2:ℝ)*sourceMu^2*‖embed (SourceNativeCutoffContact.thetaAction m ell f)‖^2 ≤
      sourceReserve sharp m ell f := by
  have hc := coefficient_nonnegative sharp
  have hn := lapse_positive
  have hnative : 0 ≤ inverseNativeEnergy (SourceNativeCutoffContact.thetaAction m ell f) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hg := original_gauge_kinetic_nonnegative
    (inverseRootAction (SourceNativeCutoffContact.thetaAction m ell f))
  unfold sourceReserve
  dsimp only
  have hp := mul_nonneg (show 0 ≤ (3/4:ℝ)*coefficientCost sharp by positivity) hnative
  have hq := mul_nonneg (show 0 ≤ 27*coefficientCost sharp/(4*sourceTime 0) by positivity) hg
  have hr := mul_nonneg (show 0 ≤ (3/8:ℝ)*coefficientCost sharp*‖vacuum‖^2 by positivity)
    (sq_nonneg ‖embed (SourceNativeCutoffContact.thetaAction m ell f)‖)
  nlinarith only [hp,hq,hr]


private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair sourceMu compressionCore resolventCore sourceQAction inverseForm

elab "paid_raw_payment%" field:ident : term => do
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualExactSylvesterRawFrequencyBalance 0) "LowEnergy")
    "ActualExactSylvesterRawFrequencyBalance"
  let name := Name.str ns field.getId.eraseMacroScopes.toString
  unless (← getEnv).contains name do throwError "Missing original raw source frequency proof"
  mkConstWithFreshMVarLevels name

private theorem causal_nonreal (advanced : Bool) (w : ℝ) :
    (causalFrequency advanced sourceMu w).im ≠ 0 := by
  cases advanced <;> simpa [causalFrequency,line_im] using source_mu_positive.ne'

private def causalCore (advanced : Bool) (F : Index) (g : QuantumTest) (w : ℝ) : QuantumTest :=
  resolventCore F (causalFrequency advanced sourceMu w) (causal_nonreal advanced w) g

def QFrequency (advanced sharp : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) (w : ℝ) : ℝ :=
  sourceQ sharp m ell (causalCore advanced F g w)

def reserveFrequency (advanced sharp : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) (w : ℝ) : ℝ :=
  sourceReserve sharp m ell (causalCore advanced F g w)

/-- The current remains the complete original CF commutator, including its own defect. -/
def QCurrentFrequency (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (g : QuantumTest) (w : ℝ) : ℝ :=
  let q := causalCore advanced F g w
  let Q : End := (2:ℂ) • sourceQAction sharp m ell
  (sourcePair q ((Complex.I*(ActualTwoResolventCascade.causalSign advanced : ℂ)) •
    (compressionCore F*Q-Q*compressionCore F) q)).re

private theorem core_reader_continuous (advanced : Bool) (F : Index) (g : QuantumTest) (A : End) :
    Continuous (fun w : ℝ => embed (A (causalCore advanced F g w))) := by
  have hs (w : ℝ) := (paid_raw_payment% core_resolvent_channels)
    advanced F sourceMu source_mu_positive w g
  have he : (fun w : ℝ => embed (A (causalCore advanced F g w))) =
      fun w => ∑ i : Channel F,pole (if advanced then -sourceMu else sourceMu)
        (channelValue F i) w • embed (A (ActualSylvesterCore.channelCore F i g)) := by
    funext w
    unfold causalCore
    rw [hs]
    simp only [map_sum,map_smul]
  rw [he]
  apply continuous_finsetSum
  intro i _
  have hp : Continuous (fun w : ℝ => pole (if advanced then -sourceMu else sourceMu)
      (channelValue F i) w) := by
    unfold pole line
    apply Continuous.inv₀
    · fun_prop
    · intro w h
      have hi := congrArg Complex.im h
      cases advanced <;>
        norm_num only [Bool.false_eq_true,ite_false,ite_true,Complex.ofReal_neg,
          Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,Complex.neg_re,
          Complex.I_re,Complex.I_im,Complex.zero_im,zero_sub,mul_zero,zero_mul,
          mul_one,zero_add,add_zero,neg_neg] at hi <;>
        exact source_mu_positive.ne' (by linarith only [hi])
  let B : ℂ →L[ℂ] H := (ContinuousLinearMap.id ℂ ℂ).smulRight
    (embed (A (ActualSylvesterCore.channelCore F i g)))
  have hb := B.continuous.comp hp
  have hb' : ((B : ℂ → H) ∘ (fun w : ℝ => pole (if advanced then -sourceMu else sourceMu)
      (channelValue F i) w)) = fun w : ℝ => pole (if advanced then -sourceMu else sourceMu)
        (channelValue F i) w • embed (A (ActualSylvesterCore.channelCore F i g)) := by
    funext w
    rfl
  rw [hb'] at hb
  exact hb

private theorem Q_frequency_integrable (advanced sharp : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) :
    Integrable (QFrequency advanced sharp m ell F g) := by
  have hi := ((paid_raw_payment% core_pair_integrable) advanced F sourceMu source_mu_positive
    (sourceQAction sharp m ell) g).re
  simp only [RCLike.re_to_complex] at hi
  refine hi.congr (Filter.Eventually.of_forall (fun w => ?_))
  change (sourcePair (causalCore advanced F g w)
    (sourceQAction sharp m ell (causalCore advanced F g w))).re = _
  exact (paid_raw_source_Q_energy%) sharp m ell _

private theorem reserve_frequency_continuous (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Continuous (reserveFrequency advanced sharp m ell F g) := by
  let T := SourceNativeCutoffContact.thetaAction m ell
  have ht := core_reader_continuous advanced F g T
  have hn (a : GaussNativeForm.ScalarIndex) := core_reader_continuous advanced F g
    (inverseVolumeAction*GaussCoreDifferential.covariantMomentum (GaussNativeForm.scalarDirection a)*T)
  have hu := core_reader_continuous advanced F g (inverseRootAction*T)
  have hg := core_reader_continuous advanced F g (gaugeKinetic*inverseRootAction*T)
  unfold reserveFrequency sourceReserve inverseNativeEnergy sourcePair
  change Continuous (fun w : ℝ =>
    (3/4:ℝ)*coefficientCost sharp*(∑ a : GaussNativeForm.ScalarIndex,
      ‖embed (inverseVolumeAction (GaussCoreDifferential.covariantMomentum (GaussNativeForm.scalarDirection a)
        (T (causalCore advanced F g w))))‖^2)+
      (27*coefficientCost sharp/(4*sourceTime 0))*(inner ℂ
        (embed (inverseRootAction (T (causalCore advanced F g w))))
        (embed (gaugeKinetic (inverseRootAction (T (causalCore advanced F g w)))))).re+
      ((3/8:ℝ)*coefficientCost sharp*‖vacuum‖^2+(3/2:ℝ)*sourceMu^2)*
        ‖embed (T (causalCore advanced F g w))‖^2)
  have hc : Continuous (fun w : ℝ => inner ℂ
      (embed (inverseRootAction (T (causalCore advanced F g w))))
      (embed (gaugeKinetic (inverseRootAction (T (causalCore advanced F g w)))))) := hu.inner hg
  have hgre := Complex.continuous_re.comp hc
  exact ((continuous_const.mul (continuous_finsetSum _
    (fun a _ => (hn a).norm.pow 2))).add
      (continuous_const.mul hgre)).add (continuous_const.mul (ht.norm.pow 2))

private theorem reserve_frequency_integrable (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Integrable (reserveFrequency advanced sharp m ell F g) := by
  have hi := (Q_frequency_integrable advanced sharp m ell F g).const_mul ((3/2:ℝ)*sourceMu^2)
  apply hi.mono' (reserve_frequency_continuous advanced sharp m ell F g).aestronglyMeasurable
  filter_upwards [] with w
  have h := actual_increment_source_reserve sharp m ell (causalCore advanced F g w)
  have hn := actual_source_reserve_nonnegative sharp m ell (causalCore advanced F g w)
  have hz : 0 ≤ sourceReserve sharp m ell (causalCore advanced F g w) :=
    (by positivity : 0 ≤ (3/2:ℝ)*sourceMu^2*‖embed (SourceNativeCutoffContact.thetaAction m ell
      (causalCore advanced F g w))‖^2).trans hn
  change ‖sourceReserve sharp m ell (causalCore advanced F g w)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg hz]
  exact (le_add_of_nonneg_left (sq_nonneg _)).trans h

private def DFrequency (advanced sharp : Bool) (m ell : ℕ) (F : Index)
    (g : QuantumTest) (w : ℝ) : ℝ :=
  ‖embed (literalIncrementAction sharp m ell (causalCore advanced F g w))‖^2

private theorem D_frequency_integrable (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Integrable (DFrequency advanced sharp m ell F g) := by
  have hi := (Q_frequency_integrable advanced sharp m ell F g).const_mul ((3/2:ℝ)*sourceMu^2)
  have hc := (core_reader_continuous advanced F g (literalIncrementAction sharp m ell)).norm.pow 2
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := actual_increment_source_reserve sharp m ell (causalCore advanced F g w)
  have hn := actual_source_reserve_nonnegative sharp m ell (causalCore advanced F g w)
  have hz : 0 ≤ sourceReserve sharp m ell (causalCore advanced F g w) :=
    (by positivity : 0 ≤ (3/2:ℝ)*sourceMu^2*‖embed (SourceNativeCutoffContact.thetaAction m ell
      (causalCore advanced F g w))‖^2).trans hn
  exact (le_add_of_nonneg_right hz).trans h

private theorem mixed_young {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μ : ℝ) (hμ : 0 < μ) (x y : V) :
    (inner ℂ x y+inner ℂ y x).re ≤ μ*‖y‖^2+μ⁻¹*‖x‖^2 := by
  have hr := re_inner_le_norm (𝕜 := ℂ) x y
  have hs := inner_re_symm (𝕜 := ℂ) x y
  change (inner ℂ x y).re = (inner ℂ y x).re at hs
  rw [Complex.add_re,←hs]
  change (inner ℂ x y).re ≤ ‖x‖*‖y‖ at hr
  have hm := mul_le_mul_of_nonneg_left hr hμ.le
  have he := inv_mul_cancel₀ hμ.ne'
  apply (mul_le_mul_iff_right₀ hμ).mp
  nlinarith only [hm,sq_nonneg (μ*‖y‖-‖x‖),he]

private theorem resolvent_embed (advanced : Bool) (F : Index) (g : QuantumTest) (w : ℝ) :
    embed (causalCore advanced F g w) = finiteResolvent F (causalFrequency advanced sourceMu w) (embed g) := by
  unfold causalCore resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- Exact half-self absorption consumes the source smoothing itself, not a supplied L price. -/
private theorem actual_mixed_self_absorption (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) :
    sourceMu*(∫ w : ℝ,‖finiteResolvent F (causalFrequency advanced sourceMu w)
      (SourceEscapeSeedTail.actualIncrement sharp m ell
        (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))‖^2)+
      Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
        (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2 ≤
      sourceMu⁻¹*(∫ w : ℝ,DFrequency advanced sharp m ell F g w) := by
  let D := SourceEscapeSeedTail.actualIncrement sharp m ell
  let E := ∫ w : ℝ,‖finiteResolvent F (causalFrequency advanced sourceMu w)
    (D (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))‖^2
  let S := ∫ w : ℝ,‖ActualTwoResolventSylvester.sourceL advanced F sourceMu D
    (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g))‖^2
  have hm := (actual_mixed_frequency_integrable advanced F sourceMu source_mu_positive D (embed g)).re
  have hl := actual_source_single_integrable advanced F sourceMu source_mu_positive D (embed g)
  have hd := D_frequency_integrable advanced sharp m ell F g
  have hp := integral_mono hm ((hl.const_mul sourceMu).add (hd.const_mul sourceMu⁻¹))
    (fun w => by
      have h := mixed_young sourceMu source_mu_positive
        (D (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))
        (ActualTwoResolventSylvester.sourceL advanced F sourceMu D
          (finiteResolvent F (causalFrequency advanced sourceMu w) (embed g)))
      change (frequencyPair advanced F sourceMu D (embed g) w).re ≤ _
      dsimp only [D] at h ⊢
      simpa only [frequencyPair,DFrequency,Pi.add_apply,
        ←resolvent_embed,←literal_increment_core] using h)
  simp only [Pi.add_apply] at hp
  rw [integral_add (hl.const_mul sourceMu) (hd.const_mul sourceMu⁻¹),integral_const_mul,integral_const_mul] at hp
  have hx := congrArg Complex.re (actual_mixed_frequency_integral advanced F sourceMu source_mu_positive D (embed g))
  have hir' := integral_re (actual_mixed_frequency_integrable advanced F sourceMu source_mu_positive D (embed g))
  simp only [RCLike.re_to_complex] at hir'
  rw [←hir'] at hx
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,sub_zero] at hx
  simp only [RCLike.re_to_complex] at hp
  rw [hx,←actual_vector_causal_energy F advanced sourceMu source_mu_positive D (embed g)] at hp
  have he := actual_two_resolvent_price advanced F sourceMu source_mu_positive D (embed g)
  change E = Real.pi/sourceMu*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu D (embed g)‖^2+S at he
  have he' := congrArg (fun x : ℝ => sourceMu*x) he
  have hs : sourceMu*(Real.pi/sourceMu*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu D (embed g)‖^2)=
      Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu D (embed g)‖^2 := by
    field_simp [source_mu_positive.ne']
  rw [mul_add,hs] at he'
  change sourceMu*E+Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu D (embed g)‖^2 ≤ _
  change 2*sourceMu*E ≤ sourceMu*S+sourceMu⁻¹*(∫ w : ℝ,DFrequency advanced sharp m ell F g w) at hp
  linarith only [hp,he']


private theorem Q_current_integrable (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Integrable (QCurrentFrequency advanced sharp m ell F g) := by
  have hi := ((paid_raw_payment% core_pair_integrable) advanced F sourceMu source_mu_positive
    ((Complex.I*(causalSign advanced : ℂ)) • (compressionCore F*((2:ℂ) • sourceQAction sharp m ell)-
      ((2:ℂ) • sourceQAction sharp m ell)*compressionCore F)) g).re
  simp only [RCLike.re_to_complex] at hi
  exact hi.congr (Filter.Eventually.of_forall (fun _ => rfl))

private theorem damping_Q_return (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) (w : ℝ) :
    (sourcePair (causalCore advanced F g w)
      (ActualExactSylvesterRawStorage.lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell)
        (causalCore advanced F g w))).re =
      4*sourceMu*QFrequency advanced sharp m ell F g w-QCurrentFrequency advanced sharp m ell F g w := by
  let q := causalCore advanced F g w
  have hq : sourcePair q ((2:ℂ) • sourceQAction sharp m ell q)=
      (2:ℂ)*sourcePair q (sourceQAction sharp m ell q) := by
    simp only [sourcePair,map_smul,inner_smul_right]
  change (sourcePair q (ActualExactSylvesterRawStorage.lyapunov advanced F
    ((2:ℂ) • sourceQAction sharp m ell) q)).re = _
  unfold ActualExactSylvesterRawStorage.lyapunov
  simp only [LinearMap.sub_apply,LinearMap.smul_apply]
  have hs (x y : QuantumTest) : sourcePair q (x-y)=sourcePair q x-sourcePair q y := by
    simp only [sourcePair,map_sub,inner_sub_right]
  have hc (c : ℂ) (x : QuantumTest) : sourcePair q (c • x)=c*sourcePair q x := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hs,hc,hq,Complex.sub_re]
  change ((2*(sourceMu:ℂ))*((2:ℂ)*sourcePair q (sourceQAction sharp m ell q))).re-
    QCurrentFrequency advanced sharp m ell F g w = _
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,mul_zero,add_zero,sub_zero]
  rw [(paid_raw_source_Q_energy%) sharp m ell q]
  change _ = 4*sourceMu*sourceQ sharp m ell q-QCurrentFrequency advanced sharp m ell F g w
  ring

/-- The whole unbounded-Q current is paid on the actual finite core orbit. -/
theorem actual_Q_current_frequency_balance (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) :
    Integrable (QFrequency advanced sharp m ell F g) ∧
    Integrable (reserveFrequency advanced sharp m ell F g) ∧
    Integrable (QCurrentFrequency advanced sharp m ell F g) ∧
    (∫ w : ℝ,QCurrentFrequency advanced sharp m ell F g w)=
      4*sourceMu*(∫ w : ℝ,QFrequency advanced sharp m ell F g w)-4*Real.pi*sourceQ sharp m ell g := by
  have hq := Q_frequency_integrable advanced sharp m ell F g
  have hr := reserve_frequency_integrable advanced sharp m ell F g
  have hc := Q_current_integrable advanced sharp m ell F g
  refine ⟨hq,hr,hc,?_⟩
  have he := (paid_raw_payment% actual_source_Q_frequency_balance) advanced sharp m ell F g
  change (∫ w : ℝ,(sourcePair (causalCore advanced F g w)
    (ActualExactSylvesterRawStorage.lyapunov advanced F ((2:ℂ) • sourceQAction sharp m ell)
      (causalCore advanced F g w))).re)=4*Real.pi*sourceQ sharp m ell g at he
  simp_rw [damping_Q_return advanced sharp m ell F g] at he
  rw [integral_sub (hq.const_mul (4*sourceMu)) hc,integral_const_mul] at he
  linarith only [he]

/-- The source reserve removes the exact-L self term and lowers the entire current price to three quarters.
No sign or tail of that remaining current is asserted. -/
theorem actual_raw_source_reserve_return (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) :
    (∫ w : ℝ,rawFrequencyResidual advanced sharp m ell F g w)+
      (3/4:ℝ)*(∫ w : ℝ,QCurrentFrequency advanced sharp m ell F g w) ≥
      Real.pi*sourceQ sharp m ell g+
      (2/sourceMu)*(∫ w : ℝ,reserveFrequency advanced sharp m ell F g w)+
      2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
        (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2 := by
  have hd := D_frequency_integrable advanced sharp m ell F g
  have hq := Q_frequency_integrable advanced sharp m ell F g
  have hr := reserve_frequency_integrable advanced sharp m ell F g
  have hp := integral_mono (hd.add hr) (hq.const_mul ((3/2:ℝ)*sourceMu^2))
    (fun w => actual_increment_source_reserve sharp m ell (causalCore advanced F g w))
  simp only [Pi.add_apply] at hp
  rw [integral_add hd hr,integral_const_mul] at hp
  have ha := actual_mixed_self_absorption advanced sharp m ell F g
  have hb := actual_raw_frequency_balance advanced sharp m ell F g
  have hc := (actual_Q_current_frequency_balance advanced sharp m ell F g).2.2.2
  have hmul := mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr source_mu_positive.le)
  have he : sourceMu⁻¹*((3/2:ℝ)*sourceMu^2)=(3/2:ℝ)*sourceMu := by
    field_simp [source_mu_positive.ne']
  rw [mul_add,←mul_assoc,he] at hmul
  have hf : (2/sourceMu)*(∫ w : ℝ,reserveFrequency advanced sharp m ell F g w)=
      2*(sourceMu⁻¹*(∫ w : ℝ,reserveFrequency advanced sharp m ell F g w)) := by ring
  rw [hf]
  linarith only [ha,hmul,hb,hc]


open SourceHardyRetardedTail SourceRelativePowerTail SourceInverseNoetherEnergy

elab "paid_raw_theta_pair%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventCascade 0) "LowEnergy") "ActualTwoResolventCascade") "theta_pair")

private def thetaEnergyFrequency (advanced : Bool) (m ell : ℕ) (F : Index)
    (g : QuantumTest) (w : ℝ) : ℝ :=
  ‖embed (SourceNativeCutoffContact.thetaAction m ell (causalCore advanced F g w))‖^2

/-- The whole CF current of the source norm slot, before either causal direction. -/
def normCurrentFrequency (advanced : Bool) (m ell : ℕ) (F : Index)
    (g : QuantumTest) (w : ℝ) : ℝ :=
  let q := causalCore advanced F g w
  let T := SourceNativeCutoffContact.thetaAction m ell
  (sourcePair q (((Complex.I*(causalSign advanced : ℂ)) •
    (compressionCore F*(T*T)-(T*T)*compressionCore F)) q)).re

/-- The remaining bulk current keeps both moving legs and the entire CF own defect. -/
def bulkCurrentFrequency (advanced : Bool) (m ell : ℕ) (F : Index)
    (g : QuantumTest) (w : ℝ) : ℝ :=
  let q := causalCore advanced F g w
  let T := SourceNativeCutoffContact.thetaAction m ell
  (sourcePair q (((Complex.I*(causalSign advanced : ℂ)) •
    (compressionCore F*(T*bulkAction*T)-(T*bulkAction*T)*compressionCore F)) q)).re

attribute [local irreducible] bulkAction SourceNativeCutoffContact.thetaAction

private theorem theta_square_energy (m ell : ℕ) (f : QuantumTest) :
    (sourcePair f ((SourceNativeCutoffContact.thetaAction m ell*
      SourceNativeCutoffContact.thetaAction m ell) f)).re=
      ‖embed (SourceNativeCutoffContact.thetaAction m ell f)‖^2 := by
  rw [Module.End.mul_apply,(paid_raw_theta_pair%) m ell f]
  unfold sourcePair
  simpa only [RCLike.re_to_complex] using
    (inner_self_eq_norm_sq (𝕜 := ℂ) (embed (SourceNativeCutoffContact.thetaAction m ell f)))

private theorem theta_frequency_integrable (advanced : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Integrable (thetaEnergyFrequency advanced m ell F g) := by
  have h := ActualVectorBulkSourcePrice.actual_theta_frequency_integrable advanced m ell F
    sourceMu source_mu_positive (coreEquiv g)
  unfold thetaEnergyFrequency causalCore resolventCore
  exact h

private theorem norm_current_integrable (advanced : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Integrable (normCurrentFrequency advanced m ell F g) := by
  let T := SourceNativeCutoffContact.thetaAction m ell
  have h := ((paid_raw_payment% core_pair_integrable) advanced F sourceMu source_mu_positive
    ((Complex.I*(causalSign advanced : ℂ)) • (compressionCore F*(T*T)-(T*T)*compressionCore F)) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _ => rfl))

private theorem bulk_current_integrable (advanced : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) : Integrable (bulkCurrentFrequency advanced m ell F g) := by
  let T := SourceNativeCutoffContact.thetaAction m ell
  have h := ((paid_raw_payment% core_pair_integrable) advanced F sourceMu source_mu_positive
    ((Complex.I*(causalSign advanced : ℂ)) • (compressionCore F*(T*bulkAction*T)-
      (T*bulkAction*T)*compressionCore F)) g).re
  simp only [RCLike.re_to_complex] at h
  exact h.congr (Filter.Eventually.of_forall (fun _ => rfl))

private theorem norm_current_balance (advanced : Bool) (m ell : ℕ) (F : Index) (g : QuantumTest) :
    (∫ w : ℝ,normCurrentFrequency advanced m ell F g w)=
      2*sourceMu*(∫ w : ℝ,thetaEnergyFrequency advanced m ell F g w)-
      2*Real.pi*‖embed (SourceNativeCutoffContact.thetaAction m ell g)‖^2 := by
  let T := SourceNativeCutoffContact.thetaAction m ell
  have h := actual_core_lyapunov_frequency_balance advanced F sourceMu source_mu_positive (T*T) g
  have hi := h.1
  have he := congrArg Complex.re h.2
  have hir := integral_re hi
  simp only [RCLike.re_to_complex] at hir
  rw [←hir] at he
  have hp (w : ℝ) :
      (sourcePair (causalCore advanced F g w)
        ((paid_raw_payment% frequencyLyapunov) advanced F sourceMu (T*T)
          (causalCore advanced F g w))).re=
      2*sourceMu*thetaEnergyFrequency advanced m ell F g w-normCurrentFrequency advanced m ell F g w := by
    let q := causalCore advanced F g w
    change (sourcePair q ((paid_raw_payment% frequencyLyapunov) advanced F sourceMu (T*T) q)).re=_
    change (sourcePair q (((2*(sourceMu : ℂ)) • (T*T)-
      (Complex.I*(causalSign advanced : ℂ)) • (compressionCore F*(T*T)-(T*T)*compressionCore F)) q)).re=_
    simp only [LinearMap.sub_apply,LinearMap.smul_apply]
    have hs (x y : QuantumTest) : sourcePair q (x-y)=sourcePair q x-sourcePair q y := by
      simp only [sourcePair,map_sub,inner_sub_right]
    have hc (c : ℂ) (x : QuantumTest) : sourcePair q (c • x)=c*sourcePair q x := by
      simp only [sourcePair,map_smul,inner_smul_right]
    rw [hs,hc,Complex.sub_re]
    change ((2*(sourceMu : ℂ))*sourcePair q ((T*T) q)).re-
      normCurrentFrequency advanced m ell F g w=_
    norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero,add_zero]
    rw [theta_square_energy]
    rfl
  change (∫ w : ℝ,(sourcePair (causalCore advanced F g w)
    ((paid_raw_payment% frequencyLyapunov) advanced F sourceMu (T*T)
      (causalCore advanced F g w))).re)=
    (2*(Real.pi : ℂ)*sourcePair g ((T*T) g)).re at he
  simp_rw [hp] at he
  rw [integral_sub ((theta_frequency_integrable advanced m ell F g).const_mul (2*sourceMu))
    (norm_current_integrable advanced m ell F g),integral_const_mul] at he
  norm_num only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero,add_zero] at he
  rw [theta_square_energy] at he
  linarith only [he]

/-- The complete norm current is genuinely paid by the original norm tails, on one event for both causes. -/
theorem actual_norm_current_causal_tail (g : QuantumTest) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m →∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced : Bool,
        |∫ w : ℝ,normCurrentFrequency advanced m ell F g w| ≤ ε := by
  intro ε hε
  have hmu := source_mu_positive
  have hpi := Real.pi_pos
  let δ := ε/(4*(sourceMu+Real.pi+1))
  have hd : 0 < δ := by dsimp only [δ];positivity
  obtain ⟨N1,h1⟩ := ActualVectorBulkSourcePrice.actual_theta_frequency_norm_tail
    sourceMu source_mu_positive (coreEquiv g) δ hd
  obtain ⟨N2,h2⟩ := original_relative_tail (embed g) (Real.sqrt δ) (Real.sqrt_pos.mpr hd)
  refine ⟨max N1 N2,fun m hm ell hml => ?_⟩
  have hs := h2 m (by omega) ell hml
  rw [←SourceNativeCutoffContact.theta_core m ell g] at hs
  have hfixed : ‖embed (SourceNativeCutoffContact.thetaAction m ell g)‖^2 ≤ δ := by
    have he := Real.sq_sqrt hd.le
    nlinarith only [hs,he,Real.sqrt_nonneg δ,norm_nonneg (embed (SourceNativeCutoffContact.thetaAction m ell g))]
  filter_upwards [h1 m (by omega) ell hml] with F hF
  intro advanced
  have hfreq : (∫ w : ℝ,thetaEnergyFrequency advanced m ell F g w) ≤ δ := by
    unfold thetaEnergyFrequency causalCore resolventCore
    exact hF advanced
  have hnonneg : 0 ≤ ∫ w : ℝ,thetaEnergyFrequency advanced m ell F g w := integral_nonneg (fun _ => sq_nonneg _)
  rw [norm_current_balance]
  have ha := norm_sub_le (2*sourceMu*(∫ w : ℝ,thetaEnergyFrequency advanced m ell F g w))
    (2*Real.pi*‖embed (SourceNativeCutoffContact.thetaAction m ell g)‖^2)
  simp only [Real.norm_eq_abs] at ha
  have hA : 0 ≤ 2*sourceMu*(∫ w : ℝ,thetaEnergyFrequency advanced m ell F g w) := by positivity
  have hB : 0 ≤ 2*Real.pi*‖embed (SourceNativeCutoffContact.thetaAction m ell g)‖^2 := by positivity
  rw [abs_of_nonneg hA,abs_of_nonneg hB] at ha
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hfreq (by positivity : 0 ≤ 2*sourceMu))
    (mul_le_mul_of_nonneg_left hfixed (by positivity : 0 ≤ 2*Real.pi))
  apply (ha.trans hbound).trans
  dsimp only [δ]
  rw [←add_mul,←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 4*(sourceMu+Real.pi+1))).mpr
  nlinarith only [hε,source_mu_positive,Real.pi_pos]

private theorem current_frequency_split (advanced sharp : Bool) (m ell : ℕ)
    (F : Index) (g : QuantumTest) (w : ℝ) :
    QCurrentFrequency advanced sharp m ell F g w=
      2*bulkCoefficient sharp*bulkCurrentFrequency advanced m ell F g w+
      2*normCoefficient sharp*normCurrentFrequency advanced m ell F g w := by
  unfold QCurrentFrequency bulkCurrentFrequency normCurrentFrequency sourceQAction
  dsimp only
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,map_smul,inner_add_right,inner_sub_right,inner_smul_right]
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,mul_zero,add_zero,sub_zero]
  ring

private theorem norm_coefficient_nonnegative (sharp : Bool) : 0 ≤ normCoefficient sharp := by
  unfold normCoefficient
  have hc := coefficient_nonnegative sharp
  positivity

/-- One common source event removes the entire norm current. The only surviving
current is the actual bulk CF word, with all native, gauge and norm reserves retained. -/
theorem actual_raw_bulk_current_paid_return (g : QuantumTest) :
    ∀ ε : ℝ,0 < ε →∃ N : ℕ,∀ m,N ≤ m →∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ advanced sharp : Bool,
      (∫ w : ℝ,rawFrequencyResidual advanced sharp m ell F g w)+
        (3/2:ℝ)*bulkCoefficient sharp*(∫ w : ℝ,bulkCurrentFrequency advanced m ell F g w) ≥
      Real.pi*sourceQ sharp m ell g+(2/sourceMu)*(∫ w : ℝ,reserveFrequency advanced sharp m ell F g w)+
        2*Real.pi*‖ActualTwoResolventSylvester.sourceL advanced F sourceMu
          (SourceEscapeSeedTail.actualIncrement sharp m ell) (embed g)‖^2-ε := by
  intro ε hε
  let B := normCoefficient false+normCoefficient true
  have hB : 0 ≤ B := add_nonneg (norm_coefficient_nonnegative false) (norm_coefficient_nonnegative true)
  obtain ⟨N,hN⟩ := actual_norm_current_causal_tail g (ε/((3/2:ℝ)*B+1)) (by positivity)
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced sharp
  have hs := actual_raw_source_reserve_return advanced sharp m ell F g
  have hc : (∫ w : ℝ,QCurrentFrequency advanced sharp m ell F g w)=
      2*bulkCoefficient sharp*(∫ w : ℝ,bulkCurrentFrequency advanced m ell F g w)+
      2*normCoefficient sharp*(∫ w : ℝ,normCurrentFrequency advanced m ell F g w) := by
    simp_rw [current_frequency_split advanced sharp m ell F g]
    rw [integral_add ((bulk_current_integrable advanced m ell F g).const_mul _)
      ((norm_current_integrable advanced m ell F g).const_mul _),integral_const_mul,integral_const_mul]
  rw [hc] at hs
  have hb : normCoefficient sharp ≤ B := by
    cases sharp
    · exact le_add_of_nonneg_right (norm_coefficient_nonnegative true)
    · exact le_add_of_nonneg_left (norm_coefficient_nonnegative false)
  have hprice := mul_le_mul_of_nonneg_left (hF advanced)
    (show 0 ≤ (3/2:ℝ)*normCoefficient sharp by have h := norm_coefficient_nonnegative sharp;positivity)
  have he : (3/2:ℝ)*normCoefficient sharp*(ε/((3/2:ℝ)*B+1)) ≤ ε := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < (3/2:ℝ)*B+1)).mpr
    nlinarith only [hb,hε]
  have ha := le_abs_self (∫ w : ℝ,normCurrentFrequency advanced m ell F g w)
  have hpa := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ (3/2:ℝ)*normCoefficient sharp by have h := norm_coefficient_nonnegative sharp;positivity)
  linarith only [hs,hprice,he,hpa]

end LowEnergy.ActualRawResidualTailPayment
