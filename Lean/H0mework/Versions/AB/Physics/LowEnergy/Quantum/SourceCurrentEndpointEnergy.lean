import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceNativeMixedCurrent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceNativeCutoffContact
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFixedJetBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace LowEnergy.SourceCurrentEndpointEnergy
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussNativeForm GaussNativeEnergy GaussCoframeForm GaussDiagonalHistory GaussLiveMomentum
open GaussRadialDomain SourceMixedNativeReturn SourceClosedCostNativeProbe
open SourceJointScaleBudget SourceFixedJetBudget SourceCoframeVolumeCurrent
open FullYSourceResolventGraphSplice SourceResolventBandLimit GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart
open GaussHistoryHilbert SourceEscapeCurrent
open scoped BigOperators ContDiff InnerProductSpace

def weightAction : CoreEnd :=
  multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth

def primitiveAdjoint (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  ∑ a : GaussNativeForm.ScalarIndex,
    SourceMixedNativeReturn.thetaAction m ell*GaussMomentumAdjoint.adjoint (scalarDirection a)*
      weightAction*constantAction (!sharp) (scalarBasis a)

theorem primitive_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (primitive sharp m ell g)=sourcePair (primitiveAdjoint sharp m ell f) g := by
  simp only [primitive,primitiveAdjoint,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair f (constantAction sharp (scalarBasis a)
    (weightAction (covariantMomentum (scalarDirection a) (SourceMixedNativeReturn.thetaAction m ell g))))=
    sourcePair (SourceMixedNativeReturn.thetaAction m ell
      (GaussMomentumAdjoint.adjoint (scalarDirection a)
        (weightAction (constantAction (!sharp) (scalarBasis a) f)))) g
  rw [constant_pair]
  unfold weightAction
  rw [multiply_pair,GaussMomentumAdjoint.momentum_pair]
  have ht := multiply_pair (SourceNativeCutoffContact.theta m ell)
    (fun _ => (SourceNativeCutoffContact.theta_smooth m ell).contDiffAt)
    (GaussMomentumAdjoint.adjoint (scalarDirection a)
      (weightAction (constantAction (!sharp) (scalarBasis a) f))) g
  change sourcePair (GaussMomentumAdjoint.adjoint (scalarDirection a)
    (weightAction (constantAction (!sharp) (scalarBasis a) f)))
      (SourceNativeCutoffContact.thetaAction m ell g)=
    sourcePair (SourceNativeCutoffContact.thetaAction m ell
      (GaussMomentumAdjoint.adjoint (scalarDirection a)
        (weightAction (constantAction (!sharp) (scalarBasis a) f)))) g at ht
  rw [SourceNativeCutoffContact.theta_action_polynomial] at ht
  simpa only [SourceMixedNativeReturn.thetaAction,weightAction] using! ht

private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

theorem source_read_input (F : Index) (g : diagonal.domain) (A : CoreEnd) :
    sourceRead F g A (g : H)=embed (A (coreEquiv.symm g)) := by
  have hg : (g : H)∈inputSpan F g :=
    (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
  have hp := (inputSpan F g).orthogonalProjectionOnto_mem_subspace_eq_self ⟨(g : H),hg⟩
  change embed (A (coreEquiv.symm
    (Submodule.inclusion (input_span_core F g)
      ((inputSpan F g).orthogonalProjectionOnto (g : H)))))=_
  rw [hp]
  rfl

def currentResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  inner ℂ (k : H) (finiteResolvent F z
    ((GaussGradedCompression.compression F*sourceRead F g (primitive sharp m ell)-
      sourceRead F g (primitive sharp m ell)*GaussGradedCompression.compression F)
        (finiteResolvent F z (g : H))))

private theorem ring_endpoint {A : Type*} [Ring A] (c r t b : A) (hb : Commute b t)
    (hl : r*(c-b)=1) (hr : (c-b)*r=1) : r*(c*t-t*c)*r=t*r-r*t := by
  have hs : c*t-t*c=(c-b)*t-t*(c-b) := by
    rw [sub_mul,mul_sub,hb.eq]
    abel
  calc
    _ = (r*(c-b))*t*r-r*t*((c-b)*r) := by rw [hs]; noncomm_ring
    _ = _ := by rw [hl,hr,one_mul,mul_one]

/-- Both endpoints are the actual original source tests; the finite input span keeps escape. -/
theorem actual_current_endpoints (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    currentResponse sharp m ell F g k z=
      inner ℂ (embed (primitiveAdjoint sharp m ell (coreEquiv.symm k)))
        (finiteResolvent F z (g : H))-
      inner ℂ (k : H) (finiteResolvent F z (embed (primitive sharp m ell (coreEquiv.symm g)))) := by
  let C := GaussGradedCompression.compression F
  let R := finiteResolvent F z
  let T := sourceRead F g (primitive sharp m ell)
  have hl : R*(C-z • 1)=1 := resolvent_left C (GaussGradedCompression.compression_selfAdjoint F) z hz
  have hr : (C-z • 1)*R=1 := resolvent_right C (GaussGradedCompression.compression_selfAdjoint F) z hz
  have hb : Commute (z • (1 : H →L[ℂ] H)) T := (Commute.one_left T).smul_left z
  have he := ring_endpoint C R T (z • 1) hb hl hr
  have hh := congrArg (fun A : H →L[ℂ] H => inner ℂ (k : H) (A (g : H))) he
  change currentResponse sharp m ell F g k z=
    inner ℂ (k : H) (T (R (g : H))-R (T (g : H))) at hh
  rw [inner_sub_right,source_read_resolvent F g _ z hz,source_read_input] at hh
  rw [hh]
  have hp := primitive_pair sharp m ell (coreEquiv.symm k) (coreEquiv.symm (sourceCore F z hz g))
  simp only [sourcePair,core_embed] at hp
  change inner ℂ (k : H) (embed (primitive sharp m ell (coreEquiv.symm (sourceCore F z hz g))))=
    inner ℂ (embed (primitiveAdjoint sharp m ell (coreEquiv.symm k)))
      (finiteResolvent F z (g : H)) at hp
  rw [hp]

private theorem two_square (a b : ℂ) : ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_sub_le a b
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a-b),norm_nonneg a,norm_nonneg b]

theorem actual_current_energy (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    (∫⁻ w : ℝ, ENNReal.ofReal (‖currentResponse sharp m ell F g k (line μ w)‖^2)) ≤
      ENNReal.ofReal ((2*Real.pi/μ)*(
        ‖embed (primitiveAdjoint sharp m ell (coreEquiv.symm k))‖^2*‖(g : H)‖^2+
        ‖(k : H)‖^2*‖embed (primitive sharp m ell (coreEquiv.symm g))‖^2)) := by
  let k₁ := primitiveAdjoint sharp m ell (coreEquiv.symm k)
  let g₁ := primitive sharp m ell (coreEquiv.symm g)
  have he (w : ℝ) := actual_current_endpoints sharp m ell F g k (line μ w)
    (by simpa only [line_im] using hμ.ne')
  have hl := actual_profile_jet_lintegral 0 0 0 F μ hμ k₁ (coreEquiv.symm g) 0
  have hr := actual_profile_jet_lintegral 0 0 0 F μ hμ (coreEquiv.symm k) g₁ 0
  have hc := profile_jet_frequency_continuous 0 0 0 F μ hμ k₁ (coreEquiv.symm g) 0
  have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal
      (‖inner ℂ (embed k₁) (finiteResolvent F (line μ w) (g : H))‖^2)) := by
    simpa only [profileJet,profile,SourceCoframeStrongJet.strongJet,pow_zero,one_smul,
      Module.End.one_apply,SourceCoframeScaleTransport.coreFlow_zero,core_embed] using!
      (hc.norm.pow 2).measurable.ennreal_ofReal
  simp only [profileJet,profile,SourceCoframeStrongJet.strongJet,pow_zero,one_smul,
    Module.End.one_apply,SourceCoframeScaleTransport.coreFlow_zero,profileJetBudget,core_embed] at hl hr
  calc
    _  ≤  ∫⁻ w : ℝ, ENNReal.ofReal 2*(
        ENNReal.ofReal (‖inner ℂ (embed k₁) (finiteResolvent F (line μ w) (g : H))‖^2)+
        ENNReal.ofReal (‖inner ℂ (k : H) (finiteResolvent F (line μ w) (embed g₁))‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [he,←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (two_square _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal
        (‖inner ℂ (embed k₁) (finiteResolvent F (line μ w) (g : H))‖^2))+
        ∫⁻ w : ℝ, ENNReal.ofReal
        (‖inner ℂ (k : H) (finiteResolvent F (line μ w) (embed g₁))‖^2)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_left hmeas]
    _  ≤  ENNReal.ofReal 2*(ENNReal.ofReal ((Real.pi/μ)*(‖embed k₁‖^2*‖(g : H)‖^2))+
        ENNReal.ofReal ((Real.pi/μ)*(‖(k : H)‖^2*‖embed g₁‖^2))) :=
      mul_le_mul_of_nonneg_left (add_le_add hl hr) (by positivity)
    _ = _ := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

def basePrimitive (sharp : Bool) : CoreEnd :=
  ∑ a : ScalarIndex, constantAction sharp (scalarBasis a)*weightedMomentum (scalarDirection a)

def baseAdjoint (sharp : Bool) : CoreEnd :=
  ∑ a : ScalarIndex, GaussMomentumAdjoint.adjoint (scalarDirection a)*
    weightAction*constantAction (!sharp) (scalarBasis a)

def primitiveContact (sharp : Bool) (m ell : ℕ) : CoreEnd :=
  ∑ a : ScalarIndex, constantAction sharp (scalarBasis a)*weightAction*
    SourceNativeCutoffContact.contactAction (scalarDirection a) m ell

private theorem theta_constant (sharp : Bool) (v : SourceQuantumScalarChart.Scalar)
    (m ell : ℕ) (f : QuantumTest) :
    constantAction sharp v (SourceMixedNativeReturn.thetaAction m ell f)=
      SourceMixedNativeReturn.thetaAction m ell (constantAction sharp v f) := by
  change constantAction sharp v
    (((1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)) f)=
    ((1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)) (constantAction sharp v f)
  rw [←SourceNativeCutoffContact.theta_action_polynomial]
  apply DFunLike.ext
  intro z
  exact map_smul (branchMap sharp v) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)

private theorem scalar_commute (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val)
    (b : SourceCoordinateSlice → ℝ)
    (hb : ∀ z : physicalChart, ContDiffAt ℝ ∞ b z.val) (f : QuantumTest) :
    multiply a ha (multiply b hb f)=multiply b hb (multiply a ha f) := by
  apply DFunLike.ext
  intro z
  change (a z : ℂ) • ((b z : ℂ) • f z)=(b z : ℂ) • ((a z : ℂ) • f z)
  exact smul_comm (a z : ℂ) (b z : ℂ) (f z)

private theorem theta_weight (m ell : ℕ) (f : QuantumTest) :
    weightAction (SourceMixedNativeReturn.thetaAction m ell f)=
      SourceMixedNativeReturn.thetaAction m ell (weightAction f) := by
  change weightAction (((1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)) f)=
    ((1-inverseAction)^(m+1)-(1-inverseAction)^(ell+1)) (weightAction f)
  rw [←SourceNativeCutoffContact.theta_action_polynomial]
  change multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth
    (multiply (SourceNativeCutoffContact.theta m ell)
      (fun _ => (SourceNativeCutoffContact.theta_smooth m ell).contDiffAt) f)=_
  exact scalar_commute _ GaussCoframeForm.inverseVolume_smooth _
    (fun _ => (SourceNativeCutoffContact.theta_smooth m ell).contDiffAt) f

theorem primitive_adjoint_tail (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    primitiveAdjoint sharp m ell f=SourceFixedJetBudget.tailAction m ell (baseAdjoint sharp f) := by
  change (∑ a : ScalarIndex, (SourceMixedNativeReturn.thetaAction m ell*
    GaussMomentumAdjoint.adjoint (scalarDirection a)*weightAction*
      constantAction (!sharp) (scalarBasis a))) f=SourceMixedNativeReturn.thetaAction m ell (baseAdjoint sharp f)
  simp only [LinearMap.sum_apply,baseAdjoint,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

/-- The only native derivative of the cutoff is retained as its generated contact. -/
theorem primitive_source_split (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    primitive sharp m ell f=SourceFixedJetBudget.tailAction m ell (basePrimitive sharp f)+
      primitiveContact sharp m ell f := by
  change primitive sharp m ell f=SourceMixedNativeReturn.thetaAction m ell (basePrimitive sharp f)+
    primitiveContact sharp m ell f
  simp only [primitive,basePrimitive,primitiveContact,LinearMap.sum_apply,map_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  change constantAction sharp (scalarBasis a) (weightAction
    (covariantMomentum (scalarDirection a) (SourceMixedNativeReturn.thetaAction m ell f)))=_
  have hn := SourceNativeCutoffContact.native_core_contact (scalarDirection a) m ell f
  rw [SourceNativeCutoffContact.theta_action_polynomial] at hn
  change covariantMomentum (scalarDirection a) (SourceMixedNativeReturn.thetaAction m ell f)=
    SourceMixedNativeReturn.thetaAction m ell (covariantMomentum (scalarDirection a) f)+
      SourceNativeCutoffContact.contactAction (scalarDirection a) m ell f at hn
  rw [hn,map_add,map_add,theta_weight,theta_constant]
  rfl

def contactSourceCost (sharp : Bool) (f : QuantumTest) : ℝ :=
  ∑ a : ScalarIndex, ‖constantBounded sharp (scalarBasis a)‖*
    (2*‖(scalarDirection a).1‖)*‖embed (weightAction f)‖

theorem contact_source_cost_nonneg (sharp : Bool) (f : QuantumTest) :
    0 ≤ contactSourceCost sharp f := Finset.sum_nonneg (fun _ _ => by positivity)

private theorem weight_contact (v : Ambient) (m ell : ℕ) (f : QuantumTest) :
    weightAction (SourceNativeCutoffContact.contactAction v m ell f)=
      SourceNativeCutoffContact.contactAction v m ell (weightAction f) := by
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.inverseVolume z : ℂ) •
    (((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative v m ell z : ℂ)) • f z)=_
  exact smul_comm _ _ _

/-- The inverse volume acts only on the fixed original test, before the bounded contact estimate. -/
theorem primitive_contact_bound (sharp : Bool) (m ell : ℕ) (hle : m ≤ ell) (f : QuantumTest) :
    ‖embed (primitiveContact sharp m ell f)‖ ≤ contactSourceCost sharp f/(m+2 : ℝ) := by
  have hp : 0<(m+2 : ℝ) := by positivity
  have ht (a : ScalarIndex) :
      ‖embed (constantAction sharp (scalarBasis a) (weightAction
        (SourceNativeCutoffContact.contactAction (scalarDirection a) m ell f)))‖ ≤
      (‖constantBounded sharp (scalarBasis a)‖*(2*‖(scalarDirection a).1‖)*
        ‖embed (weightAction f)‖)/(m+2 : ℝ) := by
    rw [weight_contact,←constant_bounded_core,←SourceNativeCutoffContact.bounded_contact_core _ _ _ hle]
    have h := ((constantBounded sharp (scalarBasis a)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left
        (SourceNativeCutoffContact.bounded_contact_bound (scalarDirection a) m ell hle (embed (weightAction f)))
        (norm_nonneg _))
    exact h.trans_eq (by ring)
  simp only [primitiveContact,LinearMap.sum_apply,map_sum]
  calc
    _  ≤  ∑ a : ScalarIndex, ‖embed (constantAction sharp (scalarBasis a) (weightAction
        (SourceNativeCutoffContact.contactAction (scalarDirection a) m ell f)))‖ := norm_sum_le _ _
    _  ≤  ∑ a : ScalarIndex, (‖constantBounded sharp (scalarBasis a)‖*(2*‖(scalarDirection a).1‖)*
        ‖embed (weightAction f)‖)/(m+2 : ℝ) := Finset.sum_le_sum (fun a _ => ht a)
    _ = _ := (Finset.sum_div _ _ _).symm

private theorem reciprocal_budget_tail (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → C/(m+2 : ℝ) ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm => ?_⟩
  apply (div_le_iff₀ (by positivity : 0<(m+2 : ℝ))).mpr
  have hnm : (N : ℝ) ≤ m := by exact_mod_cast hm
  have h := (div_lt_iff₀ hε).mp hN
  nlinarith

theorem actual_primitive_tail (sharp : Bool) (f : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖embed (primitive sharp m ell f)‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := SourceHardyRetardedTail.original_relative_tail (embed (basePrimitive sharp f))
    (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := reciprocal_budget_tail (contactSourceCost sharp f)
    (contact_source_cost_nonneg sharp f) (ε/2) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  rw [primitive_source_split,map_add]
  apply (norm_add_le _ _).trans
  rw [tail_core]
  exact (add_le_add (h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell).le
    ((primitive_contact_bound sharp m ell hell f).trans
      (h₂ m (le_trans (Nat.le_max_right _ _) hm)))).trans_eq (by ring)

theorem actual_primitive_adjoint_tail (sharp : Bool) (f : QuantumTest) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖embed (primitiveAdjoint sharp m ell f)‖ ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := SourceHardyRetardedTail.original_relative_tail (embed (baseAdjoint sharp f)) ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  rw [primitive_adjoint_tail,tail_core]
  exact (hN m hm ell hell).le

/-- Actual energy-gap currents have a common all-frequency tail, uniform in F and upper cutoff. -/
theorem actual_current_tail (sharp : Bool) (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖currentResponse sharp m ell F g k (line μ w)‖^2)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let B := 2*Real.pi/μ
  let C := B*(1+‖(g : H)‖^2+‖(k : H)‖^2)
  have hB : 0<B := by dsimp [B]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  let δ := Real.sqrt (ε/C)
  have hδ : 0<δ := Real.sqrt_pos.mpr (div_pos hε hC)
  have hδ2 : δ^2=ε/C := Real.sq_sqrt (div_pos hε hC).le
  obtain ⟨N₁,h₁⟩ := actual_primitive_adjoint_tail sharp (coreEquiv.symm k) δ hδ
  obtain ⟨N₂,h₂⟩ := actual_primitive_tail sharp (coreEquiv.symm g) δ hδ
  refine ⟨max N₁ N₂,fun m hm ell hell F => ?_⟩
  apply (actual_current_energy sharp m ell F g k μ hμ).trans
  apply ENNReal.ofReal_le_ofReal
  have hl := pow_le_pow_left₀ (norm_nonneg _)
    (h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell) 2
  have hr := pow_le_pow_left₀ (norm_nonneg _)
    (h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell) 2
  calc
    _  ≤  B*(δ^2*‖(g : H)‖^2+‖(k : H)‖^2*δ^2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hl (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hr (sq_nonneg _))) hB.le
    _  ≤  C*δ^2 := by dsimp [C]; nlinarith [mul_nonneg hB.le (sq_nonneg δ)]
    _ = ε := by rw [hδ2,mul_div_cancel₀ ε hC.ne']

end LowEnergy.SourceCurrentEndpointEnergy
