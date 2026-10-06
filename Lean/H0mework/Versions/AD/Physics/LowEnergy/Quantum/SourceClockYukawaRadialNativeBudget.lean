import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedCore
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaRadialCoefficient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialNativeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialCoefficient SourceLocalizedInverseFormPayment
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail SourceClockYukawaTail
open SourceClockYukawaNormalizedCurrent SourceCutoffDilationWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] state fullAction inverseRadius normalizedAction finiteResolvent
  GaussGradedCompression.compression actualIncrement correctedCutoffCore

def inverseDerivativeCore (a : ScalarIndex) : End := directionAction a*inverseAction^2
def inverseDerivative (a : ScalarIndex) : Op := directionOperator a*inverseRadius^2

attribute [local irreducible] inverseDerivative

private theorem derivative_core (a : ScalarIndex) (f : QuantumTest) :
    inverseDerivative a (embed f)=embed (inverseDerivativeCore a f) := by
  simp only [inverseDerivative,inverseDerivativeCore,pow_two,mul_apply_eq_comp,Module.End.mul_apply,
    inverse_core,original_direction_core]

private theorem actual_inverse_derivative (a : ScalarIndex) :
    GaussRadialMomentum.commutatorAction (scalarDirection a)=(-Complex.I) • inverseDerivativeCore a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I*(GaussRadialMomentum.radialDerivative (scalarDirection a) z:ℂ)) • f z=
    (-Complex.I) • (directionAction a ((inverseAction^2) f)) z
  rw [pow_two]
  change _=(-Complex.I) • ((directionWeight a z:ℂ) • ((reciprocal z:ℂ) • ((reciprocal z:ℂ) • f z)))
  simp only [smul_smul]
  congr 1
  unfold GaussRadialMomentum.radialDerivative directionWeight reciprocal
  push_cast
  field_simp [(show (radius z:ℂ)≠0 by exact_mod_cast (radius_pos z).ne')]
  rfl

private theorem inverse_increment (sharp : Bool) (m ell : ℕ) :
    inverseRadius*actualIncrement sharp m ell=sourceB sharp*relativeTail m ell := by
  apply GaussYukawaGrade.core_ext
  intro f
  change inverseRadius (actualIncrement sharp m ell (embed f))=
    sourceB sharp (relativeTail m ell (embed f))
  rw [literal_increment_core,literal_full_return,Module.End.mul_apply,inverse_core,
    SourceMixedNativeReturn.theta_core]
  simpa only [normalizedAction,Module.End.mul_apply] using
    (original_normalized_core sharp (thetaAction m ell f)).symm

private theorem derivative_increment (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    inverseDerivative a*actualIncrement sharp m ell=
      (directionOperator a*inverseRadius*sourceB sharp)*relativeTail m ell := by
  unfold inverseDerivative
  rw [pow_two,mul_assoc,mul_assoc,inverse_increment sharp m ell]
  simp only [mul_assoc]

def cutoffResponseCore (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  state F z hz (coreEquiv (correctedCutoffCore sharp m ell F (state F z hz g)))

def rightNativeCoefficient (sharp : Bool) (a : ScalarIndex) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  PositiveScalarWeakBudget.coefficient sharp a m ell (radialCore F z hz g)+
    inverseDerivativeCore a (cutoffResponseCore sharp m ell F z hz g)

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem response_commutator (C S : Op) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) :
    FullYSourceResolventGraphSplice.resolvent C z*(C*S-S*C)*FullYSourceResolventGraphSplice.resolvent C z=
      S*FullYSourceResolventGraphSplice.resolvent C z-FullYSourceResolventGraphSplice.resolvent C z*S := by
  have hl := resolvent_compression C hC z hz
  have hr : C*FullYSourceResolventGraphSplice.resolvent C z=1+z • FullYSourceResolventGraphSplice.resolvent C z := by
    have h := resolvent_right C hC z hz
    simp only [sub_mul,smul_mul_assoc,one_mul] at h
    exact sub_eq_iff_eq_add.mp h
  calc
    _=(FullYSourceResolventGraphSplice.resolvent C z*C)*S*FullYSourceResolventGraphSplice.resolvent C z-
        FullYSourceResolventGraphSplice.resolvent C z*S*(C*FullYSourceResolventGraphSplice.resolvent C z) := by noncomm_ring
    _=_ := by
      rw [hl,hr]
      simp only [add_mul,mul_add,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,mul_assoc]
      abel

private theorem cutoff_response_difference (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (cutoffResponseCore sharp m ell F z hz g)=
      actualIncrement sharp m ell (finiteResolvent F z (g:H))-
        finiteResolvent F z (actualIncrement sharp m ell (g:H)) := by
  rw [cutoffResponseCore,state_embed]
  change finiteResolvent F z (embed (correctedCutoffCore sharp m ell F (state F z hz g)))=_
  rw [←actual_cutoff_current_source,state_embed]
  have h := congrArg (fun A : Op => A (g:H)) (response_commutator
    (GaussGradedCompression.compression F) (actualIncrement sharp m ell)
    (GaussGradedCompression.compression_selfAdjoint F) z hz)
  simpa only [SourceClockYukawaRadialMixedGamma.cutoffCurrent,finiteResolvent,mul_apply_eq_comp,sub_apply] using h

private theorem increment_fixed (sharp : Bool) (m ell : ℕ) (h : diagonal.domain) :
    actualIncrement sharp m ell (h:H)=relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp h:H) := by
  have hy : Commute (fullAction sharp) inverseAction := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes
    · exact GaussRadialHamiltonian.adjoint_commutes
  have ht : Commute (fullAction sharp) (thetaAction m ell) := by
    unfold thetaAction
    exact (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _).sub_right
      (((Commute.one_right (fullAction sharp)).sub_right hy).pow_right _)
  have he : embed (coreEquiv.symm h)=(h:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply h)
  have hc := LinearMap.congr_fun ht.eq (coreEquiv.symm h)
  change fullAction sharp (thetaAction m ell (coreEquiv.symm h))=
    thetaAction m ell (fullAction sharp (coreEquiv.symm h)) at hc
  rw [←he,literal_increment_core,literal_full_return,Module.End.mul_apply,hc,←SourceMixedNativeReturn.theta_core]
  rfl

private def normalizedColumn (sharp : Bool) (a : ScalarIndex) : Op :=
  directionOperator a*inverseRadius*sourceB sharp

attribute [local irreducible] normalizedColumn

private theorem derivative_response_return (sharp : Bool) (a : ScalarIndex) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F z hz g))=
      normalizedColumn sharp a (relativeTail m ell (finiteResolvent F z (g:H)))-
        inverseDerivative a (finiteResolvent F z
          (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))) := by
  rw [←derivative_core,cutoff_response_difference,map_sub,increment_fixed]
  have h := congrArg (fun A : Op => A (finiteResolvent F z (g:H))) (derivative_increment sharp a m ell)
  simpa only [normalizedColumn,mul_apply_eq_comp] using
    congrArg (fun x : H => x-inverseDerivative a (finiteResolvent F z
      (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H)))) h

private def columnPrice (sharp : Bool) : ℝ := 2*(∑ a : ScalarIndex,‖normalizedColumn sharp a‖^2)
private def derivativePrice : ℝ := 2*(∑ a : ScalarIndex,‖inverseDerivative a‖^2)

attribute [local irreducible] columnPrice derivativePrice

private theorem two_square (x y : H) : ‖x-y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private theorem derivative_response_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ a : ScalarIndex,‖embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F z hz g))‖^2) ≤
      columnPrice sharp*‖relativeTail m ell (finiteResolvent F z (g:H))‖^2+
      derivativePrice*‖finiteResolvent F z
        (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))‖^2 := by
  let x := relativeTail m ell (finiteResolvent F z (g:H))
  let y := finiteResolvent F z (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))
  calc
    _ ≤ ∑ a : ScalarIndex,(2*‖normalizedColumn sharp a‖^2*‖x‖^2+2*‖inverseDerivative a‖^2*‖y‖^2) := by
      apply Finset.sum_le_sum
      intro a _
      rw [derivative_response_return sharp a m ell F z hz g]
      have hx := pow_le_pow_left₀ (norm_nonneg _) ((normalizedColumn sharp a).le_opNorm x) 2
      have hy := pow_le_pow_left₀ (norm_nonneg _) ((inverseDerivative a).le_opNorm y) 2
      rw [mul_pow] at hx hy
      have hs := two_square (normalizedColumn sharp a x) (inverseDerivative a y)
      nlinarith only [hx,hy,hs]
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,columnPrice,derivativePrice]
      ring

private theorem derivative_energy_measurable (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (∑ a : ScalarIndex,
      ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
  simp_rw [derivative_response_return]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc : Continuous (fun w : ℝ => ∑ a : ScalarIndex,
      ‖normalizedColumn sharp a (relativeTail m ell (finiteResolvent F (line μ w) (g:H)))-
        inverseDerivative a (finiteResolvent F (line μ w)
          (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H)))‖^2) := by
    apply continuous_finsetSum
    intro a _
    exact ((((normalizedColumn sharp a).continuous.comp ((relativeTail m ell).continuous.comp
      (hr.clm_apply continuous_const))).sub ((inverseDerivative a).continuous.comp
        (hr.clm_apply continuous_const))).norm.pow 2)
  exact hc.measurable.ennreal_ofReal

private theorem derivative_response_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := columnPrice sharp+derivativePrice
  have hP : 0≤columnPrice sharp := by
    unfold columnPrice
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hQ : 0≤derivativePrice := by
    unfold derivativePrice
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hC : 0≤C := add_nonneg hP hQ
  let δ := ε/(C+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₁,h₁⟩ := actual_theta_full_frequency_tail μ hμ g δ hδ
  obtain ⟨N₂,h₂⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:Op)
    (SourceClockYukawaCurrent.yukawaSource sharp g:H) δ hδ
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml] with F hx
  have hy := h₂ m ((le_max_right _ _).trans hm) ell hml F
  simp only [one_apply_eq_self] at hy
  let X (w : ℝ) := ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w)
    (relativeTail m ell (SourceClockYukawaCurrent.yukawaSource sharp g:H))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hymeas : Measurable (fun w => ENNReal.ofReal derivativePrice*Y w) :=
    ((((hr.clm_apply continuous_const).norm.pow 2).measurable).ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (columnPrice sharp)*X w+ENNReal.ofReal derivativePrice*Y w := by
      apply lintegral_mono
      intro w
      dsimp only [X,Y]
      apply (ENNReal.ofReal_le_ofReal (derivative_response_bound sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)).trans
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ]
      exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (columnPrice sharp)*(∫⁻ w : ℝ,X w)+ENNReal.ofReal derivativePrice*(∫⁻ w : ℝ,Y w) := by
      rw [lintegral_add_right _ hymeas,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (columnPrice sharp)*ENNReal.ofReal δ+ENNReal.ofReal derivativePrice*ENNReal.ofReal δ := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have he : columnPrice sharp*δ+derivativePrice*δ=C*(ε/(C+1)) := by dsimp [C,δ];ring
      rw [he,←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<C+1)).mpr
      nlinarith

/-- Both complete source currents now feed one native divergence coefficient.
The dynamic rS and cutoff-dependent rA are paid on the original common full-frequency tail. -/
theorem actual_right_native_coefficient_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖embed (rightNativeCoefficient sharp a m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := SourceClockYukawaRadialCoefficient.actual_radial_joined_coefficient_tail
    sharp false μ hμ g (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := derivative_response_common_tail sharp μ hμ g (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml,
    h₂ m ((le_max_right _ _).trans hm) ell hml] with F hz hd
  simp only [actualFrequency,Bool.false_eq_true,if_false] at hz
  let Z (w : ℝ) := ENNReal.ofReal (∑ a : ScalarIndex,
    ‖embed (PositiveScalarWeakBudget.coefficient sharp a m ell
      (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)
  let D (w : ℝ) := ENNReal.ofReal (∑ a : ScalarIndex,
    ‖embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g))‖^2)
  have hm' : Measurable (fun w : ℝ => ENNReal.ofReal (2:ℝ)*D w) :=
    (derivative_energy_measurable sharp m ell F μ hμ g).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2:ℝ)*Z w+ENNReal.ofReal (2:ℝ)*D w := by
      apply lintegral_mono
      intro w
      dsimp only [Z,D]
      have hb : (∑ a : ScalarIndex,‖embed (rightNativeCoefficient sharp a m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g)‖^2) ≤
          2*(∑ a : ScalarIndex,‖embed (PositiveScalarWeakBudget.coefficient sharp a m ell
            (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)+
          2*(∑ a : ScalarIndex,‖embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g))‖^2) := by
        rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro a _
        rw [rightNativeCoefficient,map_add]
        have h := two_square
          (embed (PositiveScalarWeakBudget.coefficient sharp a m ell
            (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g)))
          (-embed (inverseDerivativeCore a (cutoffResponseCore sharp m ell F (line μ w)
            (by simpa only [line_im] using hμ.ne') g)))
        simpa only [sub_neg_eq_add,norm_neg] using h
      apply (ENNReal.ofReal_le_ofReal hb).trans
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,Z w)+ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,D w) := by
      rw [lintegral_add_right _ hm',lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4)+ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end LowEnergy.SourceClockYukawaRadialNativeBudget
