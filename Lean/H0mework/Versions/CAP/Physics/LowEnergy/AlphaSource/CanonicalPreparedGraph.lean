import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeContactRead
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.EmIdentification.PreparedCharge
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeBilocalRead
import Mathlib.Analysis.Normed.Operator.Extend

/-! A single actual scalar-Gram moment generates simultaneous core
approximations for the original Canonical seed and all its composite legs.
The configuration preparation is an input, not selected by this construction. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.SourceGraph
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff Distributions InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder

def gramWeight (z : SourceCoordinateSlice) : ℝ :=
  1 + ∑ a : Fin 2, ∑ c : Fin 3, ‖coefficient a c z‖^2

theorem gramWeight_one_le (z : SourceCoordinateSlice) : 1 ≤ gramWeight z := by
  dsimp [gramWeight]
  have : 0 ≤ ∑ a : Fin 2, ∑ c : Fin 3, ‖coefficient a c z‖^2 := by positivity
  linarith

theorem gramWeight_pos (z : SourceCoordinateSlice) : 0 < gramWeight z :=
  zero_lt_one.trans_le (gramWeight_one_le z)

theorem gramWeight_continuous : Continuous gramWeight := by
  unfold gramWeight
  exact continuous_const.add (continuous_finsetSum _ (fun a _ =>
    continuous_finsetSum _ (fun c _ => (coefficient_smooth a c).continuous.norm.pow 2)))

def graphMeasure : Measure physicalChart :=
  (GaussHistoryHilbert.numberMeasure 1).withDensity (fun z => ENNReal.ofReal (gramWeight z))

instance graph_locallyFinite : IsLocallyFiniteMeasure graphMeasure :=
  IsLocallyFiniteMeasure.withDensity_ofReal
    (gramWeight_continuous.comp continuous_subtype_val)

instance graph_regular : graphMeasure.Regular := inferInstance

abbrev Profile := Lp ℂ 2 graphMeasure

def coreProfile (f : ScalarTest) : Profile :=
  ((f.continuous.comp continuous_subtype_val).memLp_of_hasCompactSupport
    (restricted_compact f.hasCompactSupport f.tsupport_subset)).toLp _

theorem coreProfile_ae (f : ScalarTest) :
    coreProfile f =ᵐ[graphMeasure] (fun z : physicalChart => f z) :=
  MemLp.coeFn_toLp _

def core : ScalarTest →ₗ[ℂ] Profile where
  toFun := coreProfile
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coreProfile_ae (f+g),coreProfile_ae f,coreProfile_ae g,
      Lp.coeFn_add (coreProfile f) (coreProfile g)] with z h hf hg ha
    rw [h,ha,Pi.add_apply,hf,hg]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [coreProfile_ae (c • f),coreProfile_ae f,
      Lp.coeFn_smul c (coreProfile f)] with z h hf hs
    simp only [RingHom.id_apply]
    rw [h,hs,Pi.smul_apply,hf]
    rfl

theorem core_dense : DenseRange core := by
  have dense := OpenChartTestDomain.dense_compact_contDiff_inside
    physicalChart graphMeasure (F := ℂ) (p := 2) (by norm_num)
  apply dense.mono
  rintro f ⟨g,hfg,hgk,hgc,hgs⟩
  let test : ScalarTest := ⟨g,hgc,hgk,hgs⟩
  refine ⟨test,?_⟩
  exact Lp.ext ((coreProfile_ae test).trans hfg.symm)

theorem profile_core_approximation (f : Profile) (ε : ℝ) (positive : 0<ε) :
    ∃ g : ScalarTest, ‖core g-f‖<ε := by
  obtain ⟨g,hg⟩ := core_dense.exists_dist_lt f positive
  refine ⟨g,?_⟩
  rw [norm_sub_rev]
  exact (dist_eq_norm f (core g)) ▸ hg

def seedSection : ScalarTest →ₗ[ℂ] QuantumTest :=
  (TestFunction.postcompCLM
    ((ContinuousLinearMap.id ℂ ℂ).smulRight CanonicalCompletedSector.seed)).toLinearMap

theorem seedSection_apply (f : ScalarTest) (z : SourceCoordinateSlice) :
    seedSection f z=f z • CanonicalCompletedSector.seed := rfl

theorem seed_zero_off_one (word : Occupation) (different : word.card≠1) :
    CanonicalCompletedSector.seed word=0 := by
  have h := congrArg (fun v : FockFiber => v word)
    CanonicalGradedCurrent.canonical_seed_N1_G0
  have label : NativeHistoryGrade.sourceLabel word≠(1,0) := by
    intro he
    exact different (congrArg (fun g : NativeHistoryGrade.Label => g.1.val) he)
  simpa only [GaussCoreLabel.fiberPiece_apply,if_neg label] using h.symm

theorem seedSection_component (word : Occupation) (f : ScalarTest) :
    component word (seedSection f)=CanonicalCompletedSector.seed word • f := by
  apply DFunLike.ext
  intro z
  change f z*CanonicalCompletedSector.seed word=CanonicalCompletedSector.seed word*f z
  ring

theorem scalarLp_smul (N : ℕ) (c : ℂ) (f : ScalarTest) :
    scalarLp N (c • f)=c • scalarLp N f := by
  apply Lp.ext
  filter_upwards [scalarLp_ae N (c • f),scalarLp_ae N f,
    Lp.coeFn_smul c (scalarLp N f)] with z hc hf hs
  rw [hc,hs,Pi.smul_apply,hf]
  rfl

theorem seedSection_norm_square (f : ScalarTest) :
    ‖embed (seedSection f)‖^2=‖CanonicalCompletedSector.seed‖^2*‖scalarLp 1 f‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro word _
  change ‖scalarLp word.card (component word (seedSection f))‖^2=_
  rw [seedSection_component,scalarLp_smul,norm_smul,mul_pow]
  by_cases h : word.card=1
  · rw [h]
  · rw [seed_zero_off_one word h]
    simp

theorem seedSection_norm (f : ScalarTest) :
    ‖embed (seedSection f)‖=‖CanonicalCompletedSector.seed‖*‖scalarLp 1 f‖ := by
  have h := seedSection_norm_square f
  have hs := norm_nonneg (embed (seedSection f))
  have ht := mul_nonneg (norm_nonneg CanonicalCompletedSector.seed) (norm_nonneg (scalarLp 1 f))
  nlinarith

theorem seed_unit : ‖CanonicalCompletedSector.seed‖=1 := by
  have pair : inner ℂ CanonicalCompletedSector.seed CanonicalCompletedSector.seed=1 := by
    rw [SourceQuantumFockGauge.fiber_pairing]
    change QuantizationCheck.Fermion.pairing
      (QuantizationCheck.Fermion.oneParticle CanonicalCompletedSector.seedCoordinates)
      (QuantizationCheck.Fermion.oneParticle CanonicalCompletedSector.seedCoordinates)=1
    rw [QuantizationCheck.Fermion.pairing_oneParticle]
    simp only [CanonicalCompletedSector.seedCoordinates,Fintype.sum_sum_type,
      Sum.elim_inl,Sum.elim_inr,star_zero,mul_zero,Finset.sum_const_zero,add_zero]
    change LowEnergy.Quantum.coordinatePair _ _=1
    rw [LowEnergy.Quantum.coordinatePair_full,←YangMills.FullPairing.natural_inner]
    have actual := Stage10.ChargedPreparation.CanonicalParticle.full_prepared_gram 0 0
    rw [YangMills.FullPairing.prepared,YangMills.FullPairing.operator_coordinates] at actual
    exact actual
  have real := congrArg Complex.re pair
  change RCLike.re (inner ℂ CanonicalCompletedSector.seed CanonicalCompletedSector.seed)=1 at real
  rw [inner_self_eq_norm_sq] at real
  nlinarith [norm_nonneg CanonicalCompletedSector.seed]

theorem coefficient_square_le (a : Fin 2) (c : Fin 3) (z : SourceCoordinateSlice) :
    ‖coefficient a c z‖^2≤gramWeight z := by
  have inner := Finset.single_le_sum (f := fun c : Fin 3 => ‖coefficient a c z‖^2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ c)
  have outer := Finset.single_le_sum (f := fun a : Fin 2 => ∑ c : Fin 3, ‖coefficient a c z‖^2)
    (fun i _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ a)
  have := inner.trans outer
  dsimp [gramWeight]
  linarith

theorem gram_diagonal (a s : Fin 2) (z : SourceCoordinateSlice) :
    contactCoefficient a s a s z=(∑ c : Fin 3, ‖coefficient a c z‖^2 : ℝ) := by
  simp only [contactCoefficient,ite_true,scalarGram,coefficient]
  push_cast
  apply Finset.sum_congr rfl
  intro c _
  rw [←Complex.ofReal_pow,←Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

theorem gramWeight_original (z : SourceCoordinateSlice) :
    gramWeight z=1+∑ a : Fin 2, (contactCoefficient a 0 a 0 z).re := by
  simp only [gram_diagonal,Complex.ofReal_re,gramWeight]

theorem multiplier_eLpNorm_bound (c : SourceCoordinateSlice → ℂ)
    (bound : ∀ z, ‖c z‖^2≤gramWeight z) (f : physicalChart → ℂ) :
    eLpNorm (fun z : physicalChart => c z*f z) 2 (GaussHistoryHilbert.numberMeasure 1) ≤
      eLpNorm f 2 graphMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  have hm : Measurable (fun z : physicalChart => ENNReal.ofReal (gramWeight z)) :=
    (gramWeight_continuous.comp continuous_subtype_val).measurable.ennreal_ofReal
  rw [graphMeasure,lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro z
  simp only [enorm_mul,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ)≤2)]
  apply mul_le_mul_left
  rw [←ofReal_norm,ENNReal.rpow_two,←ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (bound z)

theorem scalar_multiplier_bound (c : SourceCoordinateSlice → ℂ)
    (smooth : ContDiff ℝ ∞ c) (bound : ∀ z, ‖c z‖^2≤gramWeight z) (f : ScalarTest) :
    ‖scalarLp 1 (multiply c (fun _ => smooth.contDiffAt) f)‖≤‖core f‖ := by
  rw [scalarLp,Lp.norm_toLp]
  change (eLpNorm (fun z : physicalChart => c z*f z) 2
    (GaussHistoryHilbert.numberMeasure 1)).toReal≤‖coreProfile f‖
  rw [coreProfile,Lp.norm_toLp]
  apply ENNReal.toReal_mono _ (multiplier_eLpNorm_bound c bound _)
  rw [←eLpNorm_congr_ae (coreProfile_ae f)]
  exact (Lp.memLp (core f)).eLpNorm_ne_top

theorem scalar_base_bound (f : ScalarTest) : ‖scalarLp 1 f‖≤‖core f‖ := by
  have h := scalar_multiplier_bound (fun _ => (1 : ℂ)) contDiff_const
    (fun z => by simpa using gramWeight_one_le z) f
  have e : multiply (fun _ => (1 : ℂ)) (fun _ => contDiffAt_const) f=f := by
    apply DFunLike.ext
    intro z
    exact one_mul (f z)
  rwa [e] at h

theorem scalar_seedSection (c : SourceCoordinateSlice → ℂ) (smooth : ContDiff ℝ ∞ c)
    (f : ScalarTest) :
    scalarMultiplier c smooth (seedSection f)=
      seedSection (multiply c (fun _ => smooth.contDiffAt) f) := by
  apply DFunLike.ext
  intro z
  change c z • (f z • CanonicalCompletedSector.seed)=(c z*f z) • CanonicalCompletedSector.seed
  exact (mul_smul (c z) (f z) CanonicalCompletedSector.seed).symm

def seedCore : ScalarTest →ₗ[ℂ] H := embed.comp seedSection

theorem seedCore_bound (f : ScalarTest) :
    ‖seedCore f‖≤‖CanonicalCompletedSector.seed‖*‖core f‖ := by
  change ‖embed (seedSection f)‖≤_
  rw [seedSection_norm]
  exact mul_le_mul_of_nonneg_left (scalar_base_bound f) (norm_nonneg _)

theorem scalar_seed_bound (c : SourceCoordinateSlice → ℂ) (smooth : ContDiff ℝ ∞ c)
    (bound : ∀ z, ‖c z‖^2≤gramWeight z) (f : ScalarTest) :
    ‖embed (scalarMultiplier c smooth (seedSection f))‖≤‖CanonicalCompletedSector.seed‖*‖core f‖ := by
  rw [scalar_seedSection,seedSection_norm]
  exact mul_le_mul_of_nonneg_left (scalar_multiplier_bound c smooth bound f) (norm_nonneg _)

def legCore (addition : Bool) (a s : Fin 2) : ScalarTest →ₗ[ℂ] H :=
  (leg addition a s).comp seedSection

def legBound : ℝ := 3*‖CanonicalCompletedSector.seed‖

theorem legBound_nonnegative : 0≤legBound := by unfold legBound; positivity

theorem legCore_bound (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    ‖legCore addition a s f‖≤legBound*‖core f‖ := by
  have total : (∑ _c : Fin 3, ‖CanonicalCompletedSector.seed‖*‖core f‖)=legBound*‖core f‖ := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,legBound]
    ring
  cases addition with
  | false =>
    change ‖annihilationSource a s (seedSection f)‖≤_
    apply (annihilation_bound a s (seedSection f)).trans
    rw [←total]
    exact Finset.sum_le_sum (fun c _ =>
      scalar_seed_bound (coefficient a c) (coefficient_smooth a c) (coefficient_square_le a c) f)
  | true =>
    change ‖creationSource a s (seedSection f)‖≤_
    rw [creationSource,LinearMap.sum_apply]
    apply (norm_sum_le _ _).trans
    rw [←total]
    apply Finset.sum_le_sum
    intro c _
    apply (GaussCARHistory.create_bound _ _).trans
    apply scalar_seed_bound
    intro z
    simpa only [norm_star] using coefficient_square_le a c z

theorem original_contact_control (a s : Fin 2) (f : ScalarTest) :
    (GaussFockPair.sourcePair (seedSection f)
      (contactSource a s a s (seedSection f))).re≤2*(legBound*‖core f‖)^2 := by
  rw [←source_contact_norm]
  have left := legCore_bound true a s f
  have right := legCore_bound false a s f
  change ‖creationSource a s (seedSection f)‖≤_ at left
  change ‖annihilationSource a s (seedSection f)‖≤_ at right
  have hl := pow_le_pow_left₀ (norm_nonneg _) left 2
  have hr := pow_le_pow_left₀ (norm_nonneg _) right 2
  linarith

def prepared : Profile →L[ℂ] H := seedCore.extendOfNorm core

def completedLeg (addition : Bool) (a s : Fin 2) : Profile →L[ℂ] H :=
  (legCore addition a s).extendOfNorm core

theorem prepared_core (f : ScalarTest) : prepared (core f)=embed (seedSection f) :=
  LinearMap.extendOfNorm_eq core_dense ⟨_,seedCore_bound⟩ f

theorem completedLeg_core (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    completedLeg addition a s (core f)=leg addition a s (seedSection f) :=
  LinearMap.extendOfNorm_eq core_dense ⟨_,legCore_bound addition a s⟩ f

theorem prepared_bound (f : Profile) : ‖prepared f‖≤‖CanonicalCompletedSector.seed‖*‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le core_dense _ seedCore_bound f

theorem completedLeg_bound (addition : Bool) (a s : Fin 2) (f : Profile) :
    ‖completedLeg addition a s f‖≤legBound*‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le core_dense _ (legCore_bound addition a s) f

theorem all_legs_core_approximation (f : Profile) (ε : ℝ) (positive : 0<ε) :
    ∃ g : ScalarTest,
      ‖core g-f‖<ε ∧
      ‖embed (seedSection g)-prepared f‖≤‖CanonicalCompletedSector.seed‖*ε ∧
      ∀ (addition : Bool) (a s : Fin 2),
        ‖leg addition a s (seedSection g)-completedLeg addition a s f‖≤legBound*ε := by
  obtain ⟨g,hg⟩ := profile_core_approximation f ε positive
  refine ⟨g,hg,?_,?_⟩
  · rw [←prepared_core,←map_sub]
    exact (prepared_bound _).trans
      (mul_le_mul_of_nonneg_left hg.le (norm_nonneg _))
  · intro addition a s
    rw [←completedLeg_core,←map_sub]
    exact (completedLeg_bound addition a s _).trans
      (mul_le_mul_of_nonneg_left hg.le legBound_nonnegative)

open GaussUnitaryHistory (HistorySpace inclusion)

def response (A : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) : ℂ :=
  inner ℂ (inclusion (completedLeg left a s f))
    (A (inclusion (completedLeg right b t g)))

theorem response_core (A : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) (f g : ScalarTest) :
    response A left right a s b t (core f) (core g)=
      inner ℂ (inclusion (leg left a s (seedSection f)))
        (A (inclusion (leg right b t (seedSection g)))) := by
  simp only [response,completedLeg_core]

theorem response_bound (A : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) :
    ‖response A left right a s b t f g‖≤legBound^2*‖A‖*‖f‖*‖g‖ := by
  unfold response
  calc
    _ ≤ ‖inclusion (completedLeg left a s f)‖*
        ‖A (inclusion (completedLeg right b t g))‖ := norm_inner_le_norm _ _
    _ ≤ ‖completedLeg left a s f‖*(‖A‖*‖completedLeg right b t g‖) := by
      rw [inclusion.norm_map]
      exact mul_le_mul_of_nonneg_left
        ((A.le_opNorm _).trans_eq (by rw [inclusion.norm_map])) (norm_nonneg _)
    _ ≤ (legBound*‖f‖)*(‖A‖*(legBound*‖g‖)) := by
      exact mul_le_mul (completedLeg_bound left a s f)
        (mul_le_mul_of_nonneg_left (completedLeg_bound right b t g) (norm_nonneg A))
        (mul_nonneg (norm_nonneg A) (norm_nonneg _))
        (mul_nonneg legBound_nonnegative (norm_nonneg f))
    _ = _ := by ring

theorem response_difference (A : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) (f f' g g' : Profile) :
    response A left right a s b t f g-response A left right a s b t f' g'=
      response A left right a s b t (f-f') g+
      response A left right a s b t f' (g-g') := by
  simp only [response,map_sub,inner_sub_left,inner_sub_right]
  abel

theorem response_error (A : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) (f f' g g' : Profile) :
    ‖response A left right a s b t f g-response A left right a s b t f' g'‖≤
      legBound^2*‖A‖*(‖f-f'‖*‖g‖+‖f'‖*‖g-g'‖) := by
  rw [response_difference]
  apply (norm_add_le _ _).trans
  apply (add_le_add (response_bound A left right a s b t (f-f') g)
    (response_bound A left right a s b t f' (g-g'))).trans_eq
  ring

theorem response_continuous (A : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) :
    Continuous (fun fg : Profile×Profile => response A left right a s b t fg.1 fg.2) := by
  unfold response
  fun_prop

theorem original_composite_kernel_return
    (phi : CanonicalGradedSpatial.Localizer)
    (p k ell : CanonicalGradedSpatialSource.PhysicalMomentum)
    (A B : CanonicalGradedSpatialKernel.NativeCurrent)
    (cut : ℕ) (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) :
    response (Bilocal.fullResponse phi p k ell A B cut age frequency damping positive)
        left right a s b t f g=
      response (CanonicalGradedBilocal.response phi p k ell A B age frequency damping positive)
        left right a s b t f g := by
  have onCore : ∀ u v : ScalarTest,
      response (Bilocal.fullResponse phi p k ell A B cut age frequency damping positive)
          left right a s b t (core u) (core v)=
        response (CanonicalGradedBilocal.response phi p k ell A B age frequency damping positive)
          left right a s b t (core u) (core v) := by
    intro u v
    rw [response_core,response_core]
    exact Bilocal.composite_response_return phi p k ell A B cut age frequency damping positive
      left right a s b t (seedSection u) (seedSection v) u (seedSection_apply u)
  refine core_dense.induction_on₂ ?_ onCore f g
  exact isClosed_eq (response_continuous _ left right a s b t)
    (response_continuous _ left right a s b t)

end LowEnergy.GaussComposite.SourceGraph
