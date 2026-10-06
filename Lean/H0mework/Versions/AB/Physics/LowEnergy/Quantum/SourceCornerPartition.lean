import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHardyRetardedTail

/-! The same source localizer and its complement return the complete finite two-leg response. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceCornerPartition
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert GaussRadialDomain GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient
open SourceCornerWeight SourceGaugeRadialCurrent SourcePhysicalHardyWeight SourceHardyRetardedTail
open FullYSourceResolventGraphSplice
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff Topology InnerProductSpace

theorem localizer_bounds (z : physicalChart) : 0 ≤ localizer z.val ∧ localizer z.val ≤ 1 := by
  have hv := volume_pos z
  have hw := gauge_square_nonneg z.val
  have hden : 0 < (1+volume z.val)*(1+volume z.val*radius z.val^2)*
      (volume z.val^2+gaugeSquare z.val) := by positivity
  constructor
  · unfold localizer
    positivity
  · unfold localizer
    apply (div_le_one hden).mpr
    have ha : 1 ≤ 1+volume z.val := by linarith
    have hb : 1 ≤ 1+volume z.val*radius z.val^2 := by
      have hn := mul_nonneg hv.le (sq_nonneg (radius z.val))
      linarith
    have hab : 1 ≤ (1+volume z.val)*(1+volume z.val*radius z.val^2) :=
      one_le_mul_of_one_le_of_one_le ha hb
    calc
      volume z.val^2 ≤ volume z.val^2+gaugeSquare z.val := by linarith
      _ ≤ (1+volume z.val)*(1+volume z.val*radius z.val^2)*
          (volume z.val^2+gaugeSquare z.val) := by
        exact le_mul_of_one_le_left (by positivity) hab

theorem localizer_smooth (z : physicalChart) : ContDiffAt ℝ ∞ localizer z.val := by
  unfold localizer
  have hden : 0 < (1+volume z.val)*(1+volume z.val*radius z.val^2)*
      (volume z.val^2+gaugeSquare z.val) := by
    have hv := volume_pos z
    have hw := gauge_square_nonneg z.val
    positivity
  apply (volume_smooth.contDiffAt.pow 2).div _ hden.ne'
  exact ((contDiffAt_const.add volume_smooth.contDiffAt).mul
    (contDiffAt_const.add (volume_smooth.contDiffAt.mul (radius_smooth.contDiffAt.pow 2)))).mul
      ((volume_smooth.contDiffAt.pow 2).add gauge_square_smooth.contDiffAt)

private def scalarFiber (a : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) :
    FockFiber →L[ℂ] FockFiber := (a z : ℂ) • ContinuousLinearMap.id ℂ FockFiber

private theorem scalar_smooth (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart, ContDiffAt ℝ ∞ a z.val) (z : physicalChart) :
    ContDiffAt ℝ ∞ (scalarFiber a) z.val :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (ha z)).smul contDiffAt_const

private theorem scalar_commutes (a : SourceCoordinateSlice → ℝ) (z : physicalChart) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (scalarFiber a z.val) :=
  (Commute.one_right _).smul_right _

private theorem scalar_bound (a : SourceCoordinateSlice → ℝ)
    (bounds : ∀ z : physicalChart, 0 ≤ a z.val ∧ a z.val ≤ 1)
    (z : physicalChart) (f : FockFiber) : ‖scalarFiber a z.val f‖ ≤ 1*‖f‖ := by
  change ‖(a z.val : ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bounds z).1]
  exact mul_le_mul_of_nonneg_right (bounds z).2 (norm_nonneg f)

private theorem complement_bounds (z : physicalChart) :
    0 ≤ 1-localizer z.val ∧ 1-localizer z.val ≤ 1 := by
  have h := localizer_bounds z
  constructor <;> linarith

private theorem complement_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => 1-localizer w) z.val := contDiffAt_const.sub (localizer_smooth z)

def localized : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (scalarFiber localizer) (scalar_smooth _ localizer_smooth)
    (scalar_commutes _) 1 (by norm_num) (scalar_bound _ localizer_bounds)

def complement : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (scalarFiber (fun z => 1-localizer z))
    (scalar_smooth _ complement_smooth) (scalar_commutes _) 1 (by norm_num)
    (scalar_bound _ complement_bounds)

theorem localized_norm : ‖localized‖ ≤ 1 :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

theorem complement_norm : ‖complement‖ ≤ 1 :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

theorem localized_core (f : QuantumTest) : localized (embed f)=embed (localizedAction f) := by
  unfold localized
  rw [GaussBoundedMultiplier.extension_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact (localized_action_apply f z).symm

theorem complement_core (f : QuantumTest) :
    complement (embed f)=embed (f-localizedAction f) := by
  unfold complement
  rw [GaussBoundedMultiplier.extension_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change ((1-localizer z : ℝ) : ℂ) • f z=f z-localizedAction f z
  rw [localized_action_apply]
  rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]

theorem whole_partition : localized+complement=1 := by
  apply ContinuousLinearMap.ext
  intro x
  change localized x+complement x=x
  have hc : Set.EqOn (fun y => localized y+complement y) (fun y : H => y) (Core : Set H) := by
    intro y hy
    obtain ⟨f,hf⟩ := coreEquiv.surjective ⟨y,hy⟩
    have hf' : embed f=y := congrArg Subtype.val hf
    rw [←hf']
    change localized (embed f)+complement (embed f)=embed f
    rw [localized_core,complement_core,←map_add]
    congr 1
    abel
  exact hc.closure (localized.continuous.add complement.continuous) continuous_id
    (GaussHistoryHilbert.fockTestDomain_dense x)

theorem whole_history_partition (x : HistorySpace) :
    reader localized x+reader complement x=x := by
  have h := congrArg reader whole_partition
  rw [reader_add,reader_one] at h
  exact congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A x) h

theorem localized_increment (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g : diagonal.domain) :
    localized (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H)))=
      embed (localizedAction (incrementTest sharp m ell F z hz g)) := by
  rw [←increment_test_embed sharp m ell F z hz g,localized_core]

/-- The original full increment retains both the combined residual and the source complement. -/
theorem actual_full_increment_splice (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (k : H) (finiteResolvent F z
      (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))))=
      inner ℂ (k : H) (particular sharp m ell F z (g : H)+
        z • finiteResolvent F z (particular sharp m ell F z (g : H)))+
      inner ℂ (SourceKineticTranspose.outerResidual F (star z)
        (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (particular sharp m ell F z (g : H))+
      inner ℂ (k : H) (finiteResolvent F z (complement
        (SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))))) := by
  let d := SourceEscapeSeedTail.actualIncrement sharp m ell (finiteResolvent F z (g : H))
  have hp : d=localized d+complement d := by
    exact (congrArg (fun A : H →L[ℂ] H => A d) whole_partition).symm
  calc
    _ = inner ℂ (k : H) (finiteResolvent F z (localized d+complement d)) := by rw [←hp]
    _ = inner ℂ (k : H) (finiteResolvent F z (localized d))+
      inner ℂ (k : H) (finiteResolvent F z (complement d)) := by rw [map_add,inner_add_right]
    _ = _ := by
      dsimp only [d]
      rw [localized_increment sharp m ell F z hz g,
        actual_localized_increment_splice sharp m ell F z hz g k]

end LowEnergy.SourceCornerPartition
