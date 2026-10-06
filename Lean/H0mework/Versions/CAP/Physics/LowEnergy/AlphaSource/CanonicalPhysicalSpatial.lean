import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalGradedSpatial

/-! The original unlocalized physical principal is compressed on exactly the
same finite source core and filter. No localizer enters this time generator. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalSpatial
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussQuantumMultiplier GaussFockLabel CanonicalGradedSpatialSource
open NativeHistoryGrade SymmetricGraphClosure
open GaussUnitaryHistory (HistorySpace Index sourceFilter)
open scoped Topology InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance labelFintype : Fintype Label := Fintype.ofFinite _

abbrev momentumAction := CanonicalGradedSpatial.sourceAction

theorem momentumAction_pair (p : PhysicalMomentum) (f g : QuantumTest) :
    sourcePair f (momentumAction p g)=sourcePair (momentumAction p f) g := by
  rw [sourcePair_integral, sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    (quantized (momentumMatrix z p) (g z)) = inner ℂ
    (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
      (quantized (momentumMatrix z p) (f z))) (g z)
  exact weighted_pair _ (momentumMatrix z p) (momentumMatrix_hermitian z p) (f z) (g z)

theorem momentumAction_zero : momentumAction 0=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantizer (momentumMatrix z 0) (f z)=0
  rw [momentumMatrix_zero, map_zero]
  rfl

theorem momentumAction_blocks (p : PhysicalMomentum) (g : Label) :
    GaussCoreLabel.Commutes g (momentumAction p) := by
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreLabel.fiberPiece g (quantized (momentumMatrix z p) (f z)) =
    quantized (momentumMatrix z p) (GaussCoreLabel.fiberPiece g (f z))
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (blockWeight_quantized (fun l => if l=g then 1 else 0) (momentumMatrix z p)
      (momentumMatrix_preserves z p)).eq

def physicalAction (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  diagonalAction+momentumAction p

theorem physicalAction_zero : physicalAction 0=diagonalAction := by
  rw [physicalAction, momentumAction_zero, add_zero]

theorem physicalAction_pair (p : PhysicalMomentum) (f g : QuantumTest) :
    sourcePair f (physicalAction p g)=sourcePair (physicalAction p f) g := by
  change inner ℂ (embed f) (embed (diagonalAction g+momentumAction p g)) =
    inner ℂ (embed (diagonalAction f+momentumAction p f)) (embed g)
  simp only [map_add, inner_add_left, inner_add_right]
  exact congrArg₂ HAdd.hAdd (diagonalAction_pair f g) (momentumAction_pair p f g)

theorem physicalAction_blocks (p : PhysicalMomentum) (g : Label) :
    GaussCoreLabel.Commutes g (physicalAction p) :=
  GaussCoreLabel.commutes_add g (GaussDiagonalGrade.diagonal_action g) (momentumAction_blocks p g)

def physical (p : PhysicalMomentum) : H →ₗ.[ℂ] H := realize (physicalAction p)

theorem physical_zero : physical 0=diagonal := congrArg realize physicalAction_zero

theorem physical_core (p : PhysicalMomentum) (f : QuantumTest) :
    physical p (coreEquiv f)=embed (diagonalAction f)+embed (momentumAction p f) := by
  change embed (physicalAction p (coreEquiv.symm (coreEquiv f))) = _
  rw [coreEquiv.symm_apply_apply]
  exact map_add embed _ _

theorem physical_pair (p : PhysicalMomentum) : FormalAdjointPair (physical p) (physical p) := by
  intro f g
  obtain ⟨f,rfl⟩ := coreEquiv.surjective f
  obtain ⟨g,rfl⟩ := coreEquiv.surjective g
  change inner ℂ (embed (physicalAction p (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed (physicalAction p (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply]
  exact (physicalAction_pair p f g).symm

theorem physical_invariant (p : PhysicalMomentum) (f : diagonal.domain) :
    physical p f ∈ diagonal.domain := realize_preserves_core (physicalAction p) f

theorem physical_blocks (p : PhysicalMomentum) (g : Label) (f : diagonal.domain) :
    physical p (GaussGradedCompression.piece g f)=projection g (physical p f) := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective f
  have projected : GaussGradedCompression.piece g (coreEquiv f)=coreEquiv (GaussCoreLabel.project g f) :=
    Subtype.ext (GaussCoreLabel.embed_project g f).symm
  rw [projected]
  change embed (physicalAction p (coreEquiv.symm (coreEquiv (GaussCoreLabel.project g f)))) =
    projection g (embed (physicalAction p (coreEquiv.symm (coreEquiv f))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply, ← GaussCoreLabel.embed_project]
  exact congrArg embed (physicalAction_blocks p g f).symm

def compression (p : PhysicalMomentum) (F : Index) : H →L[ℂ] H :=
  ∑ g : Label, projection g*FiniteCoreEvolution.compression (physical p) F*projection g

theorem compression_apply (p : PhysicalMomentum) (F : Index) (x : H) :
    compression p F x=∑ g : Label, projection g
      (FiniteCoreEvolution.compression (physical p) F (projection g x)) := by
  simp only [compression, sum_apply, mul_apply_eq_comp]

theorem compression_pair (p : PhysicalMomentum) (F : Index) :
    (compression p F).toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, compression_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact (projection_symmetric g _ _).trans
    ((FiniteCoreEvolution.compression_symmetric (physical p) (physical_pair p) F _ _).trans
      (projection_symmetric g _ _))

theorem compression_selfAdjoint (p : PhysicalMomentum) (F : Index) :
    IsSelfAdjoint (compression p F) := (compression_pair p F).isSelfAdjoint

theorem compression_zero (F : Index) : compression 0 F=GaussGradedCompression.compression F := by
  exact congrArg (fun A : QuantumTest →ₗ[ℂ] QuantumTest =>
    ∑ g : Label, projection g*FiniteCoreEvolution.compression (realize A) F*projection g)
      physicalAction_zero

theorem left_block (p : PhysicalMomentum) (F : Index) (g : Label) :
    projection g*compression p F=projection g*FiniteCoreEvolution.compression (physical p) F*projection g := by
  calc
    _ = ∑ h : Label, (projection g*projection h)*FiniteCoreEvolution.compression (physical p) F*projection h := by
      simp only [compression, Finset.mul_sum, mul_assoc]
    _ = _ := by simp [projection_product, ite_mul]

theorem right_block (p : PhysicalMomentum) (F : Index) (g : Label) :
    compression p F*projection g=projection g*FiniteCoreEvolution.compression (physical p) F*projection g := by
  calc
    _ = ∑ h : Label, projection h*FiniteCoreEvolution.compression (physical p) F*(projection h*projection g) := by
      simp only [compression, Finset.sum_mul, mul_assoc]
    _ = _ := by simp [projection_product, mul_ite]

theorem compression_blocks (p : PhysicalMomentum) (F : Index) (g : Label) :
    Commute (projection g) (compression p F) := by
  show projection g*compression p F=compression p F*projection g
  rw [left_block, right_block]

theorem compression_core_exact (p : PhysicalMomentum) (F : Index) (x : diagonal.domain)
    (contains : ∀ g : Label, GaussGradedCompression.piece g x ∈ F)
    (contains_next : ∀ g : Label,
      GaussGradedCompression.piece g ⟨physical p x, physical_invariant p x⟩ ∈ F) :
    compression p F (x : H)=physical p x := by
  have exactBlock (g : Label) : FiniteCoreEvolution.compression (physical p) F (projection g (x : H)) =
      projection g (physical p x) := by
    have original := FiniteCoreEvolution.compression_core_exact (physical p) F
      (GaussGradedCompression.piece g x) (physical_invariant p (GaussGradedCompression.piece g x)) (contains g)
    have next : (⟨physical p (GaussGradedCompression.piece g x),
        physical_invariant p (GaussGradedCompression.piece g x)⟩ : diagonal.domain) =
        GaussGradedCompression.piece g ⟨physical p x, physical_invariant p x⟩ :=
      Subtype.ext (physical_blocks p g x)
    rw [next] at original
    exact (original (contains_next g)).trans (physical_blocks p g x)
  rw [compression_apply]
  simp_rw [exactBlock, GaussGradedCompression.projection_idempotent]
  rw [← sum_apply, projection_resolution, one_apply_eq_self]

theorem eventually_exact (p : PhysicalMomentum) (x : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), compression p F (x : H)=physical p x := by
  filter_upwards [GaussGradedCompression.eventually_contains x,
    GaussGradedCompression.eventually_contains ⟨physical p x, physical_invariant p x⟩] with F h hnext
  exact compression_core_exact p F x h hnext

theorem compression_core_bound (p : PhysicalMomentum) (F : Index) (x : diagonal.domain)
    (contains : ∀ g : Label, GaussGradedCompression.piece g x ∈ F) :
    ‖compression p F (x : H)‖ ≤ ‖physical p x‖ := by
  have blockBound (g : Label) :
      ‖projection g (FiniteCoreEvolution.compression (physical p) F (projection g (x : H)))‖ ≤
        ‖projection g (physical p x)‖ := by
    have coreBound := FiniteCoreEvolution.compression_core_bound (physical p) F
      (GaussGradedCompression.piece g x)
      (FiniteCoreEvolution.mem_coreSpan (physical p) F (GaussGradedCompression.piece g x) (contains g))
    exact ((piece_bound g _).trans coreBound).trans_eq (congrArg norm (physical_blocks p g x))
  have square : ‖compression p F (x : H)‖^2 ≤ ‖physical p x‖^2 := by
    rw [compression_apply, norm_sum_projection, ← norm_resolution (physical p x)]
    exact Finset.sum_le_sum (fun g _ => pow_le_pow_left₀ (norm_nonneg _) (blockBound g) 2)
  nlinarith [norm_nonneg (compression p F (x : H)), norm_nonneg (physical p x)]

open SourceFamilyOperator
open GaussUnitaryHistory (inclusion reader)
open SourceFamilyHilbert (Family value)
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

def finiteTime (p : PhysicalMomentum) (t : ℝ) : Operator Index H where
  component F := SourceFiniteUnitary.time (compression p F) t
  bounded := ⟨1, zero_le_one, fun F x => by
    rw [SourceFiniteUnitary.time_norm _ (compression_selfAdjoint p F), one_mul]⟩

def time (p : PhysicalMomentum) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (finiteTime p t)

theorem time_original (t : ℝ) : time 0 t=GaussGradedUnitary.time t := by
  apply lift_congr sourceFilter
  intro F
  exact congrArg (fun C : H →L[ℂ] H => SourceFiniteUnitary.time C t) (compression_zero F)

theorem time_zero (p : PhysicalMomentum) : time p 0=1 :=
  (lift_congr sourceFilter (finiteTime p 0) (constant 1)
    (fun F => SourceFiniteUnitary.time_zero (compression p F))).trans (lift_identity (E := H) sourceFilter)

theorem time_add (p : PhysicalMomentum) (s t : ℝ) : time p (s+t)=time p s*time p t :=
  (lift_congr sourceFilter (finiteTime p (s+t)) (comp (finiteTime p s) (finiteTime p t))
    (fun F => SourceFiniteUnitary.time_add (compression p F) s t)).trans (lift_comp sourceFilter _ _)

theorem time_norm (p : PhysicalMomentum) (t : ℝ) (x : HistorySpace) : ‖time p t x‖=‖x‖ :=
  lift_isometry sourceFilter (finiteTime p t)
    (fun F x => SourceFiniteUnitary.time_norm _ (compression_selfAdjoint p F) t x) x

theorem time_blocks (p : PhysicalMomentum) (t : ℝ) (g : Label) :
    reader (projection g)*time p t=time p t*reader (projection g) := by
  calc
    _ = lift sourceFilter (comp (constant (projection g)) (finiteTime p t)) := (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (finiteTime p t) (constant (projection g))) := by
      apply lift_congr sourceFilter
      intro F
      exact (SourceFiniteUnitary.time_commutes _ _ (compression_blocks p F g) t).eq
    _ = _ := lift_comp sourceFilter _ _

def trajectory (p : PhysicalMomentum) (t : ℝ) (x : H) : Family H sourceFilter :=
  act sourceFilter (finiteTime p t) (SourceFamilyHilbert.constant sourceFilter x)

theorem time_inclusion (p : PhysicalMomentum) (t : ℝ) (x : H) :
    time p t (inclusion x)=(trajectory p t x : HistorySpace) :=
  lift_coe sourceFilter (finiteTime p t) (SourceFamilyHilbert.constant sourceFilter x)

theorem core_remainder (p : PhysicalMomentum) (x : diagonal.domain) (t h : ℝ) :
    ‖time p (t+h) (inclusion (x : H))-time p t (inclusion (x : H))-
      h • ((-Complex.I) • time p t (inclusion (physical p x)))‖ ≤
      ‖physical p ⟨physical p x, physical_invariant p x⟩‖*‖h‖^2 := by
  classical
  let r : Family H sourceFilter := trajectory p (t+h) x-trajectory p t x-
    ((h : ℂ)*(-Complex.I)) • trajectory p t (physical p x)
  have represent : (r : HistorySpace)=time p (t+h) (inclusion (x : H))-time p t (inclusion (x : H))-
      h • ((-Complex.I) • time p t (inclusion (physical p x))) := by
    rw [time_inclusion, time_inclusion, time_inclusion, ← smul_assoc, Complex.real_smul]
    simp only [r, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul]
  rw [← represent, UniformSpace.Completion.norm_coe]
  apply SourceFamilyHilbert.norm_le_of_eventually sourceFilter r
  filter_upwards [GaussGradedCompression.eventually_contains x,
    GaussGradedCompression.eventually_contains ⟨physical p x, physical_invariant p x⟩] with F hx hnext
  have exactCore := compression_core_exact p F x hx hnext
  have nextBound := compression_core_bound p F ⟨physical p x, physical_invariant p x⟩ hnext
  have estimate := SourceFiniteUnitary.time_remainder (compression p F)
    (compression_selfAdjoint p F) (x : H) t h
  rw [exactCore] at estimate
  have estimate' := estimate.trans (mul_le_mul_of_nonneg_right nextBound (sq_nonneg ‖h‖))
  change ‖SourceFiniteUnitary.time (compression p F) (t+h) (x : H)-
    SourceFiniteUnitary.time (compression p F) t (x : H)-
      ((h : ℂ)*(-Complex.I)) • SourceFiniteUnitary.time (compression p F) t (physical p x)‖ ≤ _
  simpa only [← smul_assoc, Complex.real_smul] using estimate'

theorem core_derivative (p : PhysicalMomentum) (x : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => time p s (inclusion (x : H)))
      ((-Complex.I) • time p t (inclusion (physical p x))) t := by
  rw [hasDerivAt_iff_tendsto]
  let C := ‖physical p ⟨physical p x, physical_invariant p x⟩‖
  have hlim : Filter.Tendsto (fun s : ℝ => C*‖s-t‖) (𝓝 t) (𝓝 0) := by
    have hd : Filter.Tendsto (fun s : ℝ => s-t) (𝓝 t) (𝓝 (t-t)) :=
      (Filter.tendsto_id : Filter.Tendsto (fun s : ℝ => s) (𝓝 t) (𝓝 t)).sub tendsto_const_nhds
    simpa only [sub_self, norm_zero, mul_zero] using hd.norm.const_mul C
  apply squeeze_zero (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun s => ?_) hlim
  have estimate := core_remainder p x t (s-t)
  have scaled := mul_le_mul_of_nonneg_left estimate (inv_nonneg.mpr (norm_nonneg (s-t)))
  rw [show t+(s-t)=s by ring] at scaled
  have scalar : ‖s-t‖⁻¹*(C*‖s-t‖^2)=C*‖s-t‖ := by
    by_cases zero : ‖s-t‖=0
    · simp [zero]
    · field_simp
  exact scaled.trans_eq scalar

theorem full_finite_return (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) (F : Index) :
    CanonicalGradedCurrent.sourceProjection*SourceFiniteUnitary.time
      (compression p F+FullYSourceCutoffVolterra.cutoff cut) t =
    CanonicalGradedCurrent.sourceProjection*SourceFiniteUnitary.time (compression p F) t :=
  CanonicalGradedGaugeReturn.left_time_return _ _ CanonicalGradedCurrent.sourceProjection
    (compression_blocks p F CanonicalGradedCurrent.sourceLabel)
    (CanonicalGradedGaugeReturn.cutoff_projection cut) t

end LowEnergy.CanonicalPhysicalSpatial
