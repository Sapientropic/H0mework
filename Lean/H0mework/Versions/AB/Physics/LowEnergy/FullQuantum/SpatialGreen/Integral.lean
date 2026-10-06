import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialGreen.Equation
import Mathlib.MeasureTheory.Integral.Prod

/-! Strong L² time integration is the same source Green as the full Fourier multiplier. -/
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open MatterSpace.Response
noncomputable section

def timeIntegrand (point : BasePoint) (energy damping : ℝ) (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  temporalWeight energy damping time • momentumFlow point time initial

theorem timeIntegrand_continuous (point : BasePoint) (energy damping : ℝ) (initial : FullMatterL2) :
    Continuous (timeIntegrand point energy damping initial) :=
  (temporalWeight_continuous energy damping).smul (momentumFlow_stronglyContinuous point initial)

theorem timeIntegrand_bound (point : BasePoint) (energy damping time : ℝ) (initial : FullMatterL2)
    (future : 0≤time) :
    ‖timeIntegrand point energy damping initial time‖≤Retarded.envelope damping (sourceRate point) time*‖initial‖ := by
  rw [timeIntegrand,norm_smul,temporalWeight_norm]
  have estimate := ((momentumFlow point time).le_opNorm initial).trans
    (mul_le_mul_of_nonneg_right (momentumFlow_norm point time) (norm_nonneg _))
  rw [abs_of_nonneg future] at estimate
  exact (mul_le_mul_of_nonneg_left estimate (Real.exp_pos _).le).trans_eq (by
    unfold Retarded.envelope; ring)

theorem timeIntegrand_integrable (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (initial : FullMatterL2) : IntegrableOn (timeIntegrand point energy damping initial) (Ioi 0) := by
  apply ((Retarded.envelope_integrable damping (sourceRate point) positive).mul_const ‖initial‖).mono'
    (timeIntegrand_continuous point energy damping initial).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
  exact timeIntegrand_bound point energy damping t initial future.le

def momentumIntegral (point : BasePoint) (energy damping : ℝ) (initial : FullMatterL2) : FullMatterL2 :=
  ∫ t : ℝ in Ioi 0, timeIntegrand point energy damping initial t

def pairIntegrand (point : BasePoint) (energy damping : ℝ) (test initial : FullMatterL2)
    (time : ℝ) (frequency : Position) : ℂ :=
  inner ℂ (test frequency)
    (Retarded.integrand point (physicalMomentum frequency) energy damping time (initial frequency))

theorem pairIntegrand_measurable (point : BasePoint) (energy damping : ℝ) (test initial : FullMatterL2) :
    AEStronglyMeasurable (Function.uncurry (pairIntegrand point energy damping test initial))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Position)) := by
  have matrices : Continuous (fun tx : ℝ × Position =>
      Retarded.integrand point (physicalMomentum tx.2) energy damping tx.1) :=
    ((temporalWeight_continuous energy damping).comp continuous_fst).smul (fullMatrices_continuous point)
  have applied : AEStronglyMeasurable (fun tx : ℝ × Position =>
      Retarded.integrand point (physicalMomentum tx.2) energy damping tx.1 (initial tx.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Position)) := (isBoundedBilinearMap_apply : IsBoundedBilinearMap ℂ
    (fun pair : FiberOperators × Hilbert => pair.1 pair.2)).continuous.comp_aestronglyMeasurable
      (matrices.aestronglyMeasurable.prodMk (Lp.memLp initial).aestronglyMeasurable.comp_snd)
  exact (Lp.memLp test).aestronglyMeasurable.comp_snd.inner applied

theorem pairIntegrand_integrable (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (test initial : FullMatterL2) :
    Integrable (Function.uncurry (pairIntegrand point energy damping test initial))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Position)) := by
  have spatial : Integrable (fun x => ‖test x‖*‖initial x‖) volume :=
    (Lp.memLp test).norm.integrable_mul (Lp.memLp initial).norm
  have majorant := (Retarded.envelope_integrable damping (sourceRate point) positive).mul_prod spatial
  apply majorant.mono' (pairIntegrand_measurable point energy damping test initial)
  have future : ∀ᵐ tx : ℝ × Position ∂(volume.restrict (Ioi (0 : ℝ))).prod volume, 0≤tx.1 := by
    exact (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)).mono fun _ h => h.le
  filter_upwards [future] with tx later
  calc
    ‖pairIntegrand point energy damping test initial tx.1 tx.2‖
      ≤ ‖test tx.2‖*‖Retarded.integrand point (physicalMomentum tx.2) energy damping tx.1 (initial tx.2)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖test tx.2‖*(Retarded.envelope damping (sourceRate point) tx.1*‖initial tx.2‖) := by
      gcongr
      exact ((Retarded.integrand point (physicalMomentum tx.2) energy damping tx.1).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (Retarded.integrand_bound point (physicalMomentum tx.2)
          energy damping tx.1 later) (norm_nonneg _))
    _ = _ := by ring

theorem timeIntegrand_ae (point : BasePoint) (energy damping time : ℝ) (initial : FullMatterL2) :
    timeIntegrand point energy damping initial time=ᵐ[volume] fun frequency =>
      Retarded.integrand point (physicalMomentum frequency) energy damping time (initial frequency) := by
  filter_upwards [momentumFlow_ae point time initial,
    Lp.coeFn_smul (temporalWeight energy damping time) (momentumFlow point time initial)] with frequency flow scaled
  change (temporalWeight energy damping time • momentumFlow point time initial) frequency=_
  rw [scaled]
  change temporalWeight energy damping time • momentumFlow point time initial frequency=_
  rw [flow]
  rfl

theorem momentumIntegral_pair (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (test initial : FullMatterL2) :
    inner ℂ test (momentumIntegral point energy damping initial)=
      ∫ frequency, inner ℂ (test frequency)
        (Retarded.value point (physicalMomentum frequency) energy damping (initial frequency)) := by
  rw [momentumIntegral,← integral_inner (timeIntegrand_integrable point energy damping positive initial)]
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ frequency, pairIntegrand point energy damping test initial t frequency := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        change inner ℂ test (timeIntegrand point energy damping initial t)=_
        erw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [timeIntegrand_ae point energy damping t initial] with frequency read
        rw [read]
        rfl
    _ = ∫ frequency, ∫ t : ℝ in Ioi 0, pairIntegrand point energy damping test initial t frequency :=
      integral_integral_swap (pairIntegrand_integrable point energy damping positive test initial)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun frequency => by
        have admissible := Retarded.integrand_integrable point (physicalMomentum frequency) energy damping positive
        have vector := (ContinuousLinearMap.apply ℂ Hilbert (initial frequency)).integrable_comp admissible
        change (∫ t : ℝ in Ioi 0, inner ℂ (test frequency)
          (Retarded.integrand point (physicalMomentum frequency) energy damping t (initial frequency)))=_
        erw [integral_inner vector]
        congr 1
        exact (ContinuousLinearMap.integral_apply admissible (initial frequency)).symm

theorem momentumIntegral_ae (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (initial : FullMatterL2) : momentumIntegral point energy damping initial=ᵐ[volume]
      fun frequency => Retarded.value point (physicalMomentum frequency) energy damping (initial frequency) := by
  let coefficient := fun frequency : Position => Retarded.value point (physicalMomentum frequency) energy damping
  have continuous : Continuous coefficient :=
    (Retarded.value_continuous point energy damping positive).comp physicalMomentum_continuous
  let size := damping⁻¹+sourceRate point*damping⁻¹^2
  have bounded : ∀ frequency, ‖coefficient frequency‖ ≤ size := fun frequency =>
    Retarded.value_bound point (physicalMomentum frequency) energy damping positive
  let generated := multiplierValue coefficient continuous size bounded initial
  have read : generated=ᵐ[volume] fun frequency => coefficient frequency (initial frequency) :=
    multiplierValue_ae coefficient continuous size bounded initial
  have same : momentumIntegral point energy damping initial=generated := by
    apply ext_inner_left ℂ
    intro test
    rw [momentumIntegral_pair point energy damping positive,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [read] with frequency hf
    rw [hf]
  rw [same]
  exact read

theorem momentumGreen_integral (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : momentumGreen point energy damping positive source=
      momentumIntegral point energy damping (inversePrincipal point source) := by
  apply Lp.ext
  filter_upwards [momentumGreen_ae point energy damping positive source,
    momentumIntegral_ae point energy damping positive (inversePrincipal point source),
    (operator (StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipalInverse
      (actual.coframe point))).coeFn_compLpL source] with frequency green integrated principal
  rw [green,integrated]
  erw [principal]
  rw [Retarded.diracValue_side point (physicalMomentum frequency) energy damping positive]
  rfl

private theorem constant_toLp (L : Hilbert →L[ℂ] Hilbert) (f : SchwartzMap Position Hilbert) :
    L.compLpL 2 volume (f.toLp 2)=(f.postcompCLM L).toLp 2 := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (f.toLp 2),f.coeFn_toLp 2 volume,
    (f.postcompCLM L).coeFn_toLp 2 volume] with x hl hf hg
  erw [hl,hf]

private theorem constant_fourier_schwartz (L : Hilbert →L[ℂ] Hilbert) (f : SchwartzMap Position Hilbert) :
    FourierTransform.fourier (f.postcompCLM L)=(FourierTransform.fourier f).postcompCLM L := by
  apply SchwartzMap.ext
  intro xi
  rw [SchwartzMap.fourier_coe,SchwartzMap.postcompCLM_apply,
    SchwartzMap.fourier_coe,Real.fourier_eq,Real.fourier_eq]
  have generated := L.integral_comp_comm
    ((Real.fourierIntegral_convergent_iff (μ := volume) xi).mpr f.integrable)
  simpa only [SchwartzMap.postcompCLM_apply,Circle.smul_def,map_smul] using generated

private theorem constant_fourier (L : Hilbert →L[ℂ] Hilbert) (f : FullMatterL2) :
    fourier (L.compLpL 2 volume f)=L.compLpL 2 volume (fourier f) := by
  apply DenseRange.induction_on (p := fun g : FullMatterL2 =>
      fourier (L.compLpL 2 volume g)=L.compLpL 2 volume (fourier g))
    (SchwartzMap.denseRange_toLpCLM (E := Position) (F := Hilbert) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (fourier.continuous.comp (L.compLpL 2 volume).continuous)
      ((L.compLpL 2 volume).continuous.comp fourier.continuous)
  · intro test
    change FourierTransform.fourier (L.compLpL 2 volume (test.toLp 2))=
      L.compLpL 2 volume (FourierTransform.fourier (test.toLp 2))
    rw [constant_toLp,SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq,
      constant_toLp,constant_fourier_schwartz]

theorem green_time_integral (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : green point energy damping positive source=
      ∫ t : ℝ in Ioi 0, temporalWeight energy damping t • spatialFlow point t (inversePrincipal point source) := by
  change fourier.symm (momentumGreen point energy damping positive (fourier source))=_
  rw [momentumGreen_integral point energy damping positive]
  have exchanged := fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (timeIntegrand_integrable point energy damping positive (inversePrincipal point (fourier source)))
  change fourier.symm (∫ t : ℝ in Ioi 0,
    timeIntegrand point energy damping (inversePrincipal point (fourier source)) t)=_
  erw [← exchanged]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    change fourier.symm (temporalWeight energy damping t •
      momentumFlow point t (inversePrincipal point (fourier source)))=_
    rw [map_smul]
    congr 1
    change fourier.symm (momentumFlow point t (inversePrincipal point (fourier source)))=
      fourier.symm (momentumFlow point t (fourier (inversePrincipal point source)))
    rw [inversePrincipal,constant_fourier]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialGreen
