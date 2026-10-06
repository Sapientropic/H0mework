import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparedGraph
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPhysicalCausalCharge

/-! Actual scalar-Gram preparations consume the complete unlocalized charge
vertex. Common core approximation and the two independent causal time tails
remain separate, explicit errors; no configuration amplitude is selected. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPreparedFrequency
open GaussCoreHilbert CanonicalGradedSpatialSource CanonicalPhysicalYResolvent
open GaussComposite.SourceGraph
open SourceQuantumScalarChart (NativeLie)
open CanonicalGradedCharge (chargeReader)
open SourceFamilyOperator SourceFamilyHilbert Filter
open GaussUnitaryHistory (Index sourceFilter HistorySpace reader inclusion)
open scoped Topology InnerProductSpace

local notation "W" => CanonicalPhysicalWard.vertex
local notation "V" => CanonicalPhysicalCausalCharge.timeVertex

def vertexNorm (q : NativeLie) (cut : ℕ) (z w : ℂ) : ℝ :=
  normBound cut z*‖chargeReader q‖*normBound cut w

theorem vertexNorm_nonneg (q : NativeLie) (cut : ℕ) (z w : ℂ) : 0≤vertexNorm q cut z w :=
  mul_nonneg (mul_nonneg (normBound_nonneg cut z) (norm_nonneg _)) (normBound_nonneg cut w)

theorem full_vertex_norm (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) : ‖W p k q cut z w hz hw‖ ≤ vertexNorm q cut z w := by
  have out : ‖fullResolvent (p+k) cut z hz‖ ≤ normBound cut z :=
    ContinuousLinearMap.opNorm_le_bound _ (normBound_nonneg cut z) (fullResolvent_bound (p+k) cut z hz)
  have input : ‖fullResolvent p cut w hw‖ ≤ normBound cut w :=
    ContinuousLinearMap.opNorm_le_bound _ (normBound_nonneg cut w) (fullResolvent_bound p cut w hw)
  have charge : ‖reader (chargeReader q)‖ ≤ ‖chargeReader q‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (CanonicalPhysicalWard.charge_bound q)
  rw [CanonicalPhysicalWard.vertex_return]
  exact (norm_mul_le _ _).trans
    (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul out charge (norm_nonneg _) (normBound_nonneg cut z)))
      input (norm_nonneg _) (mul_nonneg (normBound_nonneg cut z) (norm_nonneg _)))

def frequencyRead (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : Bool) (a s b t : Fin 2) (f g : Profile) : ℂ :=
  response (W p k q cut z w hz hw) left right a s b t f g

def timeRead (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) : ℂ :=
  response (V p k q cut z w hz hw T S) left right a s b t f g

theorem frequencyRead_bound (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : Bool) (a s b t : Fin 2) (f g : Profile) :
    ‖frequencyRead p k q cut z w hz hw left right a s b t f g‖ ≤
      legBound^2*vertexNorm q cut z w*‖f‖*‖g‖ := by
  apply (response_bound _ left right a s b t f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (full_vertex_norm p k q cut z w hz hw) (sq_nonneg _)) (norm_nonneg f))
    (norm_nonneg g)

theorem response_operator_difference (A B : HistorySpace →L[ℂ] HistorySpace)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) :
    response A left right a s b t f g-response B left right a s b t f g =
      response (A-B) left right a s b t f g := by
  simp only [response, sub_apply, inner_sub_right]

theorem timeRead_error (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) :
    ‖timeRead p k q cut z w hz hw T S left right a s b t f g-
      frequencyRead p k q cut z w hz hw left right a s b t f g‖ ≤
        legBound^2*CanonicalPhysicalCausalCharge.vertexTail q cut z w T S*‖f‖*‖g‖ := by
  change ‖response _ left right a s b t f g-response _ left right a s b t f g‖ ≤ _
  rw [response_operator_difference]
  apply (response_bound _ left right a s b t f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (CanonicalPhysicalCausalCharge.timeVertex_error p k q cut z w hz hw T S)
        (sq_nonneg _)) (norm_nonneg f)) (norm_nonneg g)

theorem frequencyRead_profile_error (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : Bool) (a s b t : Fin 2) (f f' g g' : Profile) :
    ‖frequencyRead p k q cut z w hz hw left right a s b t f g-
      frequencyRead p k q cut z w hz hw left right a s b t f' g'‖ ≤
        legBound^2*vertexNorm q cut z w*(‖f-f'‖*‖g‖+‖f'‖*‖g-g'‖) := by
  apply (response_error _ left right a s b t f f' g g').trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (full_vertex_norm p k q cut z w hz hw) (sq_nonneg _)) (by positivity)

theorem core_and_time_error (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ)
    (left right : Bool) (a s b t : Fin 2) (f g : Profile) (u v : GaussDensityCore.ScalarTest) :
    ‖timeRead p k q cut z w hz hw T S left right a s b t (core u) (core v)-
      frequencyRead p k q cut z w hz hw left right a s b t f g‖ ≤
    legBound^2*CanonicalPhysicalCausalCharge.vertexTail q cut z w T S*‖core u‖*‖core v‖+
      legBound^2*vertexNorm q cut z w*(‖core u-f‖*‖core v‖+‖f‖*‖core v-g‖) := by
  have identity : timeRead p k q cut z w hz hw T S left right a s b t (core u) (core v)-
      frequencyRead p k q cut z w hz hw left right a s b t f g =
    (timeRead p k q cut z w hz hw T S left right a s b t (core u) (core v)-
      frequencyRead p k q cut z w hz hw left right a s b t (core u) (core v))+
    (frequencyRead p k q cut z w hz hw left right a s b t (core u) (core v)-
      frequencyRead p k q cut z w hz hw left right a s b t f g) := by ring
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add
    (timeRead_error p k q cut z w hz hw T S left right a s b t (core u) (core v))
    (frequencyRead_profile_error p k q cut z w hz hw left right a s b t (core u) f (core v) g))

def finiteCoreTimeRead (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ) (T S : ℝ)
    (left right : Bool) (a s b t : Fin 2) (f g : GaussDensityCore.ScalarTest) (F : Index) : ℂ :=
  inner ℂ (GaussComposite.leg left a s (seedSection f))
    (CanonicalPhysicalCausalCharge.finiteTimeVertex p k q cut z w T S F
      (GaussComposite.leg right b t (seedSection g)))

theorem original_finite_time_word (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ) (T S : ℝ)
    (left right : Bool) (a s b t : Fin 2) (f g : GaussDensityCore.ScalarTest) (F : Index) :
    finiteCoreTimeRead p k q cut z w T S left right a s b t f g F =
      inner ℂ (GaussComposite.leg left a s (seedSection f))
        ((-(∫ u in (0 : ℝ)..T, ∫ v in (0 : ℝ)..S,
          CanonicalPhysicalLaplace.dampedTime (CanonicalPhysicalSpatial.compression (p+k) F+
            FullYSourceCutoffVolterra.cutoff cut) z u*chargeReader q*
          CanonicalPhysicalLaplace.dampedTime (CanonicalPhysicalSpatial.compression p F+
            FullYSourceCutoffVolterra.cutoff cut) w v)) (GaussComposite.leg right b t (seedSection g))) :=
  congrArg (fun A : H →L[ℂ] H => inner ℂ (GaussComposite.leg left a s (seedSection f))
    (A (GaussComposite.leg right b t (seedSection g))))
      (CanonicalPhysicalCausalCharge.original_time_word p k q cut z w T S F)

theorem same_occurrence_readback (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ)
    (left right : Bool) (a s b t : Fin 2) (f g : GaussDensityCore.ScalarTest) :
    Tendsto (finiteCoreTimeRead p k q cut z w T S left right a s b t f g) sourceFilter
      (𝓝 (timeRead p k q cut z w hz hw T S left right a s b t (core f) (core g))) := by
  rw [timeRead, response_core]
  change Tendsto _ _ (𝓝 (inner ℂ
    ((SourceFamilyHilbert.constant sourceFilter (GaussComposite.leg left a s (seedSection f))) : HistorySpace)
    (lift sourceFilter (CanonicalPhysicalCausalCharge.timeVertexFamily p k q cut z w hz hw T S)
      ((SourceFamilyHilbert.constant sourceFilter (GaussComposite.leg right b t (seedSection g))) : HistorySpace))))
  rw [lift_coe, inner_coe]
  exact pair_tendsto sourceFilter (SourceFamilyHilbert.constant sourceFilter (GaussComposite.leg left a s (seedSection f)))
    (act sourceFilter (CanonicalPhysicalCausalCharge.timeVertexFamily p k q cut z w hz hw T S)
      (SourceFamilyHilbert.constant sourceFilter (GaussComposite.leg right b t (seedSection g))))

theorem prepared_causal_limit (p k : PhysicalMomentum) (q : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : 0<z.im) (hw : 0<w.im) (left right : Bool) (a s b t : Fin 2) (f g : Profile) :
    Tendsto (fun ts : ℝ × ℝ => timeRead p k q cut z w (ne_of_gt hz) (ne_of_gt hw) ts.1 ts.2
      left right a s b t f g) (atTop ×ˢ atTop)
      (𝓝 (frequencyRead p k q cut z w (ne_of_gt hz) (ne_of_gt hw) left right a s b t f g)) := by
  have h := CanonicalPhysicalCausalCharge.independent_time_vertex_limit p k q cut z w hz hw
  exact (((continuous_const.inner (continuous_id.clm_apply continuous_const) :
    Continuous (fun A : HistorySpace →L[ℂ] HistorySpace =>
      inner ℂ (inclusion (completedLeg left a s f)) (A (inclusion (completedLeg right b t g))))).continuousAt).tendsto.comp h)

end LowEnergy.CanonicalPreparedFrequency
