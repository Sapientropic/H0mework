import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPhysicalLaplace
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPhysicalWard

/-! Both charge-vertex legs are literal causal integrals on the same finite
source occurrence. Independent time cutoffs converge with a source bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPhysicalCausalCharge
open GaussCoreHilbert CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open CanonicalPhysicalLaplace CanonicalPhysicalYResolvent
open CanonicalGradedCharge (chargeReader)
open SourceQuantumScalarChart (NativeLie)
open SourceFamilyOperator Filter MeasureTheory
open GaussUnitaryHistory (Index sourceFilter HistorySpace reader)
open scoped Topology InnerProductSpace Interval

section Algebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem time_word_integral (Co Ci Q : E →L[ℂ] E) (z w : ℂ) (T S : ℝ) :
    causalIntegral Co z T*Q*causalIntegral Ci w S =
      -(∫ t in (0 : ℝ)..T, ∫ s in (0 : ℝ)..S, dampedTime Co z t*Q*dampedTime Ci w s) := by
  have hf := (dampedTime_continuous Co z).intervalIntegrable (μ := volume) 0 T
  have hg := (dampedTime_continuous Ci w).intervalIntegrable (μ := volume) 0 S
  have inner (t : ℝ) : (∫ s in (0 : ℝ)..S, dampedTime Co z t*Q*dampedTime Ci w s) =
      (dampedTime Co z t*Q)*(∫ s in (0 : ℝ)..S, dampedTime Ci w s) :=
    ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)) (dampedTime Co z t*Q)).intervalIntegral_comp_comm hg
  have outer : (∫ t in (0 : ℝ)..T, ∫ s in (0 : ℝ)..S, dampedTime Co z t*Q*dampedTime Ci w s) =
      (∫ t in (0 : ℝ)..T, dampedTime Co z t)*Q*(∫ s in (0 : ℝ)..S, dampedTime Ci w s) := by
    simp_rw [inner, mul_assoc]
    exact ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip
      (Q*(∫ s in (0 : ℝ)..S, dampedTime Ci w s))).intervalIntegral_comp_comm hf
  rw [outer]
  simp only [causalIntegral, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]

private theorem product_error (A B R S Q : E →L[ℂ] E) (a b r s q : ℝ)
    (ha : ‖A-R‖ ≤ a) (hb : ‖B-S‖ ≤ b) (hr : ‖R‖ ≤ r) (hs : ‖S‖ ≤ s) (hq : ‖Q‖ ≤ q) :
    ‖A*Q*B-R*Q*S‖ ≤ a*q*(s+b)+r*q*b := by
  have an : 0 ≤ a := (norm_nonneg _).trans ha
  have rn : 0 ≤ r := (norm_nonneg _).trans hr
  have qn : 0 ≤ q := (norm_nonneg _).trans hq
  have nb : ‖B‖ ≤ s+b := by
    have identity : B=S+(B-S) := by abel
    exact (congrArg norm identity).trans_le ((norm_add_le _ _).trans (add_le_add hs hb))
  have first : ‖(A-R)*Q*B‖ ≤ a*q*(s+b) := by
    exact (norm_mul_le _ _).trans
      (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul ha hq (norm_nonneg _) an)) nb
        (norm_nonneg _) (mul_nonneg an qn))
  have second : ‖R*Q*(B-S)‖ ≤ r*q*b := by
    exact (norm_mul_le _ _).trans
      (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hr hq (norm_nonneg _) rn)) hb
        (norm_nonneg _) (mul_nonneg rn qn))
  have identity : A*Q*B-R*Q*S=(A-R)*Q*B+R*Q*(B-S) := by noncomm_ring
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add first second)

end Algebra

def finiteTimeVertex (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ) (T S : ℝ)
    (F : Index) : H →L[ℂ] H := finiteCausal (p+k) cut z T F*chargeReader a*finiteCausal p cut w S F

theorem original_time_word (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ) (T S : ℝ)
    (F : Index) : finiteTimeVertex p k a cut z w T S F =
      -(∫ t in (0 : ℝ)..T, ∫ s in (0 : ℝ)..S,
        dampedTime (compression (p+k) F+FullYSourceCutoffVolterra.cutoff cut) z t*chargeReader a*
          dampedTime (compression p F+FullYSourceCutoffVolterra.cutoff cut) w s) :=
  time_word_integral _ _ _ z w T S

def timeVertexFamily (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ) : Operator Index H :=
  comp (comp (causalFamily (p+k) cut z hz T) (constant (chargeReader a))) (causalFamily p cut w hw S)

theorem timeVertexFamily_original (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ) (F : Index) :
    (timeVertexFamily p k a cut z w hz hw T S).component F=finiteTimeVertex p k a cut z w T S F := rfl

def timeVertex (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (timeVertexFamily p k a cut z w hz hw T S)

theorem timeVertex_return (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ) :
    timeVertex p k a cut z w hz hw T S=causal (p+k) cut z hz T*reader (chargeReader a)*causal p cut w hw S := by
  simp only [timeVertex, timeVertexFamily, lift_comp]
  rfl

def vertexTail (a : NativeLie) (cut : ℕ) (z w : ℂ) (T S : ℝ) : ℝ :=
  tailBound cut z T*‖chargeReader a‖*(normBound cut w+tailBound cut w S)+
    normBound cut z*‖chargeReader a‖*tailBound cut w S

theorem timeVertex_error (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (T S : ℝ) :
    ‖timeVertex p k a cut z w hz hw T S-CanonicalPhysicalWard.vertex p k a cut z w hz hw‖ ≤ vertexTail a cut z w T S := by
  have hzbound : ‖fullResolvent (p+k) cut z hz‖ ≤ normBound cut z :=
    ContinuousLinearMap.opNorm_le_bound _ (normBound_nonneg cut z) (fullResolvent_bound (p+k) cut z hz)
  have hwbound : ‖fullResolvent p cut w hw‖ ≤ normBound cut w :=
    ContinuousLinearMap.opNorm_le_bound _ (normBound_nonneg cut w) (fullResolvent_bound p cut w hw)
  have hqbound : ‖reader (chargeReader a)‖ ≤ ‖chargeReader a‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (CanonicalPhysicalWard.charge_bound a)
  rw [timeVertex_return, CanonicalPhysicalWard.vertex_return]
  exact product_error _ _ _ _ _ _ _ _ _ _
    (completed_norm_error (p+k) cut z hz T) (completed_norm_error p cut w hw S) hzbound hwbound hqbound

theorem independent_time_vertex_limit (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (z w : ℂ)
    (hz : 0<z.im) (hw : 0<w.im) :
    Tendsto (fun ts : ℝ × ℝ => timeVertex p k a cut z w (ne_of_gt hz) (ne_of_gt hw) ts.1 ts.2)
      (atTop ×ˢ atTop) (𝓝 (CanonicalPhysicalWard.vertex p k a cut z w (ne_of_gt hz) (ne_of_gt hw))) := by
  have hout := (causal_to_fullResolvent (p+k) cut z hz).comp (show Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ atTop) atTop from tendsto_fst)
  have hin := (causal_to_fullResolvent p cut w hw).comp (show Tendsto (Prod.snd : ℝ × ℝ → ℝ) (atTop ×ˢ atTop) atTop from tendsto_snd)
  have both := (hout.mul_const (reader (chargeReader a))).mul hin
  simpa only [timeVertex_return, CanonicalPhysicalWard.vertex_return, Function.comp_def] using! both

end LowEnergy.CanonicalPhysicalCausalCharge
