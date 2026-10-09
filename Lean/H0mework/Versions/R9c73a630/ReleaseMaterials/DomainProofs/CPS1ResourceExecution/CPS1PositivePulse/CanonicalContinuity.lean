import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Normed
import Mathlib.Analysis.InnerProductSpace.Continuous

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1PositivePulse
noncomputable section
open InnerProductSpace
open scoped BigOperators Topology
open CPS1MolecularFrame.FiniteNormed

variable {𝕜 E ι X : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype ι] [TopologicalSpace X]

theorem ordered_independent (raw : ι → E) (independent : LinearIndependent 𝕜 raw) :
    LinearIndependent 𝕜 (ordered raw) :=
  independent.comp (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm.injective

theorem canonical_gs_step (raw : ι → E) (current : Fin (Fintype.card ι)) :
    gramSchmidt 𝕜 (ordered raw) current = ordered raw current -
      ∑ previous : Finset.Iio current,
        projectionRatio (𝕜 := 𝕜) raw previous.val current •
          gramSchmidt 𝕜 (ordered raw) previous.val := by
  classical
  apply (eq_sub_iff_add_eq).mpr
  have recurrence := (gramSchmidt_def'' 𝕜 (ordered raw) current).symm
  rw [← Finset.sum_attach,Finset.attach_eq_univ] at recurrence
  exact recurrence

theorem canonical_gs_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint)) (current : Fin (Fintype.card ι)) :
    ContinuousAt (fun point => gramSchmidt 𝕜 (ordered (raw point)) current) currentPoint := by
  classical
  have orderedContinuous (index : Fin (Fintype.card ι)) :
      ContinuousAt (fun point => ordered (raw point) index) currentPoint :=
    continuous ((Fintype.equivFin ι).symm index)
  have orderedIndependent := ordered_independent (raw currentPoint) independent
  apply wellFounded_lt.induction current
  intro current previous
  have ratioContinuous (prior : Finset.Iio current) :
      ContinuousAt (fun point => projectionRatio (𝕜 := 𝕜) (raw point) prior.val current) currentPoint := by
    have gsContinuous := previous prior.val (Finset.mem_Iio.mp prior.property)
    have normContinuous : ContinuousAt (fun point =>
        (‖gramSchmidt 𝕜 (ordered (raw point)) prior.val‖ : 𝕜) ^ 2) currentPoint :=
      (RCLike.continuous_ofReal.continuousAt.comp gsContinuous.norm).pow 2
    exact (gsContinuous.inner (orderedContinuous current)).div normContinuous
      (pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero prior.val orderedIndependent))))
  have sumContinuous : ContinuousAt (fun point =>
      ∑ prior : Finset.Iio current,
        projectionRatio (𝕜 := 𝕜) (raw point) prior.val current •
          gramSchmidt 𝕜 (ordered (raw point)) prior.val) currentPoint :=
    tendsto_finsetSum Finset.univ fun prior _ =>
      (ratioContinuous prior).smul (previous prior.val (Finset.mem_Iio.mp prior.property))
  have result := (orderedContinuous current).sub sumContinuous
  change ContinuousAt (fun point => ordered (raw point) current -
    ∑ prior : Finset.Iio current,
      projectionRatio (𝕜 := 𝕜) (raw point) prior.val current •
        gramSchmidt 𝕜 (ordered (raw point)) prior.val) currentPoint at result
  simpa only [← canonical_gs_step] using result

theorem projection_ratio_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint))
    (previous current : Fin (Fintype.card ι)) :
    ContinuousAt (fun point => projectionRatio (𝕜 := 𝕜) (raw point) previous current) currentPoint := by
  have gsContinuous := canonical_gs_continuousAt raw currentPoint continuous independent previous
  have orderedContinuous : ContinuousAt (fun point => ordered (raw point) current) currentPoint :=
    continuous ((Fintype.equivFin ι).symm current)
  exact (gsContinuous.inner orderedContinuous).div
    ((RCLike.continuous_ofReal.continuousAt.comp gsContinuous.norm).pow 2)
    (pow_ne_zero 2 (RCLike.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero previous
        (ordered_independent (raw currentPoint) independent)))))

theorem canonical_coefficients_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint))
    (current source : Fin (Fintype.card ι)) :
    ContinuousAt (fun point => gsCoefficients (𝕜 := 𝕜) (raw point) current source) currentPoint := by
  classical
  apply wellFounded_lt.induction current
  intro current previous
  have sumContinuous : ContinuousAt (fun point =>
      ∑ prior : Finset.Iio current,
        projectionRatio (𝕜 := 𝕜) (raw point) prior.val current *
          gsCoefficients (𝕜 := 𝕜) (raw point) prior.val source) currentPoint :=
    tendsto_finsetSum Finset.univ fun prior _ =>
      (projection_ratio_continuousAt raw currentPoint continuous independent prior.val current).mul
        (previous prior.val (Finset.mem_Iio.mp prior.property))
  have result := (continuousAt_const (y := if source = current then (1 : 𝕜) else 0)).sub sumContinuous
  change ContinuousAt (fun point => (if source = current then (1 : 𝕜) else 0) -
    ∑ prior : Finset.Iio current,
      projectionRatio (𝕜 := 𝕜) (raw point) prior.val current *
        gsCoefficients (𝕜 := 𝕜) (raw point) prior.val source) currentPoint at result
  simpa only [← gs_coefficients_step] using result

theorem canonical_normed_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint)) (current : Fin (Fintype.card ι)) :
    ContinuousAt (fun point => gramSchmidtNormed 𝕜 (ordered (raw point)) current) currentPoint := by
  have gsContinuous := canonical_gs_continuousAt raw currentPoint continuous independent current
  have normNonzero : (‖gramSchmidt 𝕜 (ordered (raw currentPoint)) current‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (gramSchmidt_ne_zero current (ordered_independent (raw currentPoint) independent)))
  exact ((RCLike.continuous_ofReal.continuousAt.comp gsContinuous.norm).inv₀ normNonzero).smul
    gsContinuous

theorem canonical_normalized_coefficients_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint)) (current : Fin (Fintype.card ι)) (source : ι) :
    ContinuousAt (fun point =>
      (‖gramSchmidt 𝕜 (ordered (raw point)) current‖ : 𝕜)⁻¹ *
        gsCoefficients (𝕜 := 𝕜) (raw point) current (Fintype.equivFin ι source)) currentPoint := by
  have gsContinuous := canonical_gs_continuousAt raw currentPoint continuous independent current
  have normNonzero : (‖gramSchmidt 𝕜 (ordered (raw currentPoint)) current‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (gramSchmidt_ne_zero current (ordered_independent (raw currentPoint) independent)))
  exact ((RCLike.continuous_ofReal.continuousAt.comp gsContinuous.norm).inv₀ normNonzero).mul
    (canonical_coefficients_continuousAt raw currentPoint continuous independent current
      (Fintype.equivFin ι source))

def totalNormalization (raw : ι → E) : Matrix ι ι 𝕜 :=
  fun source slot =>
    (‖gramSchmidt 𝕜 (ordered raw) (Fintype.equivFin ι slot)‖ : 𝕜)⁻¹ *
      gsCoefficients (𝕜 := 𝕜) raw (Fintype.equivFin ι slot) (Fintype.equivFin ι source)

theorem total_normalization_continuousAt (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint)) :
    ContinuousAt (fun point => totalNormalization (𝕜 := 𝕜) (raw point)) currentPoint := by
  apply continuousAt_pi.mpr
  intro source
  apply continuousAt_pi.mpr
  intro slot
  exact canonical_normalized_coefficients_continuousAt raw currentPoint continuous independent
    (Fintype.equivFin ι slot) source

theorem canonical_eventually_full_rank (raw : X → ι → E) (currentPoint : X)
    (continuous : ∀ index, ContinuousAt (fun point => raw point index) currentPoint)
    (independent : LinearIndependent 𝕜 (raw currentPoint)) :
    ∀ᶠ point in 𝓝 currentPoint, rank (𝕜 := 𝕜) (raw point) = Fintype.card ι := by
  have nonzero (index : Fin (Fintype.card ι)) :
      gramSchmidtNormed 𝕜 (ordered (raw currentPoint)) index ≠ 0 := by
    have unit := gramSchmidtNormed_unit_length index (ordered_independent (raw currentPoint) independent)
    intro zero
    rw [zero,norm_zero] at unit
    exact zero_ne_one unit
  have eventuallyNonzero : ∀ᶠ point in 𝓝 currentPoint,
      ∀ index : Fin (Fintype.card ι), gramSchmidtNormed 𝕜 (ordered (raw point)) index ≠ 0 :=
    Filter.eventually_all.mpr fun index =>
      (canonical_normed_continuousAt raw currentPoint continuous independent index).eventually_ne
        (nonzero index)
  filter_upwards [eventuallyNonzero] with point allNonzero
  apply Nat.le_antisymm (rank_le_source_card (𝕜 := 𝕜) (raw point))
  have injective : Function.Injective (fun index : Fin (Fintype.card ι) =>
      (⟨index,allNonzero index⟩ : Index (𝕜 := 𝕜) (raw point))) := by
    intro first second same
    exact congrArg Subtype.val same
  simpa only [Fintype.card_fin,rank] using Fintype.card_le_of_injective _ injective

end
end CPS1PositivePulse
