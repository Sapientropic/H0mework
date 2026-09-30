import H0mework.Physics.Actual.FieldsRegularity
import H0mework.Physics.Cauchy.CanonicalCauchyState
import H0mework.Physics.Matter.ConjugateMatterVariation
import H0mework.Physics.Dirac.DiracMatterCoordinateCalculus

set_option autoImplicit false
open scoped ContDiff ENNReal

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fluid.CurrentReadout

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCanonicalCauchyState
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineDiracMatterCoordinateCalculus
open StageNineConjugateMatterVariation MeasureTheory Set

noncomputable section

local instance : Fintype MatterCoordinateIndex := Fintype.ofFinite _

def current (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (direction : Fin 4) (point : BasePoint) : ℝ :=
  (dual point (diracMatrixMatterAction (diracGamma direction) (matter point))).re

theorem current_contDiff
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (matterSmooth : ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (matter point)))
    (dualSmooth : ∀ index : MatterCoordinateIndex, ContDiff ℝ ∞ (fun point =>
      dual point (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))))
    (direction : Fin 4) : ContDiff ℝ ∞ (current matter dual direction) := by
  let gamma : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
    ((matterCoordinateEquiv.toLinearMap.comp
      ((diracMatrixMatterAction (diracGamma direction)).comp
        matterCoordinateEquiv.symm.toLinearMap)).toContinuousLinearMap).restrictScalars ℝ
  have gammaApply (value : DiracExteriorMatterCarrier) :
      gamma (matterCoordinateEquiv value) =
        matterCoordinateEquiv (diracMatrixMatterAction (diracGamma direction) value) := by
    change matterCoordinateEquiv
      (diracMatrixMatterAction (diracGamma direction)
        (matterCoordinateEquiv.symm (matterCoordinateEquiv value))) = _
    rw [matterCoordinateEquiv.symm_apply_apply]
  have gammaSmooth : ContDiff ℝ ∞ (fun point =>
      matterCoordinateEquiv (diracMatrixMatterAction (diracGamma direction) (matter point))) := by
    simpa only [Function.comp_def, gammaApply] using gamma.contDiff.comp matterSmooth
  have expression : current matter dual direction = fun point =>
      (∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (diracMatrixMatterAction (diracGamma direction) (matter point)) index *
          dual point (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))).re := by
    funext point
    unfold current
    conv_lhs => rw [← matterDualOfCoordinates_surjective (dual point), matterDualOfCoordinates_apply]
    rfl
  rw [expression]
  apply Complex.reCLM.contDiff.comp
  exact ContDiff.sum fun index _ => ((contDiff_piLp 2).mp gammaSmooth index).mul (dualSmooth index)

theorem compact_all_order_control
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (matterSmooth : ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (matter point)))
    (dualSmooth : ∀ index : MatterCoordinateIndex, ContDiff ℝ ∞ (fun point =>
      dual point (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))))
    (order : ℕ) {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ direction : Fin 4, ∀ point ∈ domain,
      ‖iteratedFDeriv ℝ order (current matter dual direction) point‖ ≤ bound := by
  let jets (point : BasePoint) : Fin 4 →
      ContinuousMultilinearMap ℝ (fun _ : Fin order => BasePoint) ℝ :=
    fun direction => iteratedFDeriv ℝ order (current matter dual direction) point
  have continuity : Continuous jets := continuous_pi fun direction =>
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
      (current_contDiff matter dual matterSmooth dualSmooth direction)
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuity.continuousOn
  exact ⟨bound, fun direction point inside =>
    (norm_le_pi_norm (jets point) direction).trans (bounded point inside)⟩

theorem compact_all_order_Lp
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier)
    (matterSmooth : ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (matter point)))
    (dualSmooth : ∀ index : MatterCoordinateIndex, ContDiff ℝ ∞ (fun point =>
      dual point (matterCoordinateEquiv.symm (EuclideanSpace.single index 1))))
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set BasePoint} (compact : IsCompact domain) :
    ∃ bound : ℝ, ∀ direction : Fin 4,
      MemLp (iteratedFDeriv ℝ order (current matter dual direction)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (current matter dual direction)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  obtain ⟨bound, bounded⟩ := compact_all_order_control matter dual matterSmooth dualSmooth order compact
  refine ⟨bound, fun direction => ?_⟩
  have continuity : Continuous (iteratedFDeriv ℝ order (current matter dual direction)) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
      (current_contDiff matter dual matterSmooth dualSmooth direction)
  have paid : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (current matter dual direction) point‖ ≤ bound := by
    filter_upwards [ae_restrict_mem compact.measurableSet] with point inside
    exact bounded direction point inside
  exact ⟨MemLp.of_bound continuity.aestronglyMeasurable bound paid,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) paid⟩

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fluid.CurrentReadout
