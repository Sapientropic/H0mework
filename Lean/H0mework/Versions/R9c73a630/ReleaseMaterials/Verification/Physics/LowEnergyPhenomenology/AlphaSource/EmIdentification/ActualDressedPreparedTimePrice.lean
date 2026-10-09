import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldTime
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberBackground

set_option autoImplicit false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPreparedPrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse ActualDressedNumberSector ActualDressedNumberZero
open ActualDressedNumberField ActualDressedSourcePreparation FullYSourceCutoffVolterra
open scoped Topology BigOperators Interval
attribute [local irreducible] numberTwoProjection actualC actualA physicalTime sourceDressedUnit
  SourceGraph.prepared

def occupationPrice (n : ℕ) (a T : ℝ) : ℝ :=
  ∑ j  ∈  Finset.range (n+1), (T*a)^j

theorem occupationPrice_nonneg (n : ℕ) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    0 ≤ occupationPrice n a T := by
  unfold occupationPrice
  exact Finset.sum_nonneg (fun j _ => pow_nonneg (mul_nonneg hT ha) j)

theorem occupationPrice_mono (n : ℕ) (a s T : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) (st : s ≤ T) :
    occupationPrice n a s ≤ occupationPrice n a T := by
  unfold occupationPrice
  exact Finset.sum_le_sum (fun j _  =>  pow_le_pow_left₀ (mul_nonneg hs ha)
    (mul_le_mul_of_nonneg_right st ha) j)

theorem actual_time_N2_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (v : H) (sector : numberTwoProjection v=v) :
    physicalTime p F t 0 v=partialEvolution (actualC p F) (actualA p F) 2 t v := by
  have source:=congrArg (fun A : H→L[ℂ]H => A v) (actual_time_N2_projection_return p F t)
  simpa only [mul_apply_eq_comp,sector] using source

theorem actual_time_N2_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (v : H) (sector : numberTwoProjection v=v) :
    ‖physicalTime p F t 0 v‖ ≤ occupationPrice 2 ‖actualA p F‖ |t| *‖v‖ := by
  rw [actual_time_N2_return p F t v sector]
  exact ((partialEvolution (actualC p F) (actualA p F) 2 t).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (partialEvolution_bound _ _ (actualC_symmetric p F) 2 t) (norm_nonneg v))

theorem actual_created_time_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t epsilon : ℝ) (precision : 0<epsilon) :
    ‖physicalTime p F t 0 (sourceDressedUnit epsilon precision)‖ ≤ occupationPrice 2 ‖actualA p F‖ |t| := by
  simpa only [source_dressed_unit_norm,mul_one] using actual_time_N2_price p F t
    (sourceDressedUnit epsilon precision) (actual_created_unit_N2 epsilon precision)

theorem actual_background_time_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (profile : SourceGraph.Profile) :
    ‖physicalTime p F t 0 (SourceGraph.prepared profile)‖ ≤
      occupationPrice 1 ‖actualA p F‖ |t| *‖SourceGraph.prepared profile‖ := by
  rw [actual_time_background]
  exact ((partialEvolution (actualC p F) (actualA p F) 1 t).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (partialEvolution_bound _ _ (actualC_symmetric p F) 1 t) (norm_nonneg _))

end LowEnergy.GaussComposite.ActualDressedPreparedPrice
