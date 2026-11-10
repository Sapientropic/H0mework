import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.JointOriginalResolventPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceMixed289ResponseOwn
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumFullFieldRiesz PreparationVacuumSourcePreparedResponse
open PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open ActualQuantitativePreparedFrameOwn ActualNativePreparedLegPriceOwn ActualSourceTensorPriceEnvelopeOwn
open scoped Topology InnerProductSpace BigOperators Matrix
attribute [local irreducible] mixedVertex jointResolvent jointCurrent jointHessian actualLeg actualFullY actualPrepared sourceProfile

def originalMixedResponsePrice (f g : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z w : ℂ) : ℝ :=
  (originalJointResolventPrice (p+k) F z * originalJointCurrentPrice f (p+k) F * originalJointResolventPrice (p+k) F z) *
    originalJointCurrentPrice g p F * originalJointResolventPrice p F w +
  (originalJointResolventPrice (p+k) F z * originalJointCurrentPrice g p F * originalJointResolventPrice p F w) *
    originalJointCurrentPrice f p F * originalJointResolventPrice p F w +
  originalJointResolventPrice (p+k) F z * originalJointCrossContactPrice f g p F * originalJointResolventPrice p F w

private theorem multiply_price (A B : H →L[ℂ] H) (a b : ℝ) (ha : ‖A‖ ≤ a) (hb : ‖B‖ ≤ b) : ‖A*B‖ ≤ a*b :=
  (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))

theorem originalMixedResponse_price (f g : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ‖mixedVertex f g p k F z w‖ ≤ originalMixedResponsePrice f g p k F z w := by
  have L := originalJointResolvent_price (p+k) F z hz
  have R := originalJointResolvent_price p F w hw
  have left := multiply_price _ _ _ _ (multiply_price _ _ _ _
    (triple_price _ _ _ _ _ _ L (originalJointCurrent_price f (p+k) F z) L)
    (originalJointCurrent_price g p F w)) R
  have right := multiply_price _ _ _ _ (multiply_price _ _ _ _
    (triple_price _ _ _ _ _ _ L (originalJointCurrent_price g p F w) R)
    (originalJointCurrent_price f p F w)) R
  have contact := triple_price _ _ _ _ _ _ L (originalJointHessian_price f g p F w) R
  unfold mixedVertex originalMixedResponsePrice
  exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add left right)) contact)

theorem originalPreparedMixed_price (epsilon : ℝ) (precision : 0 < epsilon) (f g : Field289)
    (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (left right : Bool) (a s b t : Fin 2) :
    ‖preparedMixed epsilon precision f g p k F z w left right a s b t‖ ≤
      1521 * originalMixedResponsePrice f g p k F z w := by
  simpa only [preparedMixed, actualLeg] using
    actual_pair_native_price epsilon precision _ _ (originalMixedResponse_price f g p k F z w hz hw) left right a s b t

-- Every entry is the paid derivative in one original field direction of the other original field current.
def actualMixed289Array (epsilon : ℝ) (precision : 0 < epsilon) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => preparedMixed epsilon precision (fieldUnit i) (fieldUnit j) p k F z w left right a s b t

theorem actualMixed289Array_generated (epsilon : ℝ) (precision : 0 < epsilon) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (left right : Bool) (a s b t : Fin 2) (i j : Fin 289) :
    HasDerivAt (fun r : ℝ => preparedVertex epsilon precision (fieldUnit j) p k F z w left right a s b t (r • fieldUnit i))
      (actualMixed289Array epsilon precision p k F z w left right a s b t i j) 0 :=
  preparedMixed_generated epsilon precision (fieldUnit i) (fieldUnit j) p k F z w hz hw left right a s b t

theorem actualMixed289Array_entry_price (epsilon : ℝ) (precision : 0 < epsilon) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (left right : Bool) (a s b t : Fin 2) (i j : Fin 289) :
    ‖actualMixed289Array epsilon precision p k F z w left right a s b t i j‖ ≤
      1521 * originalMixedResponsePrice (fieldUnit i) (fieldUnit j) p k F z w :=
  originalPreparedMixed_price epsilon precision (fieldUnit i) (fieldUnit j) p k F z w hz hw left right a s b t

def actualFullYMixed289Array (epsilon : ℝ) (precision : 0 < epsilon) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z w : ℂ) (left : Bool) (a s : Fin 2) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => inner ℂ (actualLeg epsilon precision left a s)
    (mixedVertex (fieldUnit i) (fieldUnit j) p k F z w (actualFullY epsilon precision))

def truncatedFullYMixed289Array (epsilon : ℝ) (precision : 0 < epsilon) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (bits : ℕ) (z w : ℂ) (left : Bool) (a s : Fin 2) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => inner ℂ (actualLeg epsilon precision left a s)
    (mixedVertex (fieldUnit i) (fieldUnit j) p k F z w
      (FullYSourceCutoffVolterra.cutoff (916 * bits) (actualPrepared epsilon precision)))

theorem actualFullYMixed289Array_entry_binary_error (epsilon : ℝ) (precision : 0 < epsilon)
    (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (bits : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (left : Bool) (a s : Fin 2) (i j : Fin 289) :
    ‖actualFullYMixed289Array epsilon precision p k F z w left a s i j -
      truncatedFullYMixed289Array epsilon precision p k F bits z w left a s i j‖ ≤
      60016320 * originalMixedResponsePrice (fieldUnit i) (fieldUnit j) p k F z w * (1 / 2 : ℝ) ^ bits := by
  unfold actualFullYMixed289Array truncatedFullYMixed289Array
  rw [← inner_sub_right, ← map_sub]
  have price := originalMixedResponse_price (fieldUnit i) (fieldUnit j) p k F z w hz hw
  have nonneg := (norm_nonneg _).trans price
  calc
    _ ≤ ‖actualLeg epsilon precision left a s‖ * originalMixedResponsePrice (fieldUnit i) (fieldUnit j) p k F z w *
        ‖actualFullY epsilon precision - FullYSourceCutoffVolterra.cutoff (916 * bits) (actualPrepared epsilon precision)‖ :=
      vertex_pair_price _ _ price _ _
    _ ≤ 39 * originalMixedResponsePrice (fieldUnit i) (fieldUnit j) p k F z w * (1538880 * (1 / 2 : ℝ) ^ bits) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (actualLeg_native_price epsilon precision left a s) nonneg)
        (actual_fullY_numerical_binary_error epsilon precision bits) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end LowEnergy.ActualSourceMixed289ResponseOwn
