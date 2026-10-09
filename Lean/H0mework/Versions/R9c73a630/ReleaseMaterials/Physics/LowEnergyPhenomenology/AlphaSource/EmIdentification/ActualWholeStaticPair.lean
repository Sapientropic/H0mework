import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeStaticUniform

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualWholeStatic
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumStaticPoleResponse ActualMasslessCurrent
open PreparationPhysicalStaticSpatialCouplingReturn
open ActualEMCarrierOwn ActualEMCurrentSplit ActualEMResponseSplit ActualEMObservable
open ActualElectronOwnerTest ActualMasslessStaticPair
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] emUnitSourceCurrent actualElectronFieldTest
  sourceGreen actualUnitMasslessWeight wholeStaticLimit

/-- The exact original detector, with its single hc, on the complete original source current. -/
def actualWholeMatrixRead (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) : WholeMatrix →L[ℝ] ℂ :=
  (actualElectronFieldTest branch qd dL dR lambda T).restrictScalars ℝ |>.comp
    ({toFun := fun M => M *ᵥ emUnitSourceCurrent qs sL sR mu S
      map_add' := fun M N => Matrix.add_mulVec _ _ _
      map_smul' := fun r M => by simp only [Matrix.smul_mulVec, RingHom.id_apply]} :
      WholeMatrix →ₗ[ℝ] (Fin 289 → ℂ)).toContinuousLinearMap

attribute [local irreducible] actualWholeMatrixRead

theorem actual_whole_matrix_read_original (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) (M : WholeMatrix) :
    actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S M =
      emCurrentObservation M (emUnitDetectorCovector branch qd dL dR lambda T)
        (emUnitSourceCurrent qs sL sR mu S) := by
  unfold actualWholeMatrixRead
  change actualElectronFieldTest branch qd dL dR lambda T
    (M *ᵥ emUnitSourceCurrent qs sL sR mu S) = _
  exact (em_unit_detector_actual branch qd dL dR lambda T _).symm

theorem actual_whole_matrix_read_origin (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) :
    actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S wholeStaticLimit =
      actualStaticPairSeed * actualUnitMasslessWeight qd dL dR lambda T *
        actualUnitMasslessWeight qs sL sR mu S /
        ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ) := by
  unfold actualWholeMatrixRead
  change actualElectronFieldTest branch qd dL dR lambda T
    (wholeStaticLimit *ᵥ emUnitSourceCurrent qs sL sR mu S) = _
  rw [whole_static_limit_actual_field, map_neg, actual_unit_static_observable]
  ring

/-- The actual rest-prepared full-current coefficient has one radius over every physical direction. -/
theorem actual_unit_whole_green_uniform (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n = 1,
        ‖(r.val : ℂ)^2 * emCurrentObservation
          (sourceGreen (sourceSpatialStaticRegularPoint n unit r))
          (emUnitDetectorCovector branch qd dL dR lambda T)
          (emUnitSourceCurrent qs sL sR mu S) -
            actualStaticPairSeed * actualUnitMasslessWeight qd dL dR lambda T *
              actualUnitMasslessWeight qs sL sR mu S /
              ((ActionNormalization.phaseMomentum * sourceSpeed branch : ℝ) : ℂ)‖ ≤ epsilon := by
  let L := actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S
  let price := 1 + ‖L‖
  have pp : 0 < price := by dsimp only [price]; positivity
  have ep : 0 < epsilon / price := div_pos positive pp
  obtain ⟨radius, rp, paid⟩ := whole_static_green_uniform (epsilon / price) ep
  refine ⟨radius, rp, ?_⟩
  intro r small n unit
  have total : ‖L ((r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)) -
      L wholeStaticLimit‖ ≤ epsilon := by
    rw [←map_sub]
    calc
      _ ≤ ‖L‖ * ‖(r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r) -
        wholeStaticLimit‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (epsilon / price) := mul_le_mul_of_nonneg_left (paid r small n unit) (norm_nonneg _)
      _ ≤ price * (epsilon / price) := mul_le_mul_of_nonneg_right
        (by dsimp only [price]; linarith [norm_nonneg L]) ep.le
      _ = epsilon := by field_simp
  dsimp only [L] at total
  rw [actual_whole_matrix_read_origin] at total
  simpa only [map_smul, actual_whole_matrix_read_original,
    Complex.real_smul, Complex.ofReal_pow, smul_eq_mul] using total

def actualWholeStaticBudget (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) : ℝ :=
  ‖actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S‖ * wholeStaticBudget

theorem actual_unit_whole_green_domination (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ r : staticDomain, r.val < radius →
      ∀ n : PhysicalMomentum, ∀ unit : spatialSquare n = 1,
        ‖(r.val : ℂ)^2 * emCurrentObservation
          (sourceGreen (sourceSpatialStaticRegularPoint n unit r))
          (emUnitDetectorCovector branch qd dL dR lambda T)
          (emUnitSourceCurrent qs sL sR mu S)‖ ≤
            actualWholeStaticBudget branch qd qs dL dR sL sR lambda mu T S := by
  let L := actualWholeMatrixRead branch qd qs dL dR sL sR lambda mu T S
  obtain ⟨radius, rp, paid⟩ := whole_static_green_domination
  refine ⟨radius, rp, ?_⟩
  intro r small n unit
  have total : ‖L ((r.val^2 : ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))‖ ≤
      ‖L‖ * wholeStaticBudget :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (paid r small n unit) (norm_nonneg _))
  simpa only [L, map_smul, actual_whole_matrix_read_original,
    Complex.real_smul, Complex.ofReal_pow, smul_eq_mul, actualWholeStaticBudget] using total

end LowEnergy.GaussComposite.ActualWholeStatic
