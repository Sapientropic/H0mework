import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumFieldWindowPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedJointNoetherSourcePrice
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumGradedTransport PreparationVacuumYukawaTransport
open PreparationVacuumUncutYukawa PreparationVacuumFullPoleContinuation PreparationVacuumActionFieldLift
open PreparationVacuumNoetherChart
open PreparationVacuumPhysicalHalfAxis PreparationVacuumSourcePreparedResponse
open PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedSylvester ActualDressedLeftFreeJet ActualDressedCubicPrice
open ActualDressedUniformMaterialCoefficients ActualDressedNumberField SourceGraph
open ActualSourcePreparedNoetherPi ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedQuantumNoetherPrice ActualSourcePreparedQuantumFieldWindowPrice
open LowEnergy.ActualMixedNoetherTimePriceOwn LowEnergy.ActualQuantitativePreparedFrameOwn
open LowEnergy.ActualSourceMixed289ResponseOwn
open ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualSourcePreparedQuantumDriverCofactor ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedN3EMChargeRead ActualSourcePreparedN3MovingResponse
open PreparationVacuumStaticPoleResponse PreparationVacuumMixedPrincipal
open PreparationPhysicalStaticSpatialCouplingReturn PreparationVacuumFullOriginResponse
open scoped Matrix BigOperators Matrix.Norms.Operator
attribute [local irreducible] jointCurrent jointResolvent noetherReader noetherReaderContact freeCompressionCurrent
  jointCResolvent actualA completeCubicNoetherPrice prepared sourceProfile actualPrepared

private theorem free_source (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    freeCompressionCurrent p F force = jointCurrent p F 0 0 force-uncutSlope force (finiteRetainer p F) := by
  have free : freeCompressionCurrent p F force = transportedCurrent force p F 0 :=
    ((free_compression_direction p F force).congr_of_eventuallyEq (jointCompression_ray force p F).symm).unique
      (transportedCompression_first force p F)
  rw [jointCurrent_source]
  unfold sourceCurrent sourceYJet uncutJetOperator
  change freeCompressionCurrent p F force =
    (transportedCurrent force p F 0+uncutSlope force (finiteRetainer p F))-uncutSlope force (finiteRetainer p F)
  rw [add_sub_cancel_right]
  exact free

private theorem shift_price {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u v k : E) (eps B : ℝ) (update : v=u-((eps^2:ℝ):ℂ) • k) (price : ‖u‖ ≤ B) :
    ‖v‖ ≤ B+eps^2*‖k‖ := by
  rw [update]
  have bound := norm_sub_le u (((eps^2:ℝ):ℂ) • k)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg eps)] at bound
  exact bound.trans (add_le_add price le_rfl)

/-- The same uncut retainer cancels from the actual free-current momentum
increment; this prices the current itself, not a presumed price-function ratio. -/
theorem source_moving_free_current_price (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (force : Field289) :
    ‖freeCompressionCurrent (event.momentum-eps^2 • n) event.frame force‖ ≤
      originalFreeCurrentPrice force event.momentum event.frame+
        eps^2*‖jointCurrent n event.frame 0 0 force-jointCurrent 0 event.frame 0 0 force‖ := by
  have affine := actual_moving_current_affine event.momentum n event.frame 0 (eps^2) force
  have retainer := congrArg (fun R => uncutSlope force R)
    (sourceRetainer_momentum (event.momentum-eps^2 • n) event.momentum event.frame)
  have moved := congrArg₂ (fun A B : H →L[ℂ] H => A-B) affine retainer
  have grouped :
      (jointCurrent event.momentum event.frame 0 0 force-
        ((eps^2:ℝ):ℂ) • (jointCurrent n event.frame 0 0 force-jointCurrent 0 event.frame 0 0 force))-
          uncutSlope force (finiteRetainer event.momentum event.frame) =
      (jointCurrent event.momentum event.frame 0 0 force-uncutSlope force (finiteRetainer event.momentum event.frame))-
        ((eps^2:ℝ):ℂ) • (jointCurrent n event.frame 0 0 force-jointCurrent 0 event.frame 0 0 force) := by abel
  have base := congrArg (fun A : H →L[ℂ] H => A-
    ((eps^2:ℝ):ℂ) • (jointCurrent n event.frame 0 0 force-jointCurrent 0 event.frame 0 0 force))
      (free_source force event.momentum event.frame).symm
  have actual := (free_source force (event.momentum-eps^2 • n) event.frame).trans
    ((moved.trans grouped).trans base)
  exact shift_price _ _ _ eps _ actual (originalFreeCurrent_price force event.momentum event.frame)

private def cubicCore (cp b c d contact jg jt a : ℝ) : ℝ :=
  (cp*b*c*d+b^2*cp*c*d+b*contact*d+b*c*(d^2*jg))*(1+a)^2+b*c*d*(3*jt*(1+a)^2)

private theorem cubic_mono (cp b c d contact jg jt a CP B C D CONTACT JG JT A : ℝ)
    (p0 : 0 ≤ cp) (b0 : 0 ≤ b) (c0 : 0 ≤ c) (d0 : 0 ≤ d)
    (e0 : 0 ≤ contact) (j0 : 0 ≤ jg) (k0 : 0 ≤ jt) (a0 : 0 ≤ a)
    (p1 : cp ≤ CP) (b1 : b ≤ B) (c1 : c ≤ C) (d1 : d ≤ D)
    (e1 : contact ≤ CONTACT) (j1 : jg ≤ JG) (k1 : jt ≤ JT) (a1 : a ≤ A) :
    cubicCore cp b c d contact jg jt a ≤ cubicCore CP B C D CONTACT JG JT A := by
  have CP0 := p0.trans p1
  have B0 := b0.trans b1
  have C0 := c0.trans c1
  have D0 := d0.trans d1
  have E0 := e0.trans e1
  have J0 := j0.trans j1
  have K0 := k0.trans k1
  have A0 := a0.trans a1
  unfold cubicCore
  gcongr

def sourceJointCubicNoetherPrice (event : DressedEvent) (n : PhysicalMomentum) (radius : ℝ)
    (reader force : Field289) : ℝ :=
  2*cubicCore (originalFreeCurrentPrice force event.momentum event.frame+
      radius*‖jointCurrent n event.frame 0 0 force-jointCurrent 0 event.frame 0 0 force‖)
    (1/|event.energy.im|) (originalNoetherReaderPrice reader event.momentum event.frame)
    (originalJointResolventPrice event.momentum event.frame event.energy)
    (originalNoetherContactPrice reader force event.momentum event.frame)
    (originalJointCurrentPrice force event.momentum event.frame)
    (originalJointCurrentPrice force event.momentum event.frame)
    (originalCompactYPrice 0 event.momentum event.frame 0)

private theorem complete_formula (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289) :
    completeCubicNoetherPrice event transfer reader force =
      2*cubicCore ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖
        ‖noetherReader reader event.momentum event.frame 0‖
        ‖jointResolvent event.momentum event.frame event.energy 0‖
        ‖noetherReaderContact reader force event.momentum event.frame‖
        ‖jointCurrent event.momentum event.frame event.energy 0 force‖
        ‖jointCurrent event.momentum event.frame 0 0 force‖ ‖actualA event.momentum event.frame‖ := by
  have background : ‖prepared (sourceProfile event.epsilon event.precision)‖ = 1 := by
    simpa only [actualPrepared] using actualPrepared_norm event.epsilon event.precision
  unfold completeCubicNoetherPrice
  change cubicCore _ _ _ _ _ _ _ _*(1+‖prepared (sourceProfile event.epsilon event.precision)‖^2) = _
  rw [background]
  ring

/-- A common source radius pays all moving epsilon values in one complete
five-arm Noether price. No caller bound on a finished response is accepted. -/
theorem source_joint_complete_noether_price (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (radius : ℝ) (inside : eps^2 ≤ radius) (reader force : Field289) :
    completeCubicNoetherPrice event (eps^2 • n) reader force ≤
      sourceJointCubicNoetherPrice event n radius reader force := by
  rw [complete_formula]
  unfold sourceJointCubicNoetherPrice
  have cp := (source_moving_free_current_price event eps n force).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right inside (norm_nonneg _)))
  have b := originalFreeResolvent_price (event.momentum-eps^2 • n) event.frame event.energy event.nonreal
  have c := originalNoetherReader_price reader event.momentum event.frame
  have d := originalJointResolvent_price event.momentum event.frame event.energy event.nonreal
  have contact := originalNoetherContact_price reader force event.momentum event.frame
  have jg := originalJointCurrent_price force event.momentum event.frame event.energy
  have jt := originalJointCurrent_price force event.momentum event.frame 0
  have a : ‖actualA event.momentum event.frame‖ ≤ originalCompactYPrice 0 event.momentum event.frame 0 := by
    simpa only [actualA] using originalCompactY_price 0 event.momentum event.frame 0
  exact mul_le_mul_of_nonneg_left
    (cubic_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (norm_nonneg (freeCompressionCurrent (event.momentum-eps^2 • n) event.frame force))
      (norm_nonneg (jointCResolvent (event.momentum-eps^2 • n) event.frame event.energy 0))
      (norm_nonneg (noetherReader reader event.momentum event.frame 0))
      (norm_nonneg (jointResolvent event.momentum event.frame event.energy 0))
      (norm_nonneg (noetherReaderContact reader force event.momentum event.frame))
      (norm_nonneg (jointCurrent event.momentum event.frame event.energy 0 force))
      (norm_nonneg (jointCurrent event.momentum event.frame 0 0 force))
      (norm_nonneg (actualA event.momentum event.frame)) cp b c d contact jg jt a) (by norm_num)

theorem source_joint_polarization_sigma_four_price (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (radius : ℝ) (inside : eps^2 ≤ radius)
    (sigma : ℝ) (positive : 0 < sigma) (small : sigma ≤ 1) (i j : Fin 289) :
    sigma^4*‖dressedStaticPolarization event (eps^2 • n) (sigma:ℂ) i j‖ ≤
      56*sourceJointCubicNoetherPrice event n radius (fieldUnit i) (fieldUnit j) :=
  (actual_static_polarization_sigma_four_price event _ sigma positive small i j).trans
    (mul_le_mul_of_nonneg_left (source_joint_complete_noether_price event eps n radius inside
      (fieldUnit i) (fieldUnit j)) (by norm_num))

private theorem contracted_price (A : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289 → ℂ)
    (P : Matrix (Fin 289) (Fin 289) ℝ) (s : ℝ) (positive : 0 < s)
    (nonnegative : ∀ i j, 0 ≤ P i j) (entry : ∀ i j, s^4*‖A i j‖ ≤ 56*P i j) :
    s^4*‖A*ᵥv‖ ≤ 56*∑ i, ∑ j, P i j*‖v j‖ := by
  have row (i : Fin 289) : s^4*‖(A*ᵥv) i‖ ≤ 56*∑ j, P i j*‖v j‖ := by
    have sum_price := norm_sum_le Finset.univ (fun j => A i j*v j)
    calc
      _ ≤ s^4*∑ j, ‖A i j*v j‖ := mul_le_mul_of_nonneg_left sum_price (by positivity)
      _ = ∑ j, (s^4*‖A i j‖)*‖v j‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul]
        ring
      _ ≤ ∑ j, (56*P i j)*‖v j‖ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (entry i j) (norm_nonneg _))
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have mass_nonnegative (i : Fin 289) : 0 ≤ ∑ j, P i j*‖v j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (nonnegative i j) (norm_nonneg _))
  have cap (i : Fin 289) : ‖(A*ᵥv) i‖ ≤ (56*∑ i, ∑ j, P i j*‖v j‖)/s^4 := by
    apply (le_div_iff₀ (pow_pos positive 4)).mpr
    rw [mul_comm]
    exact (row i).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mass_nonnegative j) (Finset.mem_univ i)) (by norm_num))
  have bound := (pi_norm_le_iff_of_nonneg (show 0 ≤ (56*∑ i, ∑ j, P i j*‖v j‖)/s^4 by
    exact div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mass_nonnegative i)))
      (by positivity))).mpr cap
  exact (mul_comm _ _).trans_le ((le_div_iff₀ (pow_pos positive 4)).mp bound)


theorem source_joint_cubic_noether_nonnegative (event : DressedEvent) (n : PhysicalMomentum)
    (radius : ℝ) (positive : 0 ≤ radius) (reader force : Field289) :
    0 ≤ sourceJointCubicNoetherPrice event n radius reader force :=
  (complete_cubic_noether_price_nonneg event ((0:ℝ)^2 • n) reader force).trans
    (source_joint_complete_noether_price event 0 n radius (by simpa using positive) reader force)

def sourceJointNoetherWindowMass (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (radius : ℝ) (positive : 0 < sigma) (small : sigma ≤ 1)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) : ℝ :=
  ∑ i, ∑ j, sourceJointCubicNoetherPrice event n radius (fieldUnit i) (fieldUnit j)*
    sourceQuantumFieldWindowPrice event e sigma n positive small regular tolerance accurate j

/-- The common epsilon-radius price contracts with the same actual field
window, retaining its clock/spatial dependence and complete source weights. -/
theorem source_joint_quantum_window_driver_price (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (radius : ℝ) (inside : e.val^2 ≤ radius)
    (positive : 0 < sigma) (small : sigma ≤ 1)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    sigma^3*‖sourceTemporalActualQuantumDriver event e sigma n‖ ≤
      56*sourceJointNoetherWindowMass event e sigma n radius positive small regular tolerance accurate := by
  let A : Matrix (Fin 289) (Fin 289) ℂ :=
    Matrix.of (fun i j => sourcePreparedPiEntry event (e.val^2 • n) (sigma:ℂ) i j)
  let P : Matrix (Fin 289) (Fin 289) ℝ :=
    fun i j => sourceJointCubicNoetherPrice event n radius (fieldUnit i) (fieldUnit j)
  have clock : 0 < (sigma:ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have nonnegative (i j : Fin 289) : 0 ≤ P i j :=
    source_joint_cubic_noether_nonnegative event n radius ((sq_nonneg e.val).trans inside) _ _
  have entry (i j : Fin 289) : sigma^4*‖A i j‖ ≤ 56*P i j := by
    rw [show A i j = dressedStaticPolarization event (e.val^2 • n) (sigma:ℂ) i j from
      source_prepared_pi_actual event _ _ clock i j]
    exact source_joint_polarization_sigma_four_price event e.val n radius inside sigma positive small i j
  have contracted := contracted_price A (sourceTemporalCorrectedField event e.val sigma n) P sigma positive nonnegative entry
  have field := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => Finset.sum_le_sum
    (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left
      (source_quantum_actual_field_window_price event e sigma n positive small regular tolerance accurate j)
      (nonnegative i j)))
  have scaled : sigma^3*‖(sigma:ℂ) • (A*ᵥsourceTemporalCorrectedField event e.val sigma n)‖ =
      sigma^4*‖A*ᵥsourceTemporalCorrectedField event e.val sigma n‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    ring
  simp only [sourceTemporalActualQuantumDriver, sourcePreparedClockQuantumMatrix, Matrix.smul_mulVec]
  change sigma^3*‖(sigma:ℂ) • (A*ᵥsourceTemporalCorrectedField event e.val sigma n)‖ ≤ _
  rw [scaled]
  exact contracted.trans (mul_le_mul_of_nonneg_left field (by norm_num))

theorem source_joint_quantum_native_reader_price (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (spatial_small : e.val^2 ≤ staticRadius)
    (radius : ℝ) (inside : e.val^2 ≤ radius) (positive : 0 < sigma) (small : sigma ≤ 1)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    sigma^3*‖sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, spatial_small⟩
      (sourceTemporalActualQuantumDriver event e sigma n)‖ ≤
        ‖sourceQuantumNativeReader e n unit spatial_small‖*
          (56*sourceJointNoetherWindowMass event e sigma n radius positive small regular tolerance accurate) := by
  rw [←source_quantum_native_reader_actual e n unit spatial_small (sourceTemporalActualQuantumDriver event e sigma n)]
  have applied := Matrix.linfty_opNorm_mulVec (sourceQuantumNativeReader e n unit spatial_small)
    (sourceTemporalActualQuantumDriver event e sigma n)
  have multiplied := mul_le_mul_of_nonneg_left applied (pow_pos positive 3).le
  calc
    _ ≤ sigma^3*(‖sourceQuantumNativeReader e n unit spatial_small‖*‖sourceTemporalActualQuantumDriver event e sigma n‖) := multiplied
    _ = ‖sourceQuantumNativeReader e n unit spatial_small‖*(sigma^3*‖sourceTemporalActualQuantumDriver event e sigma n‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (source_joint_quantum_window_driver_price event e sigma n radius inside positive small regular tolerance accurate)
      (norm_nonneg _)

theorem source_joint_quantum_window_ir_price (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (spatial_small : e.val^2 ≤ staticRadius)
    (radius : ℝ) (inside : e.val^2 ≤ radius) (positive : 0 < sigma) (small : sigma ≤ 1)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, spatial_small⟩
    let driver := sourceTemporalActualQuantumDriver event e sigma n
    sigma^3*‖-(e.val:ℂ)^4*(sourceN3TemporalEMCoefficient event e.val sigma n -
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce)-
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceSpatialStaticRegularField n unit kappa driver))-
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤
      ‖noetherPairScale^2‖*((∑ i, ‖sourceTemporalEMForce i‖)*
        ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖*
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val)*
        ‖sourceQuantumNativeReader e n unit spatial_small‖*
        (56*sourceJointNoetherWindowMass event e sigma n radius positive small regular tolerance accurate)) := by
  have original := source_temporal_quantum_spatial_pole_price event e sigma n unit spatial_small positive regular
  have reader := source_joint_quantum_native_reader_price event e sigma n unit spatial_small radius inside
    positive small regular tolerance accurate
  have paid := mul_le_mul_of_nonneg_left original (pow_pos positive 3).le
  have error_nonnegative := effectiveErrorBudget_nonneg
  apply paid.trans
  have scale_paid := mul_le_mul_of_nonneg_left reader
    (show 0 ≤ ‖noetherPairScale^2‖*((∑ i, ‖sourceTemporalEMForce i‖)*
      ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit ⟨e.val^2, pow_pos e.property.1 2, spatial_small⟩)‖*
      (2*staticInverseBudget^2*effectiveErrorBudget*e.val^2)) by positivity)
  convert scale_paid using 1 <;> ring

end LowEnergy.GaussComposite.ActualSourcePreparedJointNoetherSourcePrice
