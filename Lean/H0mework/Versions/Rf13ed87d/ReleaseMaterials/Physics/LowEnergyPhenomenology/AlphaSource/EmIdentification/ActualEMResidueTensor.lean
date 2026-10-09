import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCarrier
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPolarizationRead
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceLockedPoleDirection

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage10
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open PreparationCoordinates PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumNativeDimensions
open SourcePropagationNativeActionHessian PreparationVacuumNativePoleTensor
open PhysicalEMGaugeRealization PhysicalEMFieldCurrent
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalActualPolarizationResponse PreparationPhysicalElectromagneticDirectionReturn
open PreparationVacuumElectromagneticIdentity Electromagnetic.CanonicalCoframe
open PreparationVacuumPhysicalFeedback
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationVacuumPhysicalQuantumLockedCharge CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

theorem em_original_coordinates : rawCoordinates (p286CoordinateEquiv emDirection) =
    -(1/2:ℝ) • Pi.single 6 1 + (1/2:ℝ) • Pi.single 7 1 - (1/2:ℝ) • Pi.single 11 1 := by
  change rawRead (p286CoordinateEquiv emDirection) = _
  unfold rawRead
  rw [nativeCoordinates_apply]
  funext i
  fin_cases i <;>
    norm_num [emDirection, HyperchargeResponse.chargeDirection, nativeCoordinates,
      sourceColorP286Generator_color, sourceColorP286Generator_weak_zero,
      sourceColorP286Generator_hypercharge_zero, hyperchargeGenerator, Pi.single_apply, sourceColorRaw, Fin.ext_iff, Matrix.cons_val]
  all_goals dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.cons, Fin.cases,
    Fin.induction, Fin.induction.go]
  all_goals norm_num

/-- All four EM components retain the original raw gauge coordinates and their fixed normalization. -/
theorem em_projection_coordinates (V : Fin 289 → ℂ) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ V) mu =
      (1/2:ℂ) * (-V (gaugeSlot mu 6) + V (gaugeSlot mu 7) - V (gaugeSlot mu 11)) := by
  simp only [emInsertion, Matrix.mulVec, dotProduct, Matrix.transpose_apply, emGaugeField,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [gaugeField, Pi.single_apply, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have coords : (fun a : Fin 12 => (rawCoordinates (p286CoordinateEquiv emDirection) a : ℂ)) =
      -(1/2:ℂ) • Pi.single 6 1 + (1/2:ℂ) • Pi.single 7 1 - (1/2:ℂ) • Pi.single 11 1 := by
    rw [em_original_coordinates]
    funext a
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_sub,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_neg,Pi.single_apply,apply_ite,
      Complex.ofReal_one,Complex.ofReal_zero]
    push_cast
    split_ifs <;> rfl
  change dotProduct (fun a : Fin 12 => (rawCoordinates (p286CoordinateEquiv emDirection) a : ℂ))
    (fun a => V (gaugeSlot mu a)) = _
  rw [coords,sub_dotProduct,add_dotProduct,smul_dotProduct,smul_dotProduct,smul_dotProduct,
    single_dotProduct,single_dotProduct,single_dotProduct]
  simp only [one_mul,smul_eq_mul]
  ring


open PreparationPhysicalNormalizedFullField PreparationVacuumFullOriginResponse PreparationVacuumWholeOrigin

/-- The complete literal EM first jet has two slow input columns; the third is generated zero. -/
def emLiteralA (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![-(1/2:ℂ)*v 0-(5/72:ℂ)*rootTwo*rootFifteen*v 3,
    -(1/4:ℂ)*v 1, -(1/4:ℂ)*v 2,
    (5/72:ℂ)*rootTwo*rootFifteen*v 0-(1/2:ℂ)*v 3]

def emLiteralB (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![-(8/11:ℂ)*v 0, -(49/67:ℂ)*v 1, -(49/67:ℂ)*v 2, -(46/67:ℂ)*v 3]

set_option maxHeartbeats 2400000 in
private theorem em_literal_row (v : Fin 4 → ℂ) (mu : Fin 4) (j : Fin 289) :
    (1/2:ℂ)*(-sourceMatrix sourceEnergyChannelTerms v (gaugeSlot mu 6) j +
      sourceMatrix sourceEnergyChannelTerms v (gaugeSlot mu 7) j -
      sourceMatrix sourceEnergyChannelTerms v (gaugeSlot mu 11) j) =
    (Pi.single 0 (emLiteralA v mu) + Pi.single 1 (emLiteralB v mu) : Fin 289 → ℂ) j := by
  rw [←rowTerms_entry sourceEnergyChannelTerms v (gaugeSlot mu 6) j,
    ←rowTerms_entry sourceEnergyChannelTerms v (gaugeSlot mu 7) j,
    ←rowTerms_entry sourceEnergyChannelTerms v (gaugeSlot mu 11) j]
  fin_cases mu <;>
    norm_num [rowTerms,sourceEnergyChannelTerms,gaugeSlot,
      Matrix.of_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals simp [sourceMatrix,SourceTerm.matrix,Matrix.single_apply,coefficientValue,
    Powers.value,Pi.single_apply,emLiteralA,emLiteralB,eq_comm]
  all_goals split_ifs <;> ring

/-- The four generated EM rows explicitly retain all momentum components and exact source coefficients. -/
theorem em_literal_projection (v : Fin 4 → ℂ) (w : Fin 289 → ℂ) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ (sourceMatrix sourceEnergyChannelTerms v *ᵥ w)) mu =
      emLiteralA v mu * w 0 + emLiteralB v mu * w 1 := by
  rw [em_projection_coordinates]
  simp only [Matrix.mulVec, dotProduct]
  rw [←Finset.sum_neg_distrib, ←Finset.sum_add_distrib, ←Finset.sum_sub_distrib, Finset.mul_sum]
  have row (j : Fin 289) :
      (1/2:ℂ)*(- (sourceMatrix sourceEnergyChannelTerms v (gaugeSlot mu 6) j*w j)+
        sourceMatrix sourceEnergyChannelTerms v (gaugeSlot mu 7) j*w j-
        sourceMatrix sourceEnergyChannelTerms v (gaugeSlot mu 11) j*w j) =
      (Pi.single 0 (emLiteralA v mu)+Pi.single 1 (emLiteralB v mu) : Fin 289 → ℂ) j*w j := by
    rw [←em_literal_row]
    ring
  simp_rw [row]
  simp [Pi.single_apply, add_mul, Finset.sum_add_distrib, ite_mul]

private theorem em_origin_row (mu : Fin 4) (a : Fin 3) (j : Fin 289) :
    fullNativeOrigin (gaugeSlot mu (![6,7,11] a)) j = 0 := by
  rw [fullNativeOrigin_generated, ←rowTerms_entry]
  have rows : rowTerms (gaugeSlot mu (![6,7,11] a)) fullNativeOriginTerms = [] := by
    fin_cases mu <;> fin_cases a <;> decide +kernel
  rw [rows]
  rfl

theorem em_origin_projection (w : Fin 289 → ℂ) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ (fullNativeOrigin *ᵥ w)) mu = 0 := by
  rw [em_projection_coordinates]
  have row (a : Fin 3) : (fullNativeOrigin *ᵥ w) (gaugeSlot mu (![6,7,11] a)) = 0 := by
    simp only [Matrix.mulVec, dotProduct, em_origin_row, zero_mul, Finset.sum_const_zero]
  rw [show (fullNativeOrigin *ᵥ w) (gaugeSlot mu 6)=0 from row 0,
    show (fullNativeOrigin *ᵥ w) (gaugeSlot mu 7)=0 from row 1,
    show (fullNativeOrigin *ᵥ w) (gaugeSlot mu 11)=0 from row 2]
  ring


/-- Exact EM output of the original pole, including its full fast and residual dependence. -/
def emFrequencyProjection (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (mu : Fin 4) : ℂ :=
  (epsilon:ℂ)^2 * (emLiteralA (physicalFrequencyMomentum s n) mu *
      sourcePoleCoordinates branch epsilon s n 0 +
    emLiteralB (physicalFrequencyMomentum s n) mu * sourcePoleCoordinates branch epsilon s n 1 +
    (emInsertion.transpose *ᵥ sourcePoleFastJet branch epsilon s n) mu) +
    (emInsertion.transpose *ᵥ sourcePoleFrameResidual branch epsilon s n) mu

theorem em_frequency_projection_generated (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon ≠ 0) (mu : Fin 4) :
    (emInsertion.transpose *ᵥ sourceNativeFrequencyPolarization branch epsilon s n) mu =
      emFrequencyProjection branch epsilon s n mu := by
  have returned := congrArg (fun V : Fin 289 → ℂ => (emInsertion.transpose *ᵥ V) mu)
    (sourceNativeFrequencyPolarization_firstReturn branch epsilon s n nonzero)
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at returned
  have origin : (emInsertion.transpose *ᵥ sourcePoleOriginField branch epsilon s n) mu=0 := by
    unfold sourcePoleOriginField
    rw [←Matrix.mulVec_mulVec]
    exact em_origin_projection _ mu
  rw [origin,sourcePoleJetField_literal,Matrix.mulVec_add,Pi.add_apply] at returned
  rw [sourcePoleLiteralJet,em_literal_projection] at returned
  unfold emFrequencyProjection
  linear_combination returned

/-- The actual Ward cosource enters the original full reader before restriction to five modes. -/
def emActualModeCosource (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) : Fin 5 → ℂ := fun i =>
  (wideRayScaling epsilon *ᵥ (slowFastFrame.transpose *ᵥ
    (rawEffectiveReader (frequencyRay epsilon s n) *ᵥ
      (activeProjection *ᵥ sheetCosource q epsilon s n p left right T)))) (fiveIndex i)

theorem em_actual_mode_cosource (q : PhysicalResponsePoint) (epsilon s : ℝ) (n p : PhysicalMomentum)
    (left right : RestStateIndex) (T : ℝ) :
    nativeModeForcing epsilon s n (sheetCurrent q epsilon s n p left right T) =
      emActualModeCosource q epsilon s n p left right T := by
  unfold nativeModeForcing activeForcing emActualModeCosource
  rw [sheetCurrent_ward]

/-- The cofactor formula cancels the shared physical slope, keeping the source pivot and every mode. -/
def emActualCofactorAmplitude (q : PhysicalResponsePoint) (branch : Fin 2) (epsilon s : ℝ)
    (n p : PhysicalMomentum) (left right : RestStateIndex) (T : ℝ) : ℂ :=
  (((extendedTensor epsilon s n).adjugate *ᵥ emActualModeCosource q epsilon s n p left right T)
    (residueIndex branch)) / (extendedTensor epsilon s n).adjugate (residueIndex branch) (residueIndex branch)

theorem em_actual_cofactor_amplitude (q : PhysicalResponsePoint) (branch : Fin 2)
    (n p : PhysicalMomentum) (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonLeftReader branch e.val (sourceSheet branch n unit e.val) n
        (sheetCurrent q e.val (sourceSheet branch n unit e.val) n p left right T) =
      emActualCofactorAmplitude q branch e.val (sourceSheet branch n unit e.val) n p left right T := by
  filter_upwards [scaleVal_tendsto.eventually (sourceSheet_simple branch n unit)] with e simple
  unfold sourcePhotonLeftReader sourceNativePoleCoefficient
  rw [em_actual_mode_cosource]
  unfold sourceResidue emActualCofactorAmplitude
  simp only [Matrix.smul_mulVec,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero (Complex.ofReal_ne_zero.mpr simple.1))

/-- All eight-by-eight actual moving current residues have their own computed coefficient on the original full polarization. -/
theorem em_actual_frequency_factor (q : PhysicalResponsePoint) (branch : Fin 2)
    (n p : PhysicalMomentum) (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      actualFrequencyResidue q e.val (sourceSheet branch n unit e.val) n p left right T =
        emActualCofactorAmplitude q branch e.val (sourceSheet branch n unit e.val) n p left right T •
          sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceWholePhotonResidue_factor branch n unit,
    em_actual_cofactor_amplitude q branch n p unit left right T] with e factor cofactor
  have returned := factor (sheetCurrent q e.val (sourceSheet branch n unit e.val) n p left right T)
  rw [cofactor] at returned
  rw [sourceWholePhotonResidue_apply] at returned
  change actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p left right T = _ at returned
  rw [actualFrequencyResidue, returned, sourceNativeFrequencyPolarization]
  ext i
  simp only [Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_pow]
  ring

/-- The actual measured EM four-vector is returned without deleting any fast or mixed field row. -/
theorem em_actual_frequency_projection (q : PhysicalResponsePoint) (branch : Fin 2)
    (n p : PhysicalMomentum) (unit : spatialSquare n=1) (left right : RestStateIndex) (T : ℝ) :
    ∀ᶠ e in scaleApproach, ∀ mu : Fin 4,
      (emInsertion.transpose *ᵥ actualFrequencyResidue q e.val (sourceSheet branch n unit e.val) n p left right T) mu =
        emActualCofactorAmplitude q branch e.val (sourceSheet branch n unit e.val) n p left right T *
          emFrequencyProjection branch e.val (sourceSheet branch n unit e.val) n mu := by
  filter_upwards [em_actual_frequency_factor q branch n p unit left right T] with e factor
  intro mu
  rw [factor, Matrix.mulVec_smul]
  change _ * (emInsertion.transpose *ᵥ sourceNativeFrequencyPolarization branch e.val _ n) mu = _
  rw [em_frequency_projection_generated branch e.val _ n e.property.1.ne' mu]

end LowEnergy.GaussComposite.ActualEMCarrierOwn
