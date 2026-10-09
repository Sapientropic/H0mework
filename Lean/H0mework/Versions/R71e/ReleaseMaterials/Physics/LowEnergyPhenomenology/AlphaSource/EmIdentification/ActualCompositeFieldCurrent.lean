import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMExternalRepresentation
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceYukawaPositiveCorrection
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRawJointReaderCompression
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeStaticUniform

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeFieldCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussQuantumMultiplier GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory GaussDensityCore GaussFockPair
open MixedSpectatorCandidate YukawaResolventDetection GaussCoreLabel
open FullYDynamicSource FullYDynamicSourceRefinement FullYDynamicResponse FullYSourceResolventGraphSplice
open SourceClockYukawaCubicCurrent GeneralThreeParticleResponse SourceScalarPairedTransport
open PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift PreparationVacuumSourceActionJets
open PreparationVacuumGaugeSourceInjection PreparationVacuumNonlinearFieldCurve PreparationVacuumOriginalGreenFeedback PreparationVacuumActualFieldQuantization
open PreparationVacuumStaticPoleResponse PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic
open ActualEMExternalRepresentation
open MeasureTheory Filter
open scoped Matrix BigOperators Topology InnerProductSpace Matrix.Norms.Operator
attribute [local irreducible] literalCoreResolvent literalSharpResolvent rawForm rawContactForm
  sourceGreen wholeStaticLimit

/-- The actual source profile is generated before every response parameter. -/
def compositeProfile (dual : Bool) : ScalarTest :=
  (actual_generated_candidate_Y_excess dual).choose

theorem composite_profile_source (dual : Bool) : compositeProfile dual sourcePoint.val=1 :=
  (actual_generated_candidate_Y_excess dual).choose_spec.1

structure CompositeLeg where
  dual : Bool
  frame : GaussUnitaryHistory.Index
  sharp : Bool
  energy : ℂ
  nonreal : energy.im≠0

def compositeInput (leg : CompositeLeg) : QuantumTest :=candidateTest leg.dual (compositeProfile leg.dual)

/-- The actual spacetime input is the same certified norm1 full504 charged spin-half/color-singlet state with its generated profile. -/
theorem composite_input_unit (leg : CompositeLeg) (z : SourceCoordinateSlice) :
    compositeInput leg z=((Real.sqrt 2:ℂ)*compositeProfile leg.dual z) • actualCompositeUnit leg.dual := by
  have nz : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  change compositeProfile leg.dual z • candidate leg.dual=_
  rw [actualCompositeUnit,smul_smul]
  congr 1
  field_simp

/-- Literal full504 EM charge is generated on the input; no eigenstate claim is imposed on the later fullY response. -/
theorem composite_input_em_charge (leg : CompositeLeg) (z : SourceCoordinateSlice) :
    GaussQuantumMultiplier.quantized PhysicalEMNativeChargeFull.emFullCharge (compositeInput leg z)=
      (if leg.dual then (-1:ℂ) else 1) • compositeInput leg z := by
  rw [composite_input_unit,map_smul,(actual_composite_em_spin_color leg.dual).2.1]
  module

def compositeResponse (leg : CompositeLeg) : QuantumTest :=
  if leg.sharp then literalSharpResolvent leg.frame leg.energy leg.nonreal (compositeInput leg)
    else literalCoreResolvent leg.frame leg.energy leg.nonreal (compositeInput leg)

/-- Neither the full original Y nor its independent sharp is replaced by a one-particle preparation. -/
theorem composite_response_nonzero (leg : CompositeLeg) : compositeResponse leg≠0 := by
  have input : compositeInput leg≠0 := by
    have hn:=actual_candidate_test_nonzero leg.dual (compositeProfile leg.dual) (by
      intro zero
      have atSource:=congrArg (fun f : ScalarTest=>f sourcePoint.val) zero
      rw [composite_profile_source] at atSource
      simp only [zero_apply] at atSource
      exact one_ne_zero atSource)
    intro zero
    apply hn
    change GaussCoreHilbert.embed (compositeInput leg)=0
    rw [zero,map_zero]
  intro zero
  cases hs : leg.sharp
  · have eqn:=LinearMap.congr_fun (literal_core_right_inverse leg.frame leg.energy leg.nonreal) (compositeInput leg)
    change literalCoreShift leg.frame leg.energy (literalCoreResolvent leg.frame leg.energy leg.nonreal (compositeInput leg))=compositeInput leg at eqn
    have response : compositeResponse leg=literalCoreResolvent leg.frame leg.energy leg.nonreal (compositeInput leg) := by simp only [compositeResponse,hs,Bool.false_eq_true,if_false]
    rw [←response,zero,map_zero] at eqn
    exact input eqn.symm
  · have eqn:=LinearMap.congr_fun (literal_sharp_right_inverse leg.frame leg.energy leg.nonreal) (compositeInput leg)
    change literalSharpShift leg.frame leg.energy (literalSharpResolvent leg.frame leg.energy leg.nonreal (compositeInput leg))=compositeInput leg at eqn
    have response : compositeResponse leg=literalSharpResolvent leg.frame leg.energy leg.nonreal (compositeInput leg) := by simp only [compositeResponse,hs,if_true]
    rw [←response,zero,map_zero] at eqn
    exact input eqn.symm

/-- The complete response keeps the original finite-frame compression defect in the full source equation. -/
theorem composite_full_source_return (leg : CompositeLeg) (full : leg.sharp=false) :
    (GaussFullHamiltonian.fullAction-leg.energy • (1 : Module.End ℂ QuantumTest)) (compositeResponse leg)=
      compositeInput leg+defectAction leg.frame (compositeResponse leg) := by
  simpa only [compositeResponse,full,Bool.false_eq_true,if_false] using
    literal_full_source_residual leg.frame leg.energy leg.nonreal (compositeInput leg)

theorem composite_sharp_source_return (leg : CompositeLeg) (sharp : leg.sharp=true) :
    (GaussFullHamiltonian.sharpAction-leg.energy • (1 : Module.End ℂ QuantumTest)) (compositeResponse leg)=
      compositeInput leg+defectAction leg.frame (compositeResponse leg) := by
  simpa only [compositeResponse,sharp,if_true] using
    literal_sharp_full_source_residual leg.frame leg.energy leg.nonreal (compositeInput leg)

/-- All four original Y legs of this N3 event remain in the generated current endpoints. -/
theorem composite_full_four_legs (leg : CompositeLeg) (full : leg.sharp=false) :
    compositeResponse leg=∑j : Fin 4, GeneralThreeParticleResponse.leg leg.frame leg.energy leg.nonreal (compositeInput leg) j.val := by
  simpa only [compositeResponse,full,Bool.false_eq_true,if_false] using
    full_response leg.frame leg.energy leg.nonreal (compositeInput leg)
      (actual_candidate_test_sector leg.dual (compositeProfile leg.dual))

/-- The independent sharp endpoint consumes the actual bottom-grade response law. -/
theorem composite_sharp_bottom (leg : CompositeLeg) (sharp : leg.sharp=true) :
    compositeResponse leg=resolventCore leg.frame leg.energy leg.nonreal (compositeInput leg) := by
  simpa only [compositeResponse,sharp,if_true] using
    sharp_response leg.frame leg.energy leg.nonreal (compositeInput leg)
      (actual_candidate_test_sector leg.dual (compositeProfile leg.dual))

def compositeUnitLeg (leg : CompositeLeg) : QuantumTest :=
  ((‖GaussCoreHilbert.embed (compositeResponse leg)‖:ℂ)⁻¹) • compositeResponse leg

/-- Each actual dynamic endpoint generates its own unit normalization from the complete response. -/
theorem composite_unit_norm (leg : CompositeLeg) : ‖GaussCoreHilbert.embed (compositeUnitLeg leg)‖=1 := by
  have nz : GaussCoreHilbert.embed (compositeResponse leg)≠0 := by
    intro zero
    exact composite_response_nonzero leg (embed_injective zero)
  rw [compositeUnitLeg,map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr nz)]

/-- Unit normalization consumes the full four-leg norm, retaining all original Y contributions. -/
theorem composite_full_norm_four_legs (leg : CompositeLeg) (full : leg.sharp=false) :
    ‖GaussCoreHilbert.embed (compositeResponse leg)‖^2=
      ∑j : Fin 4, ‖GaussCoreHilbert.embed (GeneralThreeParticleResponse.leg leg.frame leg.energy leg.nonreal (compositeInput leg) j.val)‖^2 := by
  simpa only [compositeResponse,full,Bool.false_eq_true,if_false] using
    full_response_norm leg.frame leg.energy leg.nonreal (compositeInput leg)
      (actual_candidate_test_sector leg.dual (compositeProfile leg.dual))

/-- The unit endpoint retains the generated source normalization and the original compression defect. -/
theorem composite_unit_full_source (leg : CompositeLeg) (full : leg.sharp=false) :
    (GaussFullHamiltonian.fullAction-leg.energy • (1 : Module.End ℂ QuantumTest)) (compositeUnitLeg leg)=
      ((‖GaussCoreHilbert.embed (compositeResponse leg)‖:ℂ)⁻¹) • compositeInput leg+
        defectAction leg.frame (compositeUnitLeg leg) := by
  rw [compositeUnitLeg,map_smul,composite_full_source_return leg full,smul_add,map_smul]

theorem composite_unit_sharp_source (leg : CompositeLeg) (sharp : leg.sharp=true) :
    (GaussFullHamiltonian.sharpAction-leg.energy • (1 : Module.End ℂ QuantumTest)) (compositeUnitLeg leg)=
      ((‖GaussCoreHilbert.embed (compositeResponse leg)‖:ℂ)⁻¹) • compositeInput leg+
        defectAction leg.frame (compositeUnitLeg leg) := by
  rw [compositeUnitLeg,map_smul,composite_sharp_source_return leg sharp,smul_add,map_smul]

/-- The causal frequency event is the existing fullY/independent-sharp owner event, on its original line. -/
def compositeCausalLeg (F : GaussUnitaryHistory.Index) (dual sharp advanced : Bool)
    (damping : ℝ) (positive : 0<damping) (omega : ℝ) : CompositeLeg :=
  ⟨dual,F,sharp,SourceResolventBandLimit.line (FullYPairedParseval.direction advanced*damping) omega,
    FullYDynamicResponse.causal_line_nonreal advanced damping omega positive⟩

theorem composite_causal_owner (F : GaussUnitaryHistory.Index) (dual sharp advanced : Bool)
    (damping : ℝ) (positive : 0<damping) (omega : ℝ) :
    compositeResponse (compositeCausalLeg F dual sharp advanced damping positive omega)=
      FullYDynamicResponse.literalResponse F sharp (candidateTest dual (compositeProfile dual)) advanced damping positive omega := rfl

/-- Full289 forcing, generated directly by the original independent-dual action density on the actual N3 response endpoints. -/
def compositeCurrent (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 289→ℂ :=
  fun i=> -rawForm (fieldUnit i) p (compositeUnitLeg left) (compositeUnitLeg right) 0

/-- The original action symbol precedes full independent-dual quantization in every current slot. -/
theorem composite_current_action (p : PhysicalMomentum) (left right : CompositeLeg) (i : Fin 289) :
    compositeCurrent p left right i=
      -(∫z,pairSample z (compositeUnitLeg left z)
        (quantizer (rawActionSymbol (fieldUnit i) p (sourceState z)) (compositeUnitLeg right z))
          ∂GaussHistoryHilbert.configurationMeasure) := by
  rw [compositeCurrent,rawForm_original]
  rfl

/-- The complete original contact derivative is retained at the same actual endpoints. -/
theorem composite_current_contact (p : PhysicalMomentum) (left right : CompositeLeg)
    (i : Fin 289) (force : Field289) :
    HasDerivAt (fun r : ℝ=> -rawForm (fieldUnit i) p (compositeUnitLeg left) (compositeUnitLeg right) (r • force))
      (-rawContactForm (fieldUnit i) force p (compositeUnitLeg left) (compositeUnitLeg right)) 0 :=
  (rawForm_direction (fieldUnit i) force p (compositeUnitLeg left) (compositeUnitLeg right)).neg

/-- Contact is the original action second variation on the same generated endpoints. -/
theorem composite_contact_original (p : PhysicalMomentum) (left right : CompositeLeg)
    (i : Fin 289) (force : Field289) :
    -rawContactForm (fieldUnit i) force p (compositeUnitLeg left) (compositeUnitLeg right)=
      -(∫z,pairSample z (compositeUnitLeg left z)
        (rawContactFiber (fieldUnit i) force p z (compositeUnitLeg right z))
          ∂GaussHistoryHilbert.configurationMeasure) := by
  rw [rawContactForm_original]

/-- The detector alone carries the original single action/time-speed normalization. -/
def compositeDetector (branch : Fin 2) (p : PhysicalMomentum) (left right : CompositeLeg) : Fin 289→ℂ :=
  (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹) • compositeCurrent p left right

def compositeMatrixRead (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : WholeMatrix→L[ℝ]ℂ :=
  ({toFun := fun M=>dotProduct (compositeDetector branch pd dL dR) (M*ᵥcompositeCurrent ps sL sR)
    map_add' := fun M N=>by rw [Matrix.add_mulVec,dotProduct_add]
    map_smul' := fun r M=>by simp only [Matrix.smul_mulVec,dotProduct_smul,RingHom.id_apply,Complex.real_smul]} :
      WholeMatrix→ₗ[ℝ]ℂ).toContinuousLinearMap

/-- The same generated current and detector consume the entire original field matrix. -/
theorem composite_matrix_read (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (M : WholeMatrix) :
    compositeMatrixRead branch pd ps dL dR sL sR M=
      dotProduct (compositeDetector branch pd dL dR) (M*ᵥcompositeCurrent ps sL sR) := rfl

/-- The coefficient is the source-fixed full static residue applied once to the actual generated current. -/
theorem composite_whole_coefficient (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    dotProduct (compositeDetector branch pd dL dR) (wholeStaticLimit*ᵥcompositeCurrent ps sL sR)=
      -dotProduct (compositeDetector branch pd dL dR) (staticResidue (compositeCurrent ps sL sR)) := by
  rw [whole_static_limit_actual_field,dotProduct_neg]

/-- The actual N3 source and independently normalized detector have one source-generated uniform radius over all physical directions. -/
theorem composite_whole_green_uniform (branch : Fin 2) (pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃radius : ℝ, 0<radius ∧ ∀r : staticDomain, r.val<radius→
      ∀n : PhysicalMomentum, ∀unit : spatialSquare n=1,
        ‖(r.val:ℂ)^2*dotProduct (compositeDetector branch pd dL dR)
          (sourceGreen (sourceSpatialStaticRegularPoint n unit r)*ᵥcompositeCurrent ps sL sR)-
            dotProduct (compositeDetector branch pd dL dR) (wholeStaticLimit*ᵥcompositeCurrent ps sL sR)‖≤epsilon := by
  let L:=compositeMatrixRead branch pd ps dL dR sL sR
  let price:=1+‖L‖
  have pp : 0<price := by dsimp only [price];positivity
  obtain ⟨radius,rp,paid⟩:=whole_static_green_uniform (epsilon/price) (div_pos positive pp)
  refine ⟨radius,rp,?_⟩
  intro r small n unit
  have total : ‖L ((r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r))-L wholeStaticLimit‖≤epsilon := by
    rw [←map_sub]
    calc
      _≤‖L‖*‖(r.val^2:ℝ) • sourceGreen (sourceSpatialStaticRegularPoint n unit r)-wholeStaticLimit‖:=L.le_opNorm _
      _≤‖L‖*(epsilon/price):=mul_le_mul_of_nonneg_left (paid r small n unit) (norm_nonneg _)
      _≤price*(epsilon/price):=mul_le_mul_of_nonneg_right (by dsimp only [price];linarith [norm_nonneg L]) (div_nonneg positive.le pp.le)
      _=epsilon:=by field_simp
  simpa only [L,composite_matrix_read,map_smul,Complex.real_smul,smul_eq_mul,Complex.ofReal_pow] using total

end LowEnergy.GaussComposite.ActualCompositeFieldCurrent
