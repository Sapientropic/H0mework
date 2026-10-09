import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeStaticCurrent
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.GaugeBand
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterBottomResponse

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeGaugeBand
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
open ActualCompositeFieldCurrent ActualCompositeStaticCurrent
open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumFullFieldRiesz
open GaussFockLabel NativeHistoryGrade NamedColorQtNext
open Set
attribute [local irreducible] rawForm compositeResponse

def compositeBase (leg : CompositeLeg) : QuantumTest :=
  resolventCore leg.frame leg.energy leg.nonreal (compositeInput leg)

theorem composite_base_bottom (leg : CompositeLeg) : project (3,0) (compositeBase leg)=compositeBase leg :=
  actual_resolvent_sector leg.frame (3,0) leg.energy leg.nonreal (compositeInput leg)
    (actual_candidate_test_sector leg.dual (compositeProfile leg.dual))

/-- FullY and its independent sharp have the same actual bottom component. -/
theorem composite_response_bottom (leg : CompositeLeg) : project (3,0) (compositeResponse leg)=compositeBase leg := by
  cases hs : leg.sharp
  · have paid:=actual_bottom_primal_projected_resolvent leg.frame 3 leg.energy leg.nonreal (compositeInput leg)
    have inputSector : project (3,0) (compositeInput leg)=compositeInput leg :=
      actual_candidate_test_sector leg.dual (compositeProfile leg.dual)
    rw [inputSector] at paid
    simpa only [compositeResponse,hs,Bool.false_eq_true,if_false,compositeBase] using paid
  · rw [composite_sharp_bottom leg hs]
    exact composite_base_bottom leg

private theorem sample_project (g : Label) (z : SourceCoordinateSlice) (u v : FockFiber) :
    pairSample z (fiberPiece g u) v=pairSample z u (fiberPiece g v) := by
  unfold pairSample
  apply Finset.sum_congr rfl
  intro word _
  simp only [fiberPiece_apply]
  by_cases same : NativeHistoryGrade.sourceLabel word=g <;> simp [same]

/-- Original pure gauge action variations preserve the complete actual Number/grade sector. -/
theorem gauge_form_project (mu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (g : Label) (f h : QuantumTest) :
    rawForm (gaugeField mu a) p (project g f) h 0=rawForm (gaugeField mu a) p f (project g h) 0 := by
  rw [rawForm_original,rawForm_original]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [project_apply]
  by_cases inside : z∈physicalChart
  · rw [sample_project]
    have blocks : Commute (fiberPiece g) (rawStateFiber (gaugeField mu a) p (sourceState z)) := by
      rw [←rawActionSymbol_actual]
      unfold fiberPiece
      exact blockWeight_quantized _ _ (sourceRawGaugeMatrix_gradeZero mu a p ⟨z,inside⟩)
    have commutes:=congrArg (fun A : FockFiber→L[ℂ] FockFiber=>A (h z)) blocks.eq
    simpa only [mul_apply_eq_comp] using congrArg (fun v=>pairSample z (f z) v) commutes
  · have off : z∉tsupport f:=fun member=>inside (f.tsupport_subset member)
    rw [image_eq_zero_of_notMem_tsupport off,map_zero,pairSample_zero_left,pairSample_zero_left]

/-- With an actual independent-sharp left endpoint, all raised fullY numerator legs are removed by the original gauge block law. -/
theorem composite_sharp_left_gauge (p : PhysicalMomentum) (left right : CompositeLeg)
    (sharp : left.sharp=true) (mu : Fin 4) (a : Fin 12) :
    rawForm (gaugeField mu a) p (compositeResponse left) (compositeResponse right) 0=
      rawForm (gaugeField mu a) p (compositeBase left) (compositeBase right) 0 := by
  have bottom : project (3,0) (compositeResponse left)=compositeResponse left := by
    rw [composite_sharp_bottom left sharp]
    exact composite_base_bottom left
  have paid:=gauge_form_project mu a p (3,0) (compositeResponse left) (compositeResponse right)
  rw [bottom,composite_response_bottom,composite_sharp_bottom left sharp] at paid
  rw [composite_sharp_bottom left sharp]
  exact paid

/-- The opposite actual sharp placement has the same generated gauge numerator reduction. -/
theorem composite_sharp_right_gauge (p : PhysicalMomentum) (left right : CompositeLeg)
    (sharp : right.sharp=true) (mu : Fin 4) (a : Fin 12) :
    rawForm (gaugeField mu a) p (compositeResponse left) (compositeResponse right) 0=
      rawForm (gaugeField mu a) p (compositeBase left) (compositeBase right) 0 := by
  have bottom : project (3,0) (compositeResponse right)=compositeResponse right := by
    rw [composite_sharp_bottom right sharp]
    exact composite_base_bottom right
  have paid:=gauge_form_project mu a p (3,0) (compositeResponse left) (compositeResponse right)
  rw [bottom,composite_response_bottom,composite_sharp_bottom right sharp] at paid
  rw [composite_sharp_bottom right sharp]
  exact paid.symm

private theorem raw_smul_left (reader : Field289) (p : PhysicalMomentum) (c : ℂ) (a b : QuantumTest) :
    rawForm reader p (c • a) b 0=star c*rawForm reader p a b 0 := by
  rw [rawForm_original,rawForm_original]
  simp only [smul_apply,pairSample_smul_left]
  rw [integral_const_mul]

private theorem raw_smul_right (reader : Field289) (p : PhysicalMomentum) (c : ℂ) (a b : QuantumTest) :
    rawForm reader p a (c • b) 0=c*rawForm reader p a b 0 := by
  rw [rawForm_original,rawForm_original]
  simp only [smul_apply,map_smul,pairSample_smul_right]
  rw [integral_const_mul]

def compositeInverseNorm (leg : CompositeLeg) : ℂ :=
  ((‖GaussCoreHilbert.embed (compositeResponse leg)‖:ℂ)⁻¹)

private theorem inverseNorm_star (leg : CompositeLeg) : star (compositeInverseNorm leg)=compositeInverseNorm leg := by
  change (starRingEnd ℂ) ((‖GaussCoreHilbert.embed (compositeResponse leg)‖:ℂ)⁻¹)=_
  rw [map_inv₀]
  congr 1
  exact Complex.conj_ofReal _

/-- A concrete original base-resolvent gauge current, rather than a caller-chosen coupling scalar. -/
def compositeBaseWeight (p : PhysicalMomentum) (left right : CompositeLeg) : ℂ :=
  (3/10:ℂ)*rootTwo*(-rawForm (gaugeField 1 0) p (compositeBase left) (compositeBase right) 0+
    rawForm (gaugeField 2 1) p (compositeBase left) (compositeBase right) 0)

/-- Independent-sharp/fullY pairing removes every raised gauge numerator, while preserving both complete response norms. -/
theorem composite_weight_sharp_left (p : PhysicalMomentum) (left right : CompositeLeg)
    (sharp : left.sharp=true) :
    compositeMasslessWeight p left right=
      compositeInverseNorm left*compositeInverseNorm right*compositeBaseWeight p left right := by
  have field21 : fieldUnit (21:Fin 289)=gaugeField 1 0 := rfl
  have field34 : fieldUnit (34:Fin 289)=gaugeField 2 1 := rfl
  have unitL : compositeUnitLeg left=compositeInverseNorm left • compositeResponse left := rfl
  have unitR : compositeUnitLeg right=compositeInverseNorm right • compositeResponse right := rfl
  rw [composite_weight_action,unitL,unitR]
  simp only [raw_smul_left,raw_smul_right]
  rw [inverseNorm_star,field21,field34,composite_sharp_left_gauge p left right sharp,
    composite_sharp_left_gauge p left right sharp]
  unfold compositeBaseWeight
  ring

theorem composite_weight_sharp_right (p : PhysicalMomentum) (left right : CompositeLeg)
    (sharp : right.sharp=true) :
    compositeMasslessWeight p left right=
      compositeInverseNorm left*compositeInverseNorm right*compositeBaseWeight p left right := by
  have field21 : fieldUnit (21:Fin 289)=gaugeField 1 0 := rfl
  have field34 : fieldUnit (34:Fin 289)=gaugeField 2 1 := rfl
  have unitL : compositeUnitLeg left=compositeInverseNorm left • compositeResponse left := rfl
  have unitR : compositeUnitLeg right=compositeInverseNorm right • compositeResponse right := rfl
  rw [composite_weight_action,unitL,unitR]
  simp only [raw_smul_left,raw_smul_right]
  rw [inverseNorm_star,field21,field34,composite_sharp_right_gauge p left right sharp,
    composite_sharp_right_gauge p left right sharp]
  unfold compositeBaseWeight
  ring

/-- The literal full504 charge acts on the original smooth physical core. -/
def compositeChargeCore : Module.End ℂ QuantumTest :=
  localMultiplier (fun _=>quantized PhysicalEMNativeChargeFull.emFullCharge) (fun _=>contDiffAt_const)

theorem composite_input_charge_core (leg : CompositeLeg) :
    compositeChargeCore (compositeInput leg)=(if leg.dual then (-1:ℂ) else 1) • compositeInput leg := by
  apply DFunLike.ext
  intro z
  exact composite_input_em_charge leg z

def compositeResolvent (leg : CompositeLeg) : Module.End ℂ QuantumTest :=
  if leg.sharp then literalSharpResolvent leg.frame leg.energy leg.nonreal
    else literalCoreResolvent leg.frame leg.energy leg.nonreal

private theorem composite_response_resolvent (leg : CompositeLeg) :
    compositeResolvent leg (compositeInput leg)=compositeResponse leg := by
  cases hs : leg.sharp <;>
    simp only [compositeResolvent,compositeResponse,hs,Bool.false_eq_true,if_false,if_true]

def compositeShift (leg : CompositeLeg) : Module.End ℂ QuantumTest :=
  if leg.sharp then literalSharpShift leg.frame leg.energy else literalCoreShift leg.frame leg.energy

private theorem composite_source_equation (leg : CompositeLeg) :
    compositeShift leg (compositeResponse leg)=compositeInput leg := by
  cases hs : leg.sharp
  · simpa only [compositeShift,compositeResponse,hs,Bool.false_eq_true,if_false,
      Module.End.mul_apply,Module.End.one_apply] using
      LinearMap.congr_fun (literal_core_right_inverse leg.frame leg.energy leg.nonreal) (compositeInput leg)
  · simpa only [compositeShift,compositeResponse,hs,if_true,Module.End.mul_apply,Module.End.one_apply] using
      LinearMap.congr_fun (literal_sharp_right_inverse leg.frame leg.energy leg.nonreal) (compositeInput leg)

private theorem composite_left_inverse (leg : CompositeLeg) : compositeResolvent leg*compositeShift leg=1 := by
  cases hs : leg.sharp
  · simpa only [compositeResolvent,compositeShift,hs,Bool.false_eq_true,if_false] using
      literal_core_left_inverse leg.frame leg.energy leg.nonreal
  · simpa only [compositeResolvent,compositeShift,hs,if_true] using
      literal_sharp_left_inverse leg.frame leg.energy leg.nonreal

/-- Output mixing is generated by the original finite-frame Hamiltonian/Y shift and literal fullEM action. -/
def compositeChargeMixing (leg : CompositeLeg) : QuantumTest :=
  (compositeShift leg*compositeChargeCore-compositeChargeCore*compositeShift leg) (compositeResponse leg)

/-- Input EM±1 reaches the complete response with its exact source-generated charge mixing retained. -/
theorem composite_output_charge_return (leg : CompositeLeg) :
    compositeChargeCore (compositeResponse leg)=
      (if leg.dual then (-1:ℂ) else 1) • compositeResponse leg+
        compositeResolvent leg (compositeChargeMixing leg) := by
  have inverse:=LinearMap.congr_fun (composite_left_inverse leg) (compositeChargeCore (compositeResponse leg))
  simp only [Module.End.mul_apply,Module.End.one_apply] at inverse
  calc
    _=compositeResolvent leg (compositeShift leg (compositeChargeCore (compositeResponse leg))) := inverse.symm
    _=compositeResolvent leg (compositeChargeCore (compositeShift leg (compositeResponse leg))+compositeChargeMixing leg) := by
      congr 1
      simp only [compositeChargeMixing,LinearMap.sub_apply,Module.End.mul_apply]
      abel
    _=_ := by
      rw [composite_source_equation,composite_input_charge_core,map_add,map_smul]
      rw [composite_response_resolvent]

/-- The same mixing survives the generated complete-response unit normalization. -/
theorem composite_unit_charge_return (leg : CompositeLeg) :
    compositeChargeCore (compositeUnitLeg leg)=
      (if leg.dual then (-1:ℂ) else 1) • compositeUnitLeg leg+
        compositeInverseNorm leg • compositeResolvent leg (compositeChargeMixing leg) := by
  have unit : compositeUnitLeg leg=compositeInverseNorm leg • compositeResponse leg := rfl
  rw [unit,map_smul,composite_output_charge_return,smul_add,smul_comm]

/-- FullY output charge mixing is exactly the original finite-frame commutator plus the original Yukawa commutator. -/
theorem composite_full_charge_mixing (leg : CompositeLeg) (full : leg.sharp=false) :
    compositeChargeMixing leg=
      SourceScalarPairedTransport.compressionCore leg.frame (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (SourceScalarPairedTransport.compressionCore leg.frame (compositeResponse leg))+
      GaussYukawaOperator.originalAction (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (GaussYukawaOperator.originalAction (compositeResponse leg)) := by
  simp only [compositeChargeMixing,compositeShift,full,Bool.false_eq_true,if_false,literalCoreShift,
    Module.End.mul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.one_apply,map_sub,map_add,map_smul]
  module

theorem composite_sharp_charge_mixing (leg : CompositeLeg) (sharp : leg.sharp=true) :
    compositeChargeMixing leg=
      SourceScalarPairedTransport.compressionCore leg.frame (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (SourceScalarPairedTransport.compressionCore leg.frame (compositeResponse leg))+
      GaussFullHamiltonian.adjointAction (compositeChargeCore (compositeResponse leg))-
        compositeChargeCore (GaussFullHamiltonian.adjointAction (compositeResponse leg)) := by
  simp only [compositeChargeMixing,compositeShift,sharp,if_true,literalSharpShift,
    Module.End.mul_apply,LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.one_apply,map_sub,map_add,map_smul]
  module

/-- The generated normalization contains a strictly positive fullY spectral increment on every original causal band. -/
theorem composite_fullY_norm_excess (F : GaussUnitaryHistory.Index) (dual advanced : Bool)
    (damping : ℝ) (positive : 0<damping) :
    (Real.pi/damping)*(2*‖scalarLp 3 (compositeProfile dual)‖^2)<
      ∫omega : ℝ, ‖GaussCoreHilbert.embed (compositeResponse (compositeCausalLeg F dual false advanced damping positive omega))‖^2 := by
  simpa only [composite_causal_owner,compositeProfile] using
    ((actual_generated_candidate_Y_excess dual).choose_spec.2 F advanced damping positive).2

end LowEnergy.GaussComposite.ActualCompositeGaugeBand
