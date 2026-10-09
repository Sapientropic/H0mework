import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeFields
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginMatterPhase
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseChargeProjection

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMGaugeRealization
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracExteriorMatterAction DiracCliffordRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePhaseChargeInventory
open PreparationVacuumGaugeSourceInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumLowerClassical PreparationCoordinates GaussNativeMatter
open YangMills.FullPairing SourceQuantumScalarChart Stage10.CanonicalMatter
open Stage9DEF.Compatibility Electromagnetic.CanonicalCoframe
open Stage10 StageNineP286GaugeConnectionVariation SU7ExteriorMatterRestriction
open SourcePropagationNativeActionHessian StageNineLorentzConnectionVariationDensity
open StageNineLorentzConnectionVariation PreparationPhysicalNativePoleChargeReturn
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The electromagnetic block is the literal source colour generator `2`
    corrected by half of the actual hypercharge direction — a fixed
    source-generated direction, not a chosen axis. -/
def emDirection : P286LieBlockData :=
  -(sourceColorP286Generator 2)-(1/2:ℝ) • HyperchargeResponse.chargeDirection

/-- The gauge action of the electromagnetic direction on the whole
    252-state mother carrier. -/
def emGaugeAction : YangMills.FullPairing.Mother :=
  diracExteriorMotherLieAction (p286LieBlockEmbed emDirection)

/-- The remaining full-matter defect: the source generator differs from the
    gauge block by exactly `½·(TY − i·id)` on the entire carrier. -/
def emFullDefect : YangMills.FullPairing.Mother :=
  (1/2:ℂ) • (diracExteriorMotherLieAction
    (p286LieBlockEmbed HyperchargeResponse.chargeDirection)-
      Complex.I • (LinearMap.id : YangMills.FullPairing.Mother))

private theorem emla_zero : diracExteriorMotherLieAction 0 = 0 := by
  apply LinearMap.ext
  intro v
  exact StageNineP286GaugeConnectionVariationDensity.diracExteriorMotherLieAction_zero_matrix v

private theorem emla_neg (matrix : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (-matrix) =
      -diracExteriorMotherLieAction matrix := by
  rw [show (-matrix) = (-1:ℝ) • matrix from (neg_one_smul ℝ matrix).symm]
  rw [diracExteriorMotherLieAction_real_smul]
  push_cast
  module

private theorem emla_sub (first second : SU7MotherLieMatrix) :
    diracExteriorMotherLieAction (first-second) =
      diracExteriorMotherLieAction first-diracExteriorMotherLieAction second := by
  rw [sub_eq_add_neg, diracExteriorMotherLieAction_add, emla_neg]
  module

/-- The literal original generator `X` is gauge block plus defect, on the
    entire 252-state carrier. -/
theorem original_generator_gauge :
    sourceNativeOriginGenerator = emGaugeAction + emFullDefect := by
  rw [emGaugeAction, emDirection, emFullDefect, sourceNativeOriginGenerator]
  rw [p286LieBlockEmbed_sub, p286LieBlockEmbed_neg,
    p286LieBlockEmbed_real_smul, emla_sub, emla_neg,
    diracExteriorMotherLieAction_real_smul]
  push_cast
  module

/-- The literal source primal phase is the sum of the two real operator
    legs — the defect is not discarded on the actual matter. -/
theorem origin_actual_primal_em (point : BasePoint) :
    diracMatrixMatterAction (ActiveGauge.rotation point)
        (primalInsertion (sourceNativeOriginReal 0)) =
      emGaugeAction (actual.matter point)+emFullDefect (actual.matter point) := by
  rw [sourceNativeOrigin_actualMatter, original_generator_gauge,
    LinearMap.add_apply]

/-- The repaired independent dual is contragredient to the same gauge-block
    plus defect decomposition, preserving the original minus sign. -/
theorem origin_actual_dual_em (point : BasePoint) :
    (dualInsertion (sourceNativeOriginReal 0)).comp
        (diracMatrixMatterAction (ActiveGauge.rotation point)) =
      -(actual.conjugateMatter point).comp (emGaugeAction + emFullDefect) := by
  rw [sourceNativeOrigin_actualDual, original_generator_gauge]

/-- The exterior weight of the two-element colour doublet basis index is
    `1`, by the public exterior charge law on the actual degree-2 index. -/
private theorem doublet_hypercharge_eigen (state : Fin 2) :
    exteriorSpinorMotherLieAction
        (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
        (sourceColorDoubletMatter state) =
      Complex.I • sourceColorDoubletMatter state := by
  have weight : exteriorHyperchargeWeight (sourceColorDoubletIndex state) = 1 := by
    fin_cases state <;> decide
  simp [sourceColorDoubletMatter, exteriorSpinorMotherLieAction,
    HyperchargeResponse.exterior_charge_basis, weight]

/-- The defect vanishes exactly on the source-embedded carrier: there the
    hypercharge leg already contributes `i·id`. This says nothing about
    the rest of the 252-state carrier. -/
theorem em_defect_embedded (values : Stage9DEF.Source.Index → ℂ) :
    emFullDefect (Stage9DEF.Compatibility.embed values) = 0 := by
  have eigen : diracExteriorMotherLieAction
      (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (embed values) = Complex.I • embed values := by
    funext spin
    change exteriorSpinorMotherLieAction
        (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
        (∑ color : Fin 2, values (spin, color) • sourceColorDoubletMatter color) =
      Complex.I •
        (∑ color : Fin 2, values (spin, color) • sourceColorDoubletMatter color)
    simp only [map_sum, map_smul, doublet_hypercharge_eigen, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro color _
    exact smul_comm _ _ _
  rw [emFullDefect]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    eigen]
  rw [sub_self, smul_zero]

/-- The degree-2 colour-neutral doublet used to certify that the defect is
    a real nonzero operator: its two indices carry hypercharge weight `0`,
    so the hypercharge leg vanishes on it while `-i/2·id` does not. -/
private def defectIndex : ExteriorBasisIndex 2 :=
  ⟨{Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)}, by
    change ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} : Finset SU7MotherIndex).card = 2
    simp⟩

private def defectVector : DiracExteriorMatterCarrier :=
  fun spin => if spin = 0 then (0, su7ExteriorBasis 2 defectIndex, 0) else 0

private theorem defect_weight_zero : exteriorHyperchargeWeight defectIndex = 0 := by
  simp [defectIndex, exteriorHyperchargeWeight, fundamentalHyperchargeWeight]

private theorem defect_hypercharge_action :
    diracExteriorMotherLieAction
        (p286LieBlockEmbed HyperchargeResponse.chargeDirection) defectVector = 0 := by
  funext spin
  change exteriorSpinorMotherLieAction
      (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (defectVector spin) = 0
  unfold exteriorSpinorMotherLieAction
  simp only [defectVector]
  by_cases same : spin = 0
  · rw [if_pos same, LinearMap.prodMap_apply, map_zero,
      LinearMap.prodMap_apply, map_zero,
      HyperchargeResponse.exterior_charge_basis, defect_weight_zero]
    simp
  · rw [if_neg same, map_zero]

/-- The defect is a genuine nonzero operator on the full carrier; only on
    the actual source embedding does it vanish. -/
theorem em_defect_nonzero : emFullDefect ≠ 0 := by
  intro vanish
  have applied : emFullDefect defectVector = 0 := by
    rw [vanish]
    rfl
  have value : ((emFullDefect defectVector) 0).2.1 =
      -(Complex.I/2) • su7ExteriorBasis 2 defectIndex := by
    simp only [emFullDefect, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    rw [defect_hypercharge_action]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, defectVector,
      ↓reduceIte]
    change ((1/2:ℂ) • (0-Complex.I • su7ExteriorBasis 2 defectIndex)) =
      -(Complex.I/2) • su7ExteriorBasis 2 defectIndex
    rw [zero_sub, smul_neg, smul_smul, ← neg_smul]
    congr 1
    ring
  have proj : ((emFullDefect defectVector) 0).2.1 = 0 := by
    have h := congrFun applied 0
    rw [h]
    rfl
  rw [value] at proj
  have scalar : (-(Complex.I/2) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero Complex.I_ne_zero (by norm_num))
  exact (su7ExteriorBasis 2).linearIndependent.ne_zero defectIndex
    ((smul_eq_zero.mp proj).resolve_left scalar)

/-- The four-current generator of the literal source generator `X`. -/
def originCurrentAction (mu : Fin 4) : YangMills.FullPairing.Mother :=
  Complex.I • (diracMatrixMatterAction (diracGamma mu)).comp sourceNativeOriginGenerator

/-- The same current read on the full defect leg only. -/
def emCurrentDefect (mu : Fin 4) : YangMills.FullPairing.Mother :=
  Complex.I • (diracMatrixMatterAction (diracGamma mu)).comp emFullDefect

/-- The literal current is gauge-block current plus defect current, with
    the complete 252-state difference retained. -/
theorem em_current_full (mu : Fin 4) :
    originCurrentAction mu =
      Stage9DEF.Compatibility.currentAction mu emDirection+emCurrentDefect mu := by
  rw [originCurrentAction, emCurrentDefect, original_generator_gauge]
  apply LinearMap.ext
  intro v
  simp only [Stage9DEF.Compatibility.currentAction, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_add]
  rw [show emGaugeAction =
      diracExteriorMotherLieAction (p286LieBlockEmbed emDirection) from rfl]
  rw [smul_add]

/-- The temporal current of the original generator is the already-paid
    source phase Noether insertion. -/
theorem origin_temporal_current :
    originCurrentAction 0 = sourcePhaseNoether := by
  rw [originCurrentAction]
  unfold sourcePhaseNoether
  rfl

/-- After the phase inverse the electromagnetic density fiber is `I·eA`. -/
theorem em_phase_current :
    phaseInverse.comp
        (Stage9DEF.Compatibility.currentAction 0 emDirection) =
      Complex.I • emGaugeAction := by
  apply LinearMap.ext
  intro v
  simp only [Stage9DEF.Compatibility.currentAction, LinearMap.comp_apply,
    LinearMap.smul_apply, map_smul, diracGamma, Matrix.cons_val_zero]
  rw [phase_inverse_source]
  rw [show emGaugeAction =
      diracExteriorMotherLieAction (p286LieBlockEmbed emDirection) from rfl]

/-- After the phase inverse the defect current fiber is `I·D`. -/
theorem em_phase_defect :
    phaseInverse.comp (emCurrentDefect 0) = Complex.I • emFullDefect := by
  apply LinearMap.ext
  intro v
  simp only [emCurrentDefect, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, diracGamma, Matrix.cons_val_zero]
  rw [phase_inverse_source]

/-- On the source embedding the literal current is the gauge current
    because the defect vanishes. -/
theorem em_current_embedded (mu : Fin 4) (values : Stage9DEF.Source.Index → ℂ) :
    originCurrentAction mu (Stage9DEF.Compatibility.embed values) =
      Stage9DEF.Compatibility.currentAction mu emDirection
        (Stage9DEF.Compatibility.embed values) := by
  rw [em_current_full, LinearMap.add_apply, emCurrentDefect,
    LinearMap.smul_apply, LinearMap.comp_apply, em_defect_embedded,
    map_zero, smul_zero, add_zero]

/-- The electromagnetic gauge field: the source direction expanded in the
    original twelve gauge slots. -/
def emGaugeField (mu : Fin 4) : Field289 :=
  ∑ a : Fin 12,(rawCoordinates (p286CoordinateEquiv emDirection) a:ℝ) •
    gaugeField mu a

/-- The gauge block of the source field is the electromagnetic direction on
    the diagonal and zero elsewhere. -/
theorem em_field_gauge (mu nu : Fin 4) :
    (sourceField (emGaugeField mu)).gauge nu =
      if nu = mu then emDirection else 0 := by
  have eval : fieldGauge (emGaugeField mu) nu =
      if nu = mu then p286CoordinateEquiv emDirection else 0 := by
    simp only [fieldGauge, emGaugeField, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, gauge_gauge_slot]
    by_cases same : nu = mu
    · subst nu
      simp only [true_and, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      exact (raw_original_expansion (p286CoordinateEquiv emDirection)).symm
    · simp only [same, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero,
        zero_smul]
  change p286CoordinateEquiv.symm (fieldGauge (emGaugeField mu) nu) = _
  rw [eval]
  split_ifs with hsplit
  · exact LinearEquiv.symm_apply_apply _ _
  · exact map_zero _

private theorem dmma_zero : diracMatrixMatterAction (0 : DiracMatrix) = 0 := by
  apply LinearMap.ext
  intro v
  exact diracMatrixMatterAction_zero_matrix v

/-- The connection direction of the source field is the literal gauge
    mother action on the diagonal and zero elsewhere. -/
theorem em_field_connection (mu nu : Fin 4) :
    connectionDirection (sourceField (emGaugeField mu)) nu =
      if nu = mu then Quantum.operatorMatrix emGaugeAction else 0 := by
  have lorentz : (sourceField (emGaugeField mu)).lorentz = 0 := by
    ext a b
    change fieldLorentz (emGaugeField mu) a b = (0 : LorentzBivectorOneForm) a b
    simp only [fieldLorentz, emGaugeField, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    rw [Finset.sum_eq_zero]
    intro c _
    have slot : (gaugeField mu c) (lorentzSlot a b) = 0 := by
      have h := congrFun (congrFun (gauge_lorentz mu c) a) b
      simpa [fieldLorentz] using h
    rw [slot, mul_zero]
  unfold connectionDirection
  rw [lorentz, lorentzSkewConnectionOfBivectorOneForm_zero,
    diracSpinConnectionLift_zero, dmma_zero, zero_add, em_field_gauge]
  split_ifs with hsplit
  · subst nu
    rfl
  · rw [p286LieBlockEmbed_zero, emla_zero]
    exact map_zero Quantum.operatorMatrix.toRingEquiv

end LowEnergy.GaussComposite.PhysicalEMGaugeRealization
