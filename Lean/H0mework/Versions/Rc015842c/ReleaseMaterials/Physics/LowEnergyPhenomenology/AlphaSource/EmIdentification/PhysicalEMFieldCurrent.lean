import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMChargeReadout
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldCoefficients
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceRestGaugeVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMFieldCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction DiracCliffordRepresentation
open SU7ExteriorBreakingYukawa StageNineDiracDualYukawaSpinJurisdiction SourceQuantumScalarChart
open StageNineDiracDualFormNativeConjugateMatterVariation
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous Stage9DEF
open Stage10 Stage10.CanonicalMatter YangMills.FullPairing FullQuantum FullSpace
open FullQuantum.CoframeResponse FullQuantum.Triangular
open Electromagnetic.CanonicalCoframe Electromagnetic.CanonicalPacket Electromagnetic.ExternalState
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalActualPhaseChargeReturn PreparationPhysicalNativePhaseChargeInventory
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNormalizedFullField
open PreparationVacuumMixedFieldReturn PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldCovector PreparationVacuumLowerClassical PreparationCoordinates
open GaussNativeMatter
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMChargeReadout
open GaussComposite.PhysicalFullFieldScattering
open scoped Matrix BigOperators Topology InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _

/-- The coframe block of every density coefficient vanishes for the zero
    coframe direction, so a pure gauge field has no coframe contribution. -/
private theorem coframeDensityCoefficients_zero (i : Fin 4) :
    coframeDensityCoefficients (0 : LorentzianCoframe) i = 0 := by
  induction i using Fin.cases
  · rw [coframeDensityCoefficients, Fin.cases_zero]
    simp only [densitizedLowerDirection, densitizedPrincipalDirection,
      lowerDirection, principalDirection, volumeDirection,
      map_zero, Complex.ofReal_zero, smul_zero, zero_smul, zero_mul,
      add_zero, sub_self]
  · rename_i j
    rw [coframeDensityCoefficients, Fin.cases_succ]
    simp only [densitySpatialJet, densitizedPrincipalDirection, coefficientJet,
      volumeDirection, principalDirection,
      map_zero, Complex.ofReal_zero, smul_zero, zero_smul, zero_mul,
      add_zero, sub_self]

/-- The electromagnetic gauge field returns the source gauge-density action
    at the temporal slot and zero at the three spatial slots, on the whole
    source matrix space. -/
theorem em_field_density (mu i : Fin 4) :
    fieldDensityCoefficients (sourceField (emGaugeField mu)) i =
      if i = 0 then Quantum.operatorMatrix
        (sourceGaugeDensityAction mu emDirection) else 0 := by
  have dcoframe : (sourceField (emGaugeField mu)).coframe = 0 := by
    change ⇑fieldCoframeLinear (emGaugeField mu) = 0
    rw [emGaugeField, map_sum]
    apply Finset.sum_eq_zero
    intro a _
    simp only [map_smul]
    change _ • fieldCoframe (gaugeField mu a) = 0
    rw [gauge_coframe, smul_zero]
  have dscalar : scalarDirection (sourceField (emGaugeField mu)) = 0 := by
    have scalar : (sourceField (emGaugeField mu)).scalar = 0 := by
      change ⇑fieldScalarLinear (emGaugeField mu) = 0
      rw [emGaugeField, map_sum]
      apply Finset.sum_eq_zero
      intro a _
      simp only [map_smul]
      change _ • fieldScalar (gaugeField mu a) = 0
      rw [gauge_scalar, smul_zero]
    unfold scalarDirection
    rw [scalar]
    simp only [map_zero]
    have zero :=
      diracDualRightChiralYukawaAction_smul (0:ℂ) (0:ExteriorBreakingScalarCarrier)
    simp only [zero_smul] at zero
    rw [zero, map_zero]
  have vol : sourceVolume = (lapse : ℂ) := by
    rw [sourceVolume]
    rw [show actual.coframe 0 = homogeneousCoframe lapse from
      congrFun actual_coframe 0, homogeneousCoframe_det, abs_of_pos lapse_pos]
  have coeff : coefficientMatrix mu (actual.coframe 0) =
      Quantum.operatorMatrix (Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma
          {coframe := homogeneousCoframe lapse, derivative := 0} mu)) := by
    rw [show actual.coframe 0 = homogeneousCoframe lapse from
      congrFun actual_coframe 0]
    rw [coefficientMatrix]
    rw [show ⇑spinCoordinates (inverseCoframeDiracGamma
        {coframe := homogeneousCoframe lapse, derivative := 0} mu) =
      Quantum.operatorMatrix (diracMatrixMatterAction (inverseCoframeDiracGamma
        {coframe := homogeneousCoframe lapse, derivative := 0} mu)) from rfl]
    exact (map_smul Quantum.operatorMatrix.toLinearEquiv _ _).symm
  unfold fieldDensityCoefficients
  by_cases hi : i = 0
  · simp only [if_pos hi]
    rw [dcoframe, coframeDensityCoefficients_zero, zero_add]
    simp only [em_field_connection]
    rw [Finset.sum_eq_single mu
      (fun nu _ hne => by rw [if_neg hne]; exact mul_zero _)
      (fun off => absurd (Finset.mem_univ mu) off)]
    rw [if_pos rfl, coeff, dscalar, add_zero, vol]
    rw [← smul_mul_assoc]
    rw [show (lapse:ℂ) • Quantum.operatorMatrix
        (Complex.I • diracMatrixMatterAction (inverseCoframeDiracGamma
          {coframe := homogeneousCoframe lapse, derivative := 0} mu)) =
      Quantum.operatorMatrix ((lapse:ℂ) • Complex.I • diracMatrixMatterAction
        (inverseCoframeDiracGamma
          {coframe := homogeneousCoframe lapse, derivative := 0} mu)) from
      (map_smul Quantum.operatorMatrix.toLinearEquiv _ _).symm]
    rw [smul_smul]
    rw [show Quantum.operatorMatrix
        (((lapse:ℂ)*Complex.I) • diracMatrixMatterAction
          (inverseCoframeDiracGamma
            {coframe := homogeneousCoframe lapse, derivative := 0} mu)) *
      Quantum.operatorMatrix emGaugeAction =
      Quantum.operatorMatrix
        (((lapse:ℂ)*Complex.I) • diracMatrixMatterAction
          (inverseCoframeDiracGamma
            {coframe := homogeneousCoframe lapse, derivative := 0} mu) *
          emGaugeAction) from
      (map_mul Quantum.operatorMatrix.toRingEquiv _ _).symm]
    rfl
  · simp only [if_neg hi]
    rw [dcoframe, coframeDensityCoefficients_zero, zero_add]

/-- The full fiber coefficients of the electromagnetic gauge field read the
    source gauge-density weight times the canonical density reader of the
    electromagnetic current, on the whole Hilbert space. -/
theorem em_field_coefficients (mu i : Fin 4) :
    fieldCoefficients (sourceField (emGaugeField mu)) i =
      if i = 0 then sourceGaugeDensityWeight mu •
        Electromagnetic.CanonicalPacket.densityReader
          (Stage9DEF.Compatibility.currentAction mu emDirection) else 0 := by
  unfold fieldCoefficients
  by_cases hi : i = 0
  · rw [em_field_density]
    simp only [if_pos hi]
    unfold canonicalMatrixRead
    change operator (phaseInverse * ⇑Quantum.operatorMatrix.toLinearEquiv.symm
        (Quantum.operatorMatrix (sourceGaugeDensityAction mu emDirection))) = _
    rw [show ⇑Quantum.operatorMatrix.toLinearEquiv.symm
        (Quantum.operatorMatrix (sourceGaugeDensityAction mu emDirection)) =
      sourceGaugeDensityAction mu emDirection from
      LinearEquiv.symm_apply_apply _ _]
    rw [sourceGaugeDensityAction_normal]
    change operator (phaseInverse.comp (sourceGaugeDensityWeight mu •
      Stage9DEF.Compatibility.currentAction mu emDirection)) = _
    rw [LinearMap.comp_smul, operator_smul]
    rfl
  · rw [em_field_density]
    simp only [if_neg hi]
    exact map_zero _

/-- The complex coefficient cast agrees with the real scalar action on the
    complex numbers. -/
private theorem coe_smul (r : ℝ) (z : ℂ) : ((r : ℂ)) • z = r • z := by
  rw [smul_eq_mul]
  exact (Complex.real_smul).symm

/-- The gauge-density read is real-linear in the P286 direction: the source
    vertex is a composite of real-linear source maps. -/
private def forcingReadLinear (point : BasePoint) (left right : RestStateIndex)
    (mu : Fin 4) : P286LieBlockData →ₗ[ℝ] ℂ where
  toFun dir := actual.conjugateMatter point
    (canonicalDual (actualRestStatePreparation left)
      (sourceGaugeDensityAction mu dir
        (actualRestStatePreparation right (actual.matter point))))
  map_add' first second := by
    simp only [sourceGaugeDensityAction, p286LieBlockEmbed_add,
      diracExteriorMotherLieAction_add, LinearMap.comp_add,
      LinearMap.add_apply, LinearMap.smul_apply, smul_add, map_add, map_smul]
  map_smul' r dir := by
    show actual.conjugateMatter point
      (canonicalDual (actualRestStatePreparation left)
        (sourceGaugeDensityAction mu (r • dir)
          (actualRestStatePreparation right (actual.matter point)))) =
      r • actual.conjugateMatter point
        (canonicalDual (actualRestStatePreparation left)
          (sourceGaugeDensityAction mu dir
            (actualRestStatePreparation right (actual.matter point))))
    have ssmul : sourceGaugeDensityAction mu (r • dir) =
        (r:ℂ) • sourceGaugeDensityAction mu dir := by
      simp only [sourceGaugeDensityAction, p286LieBlockEmbed_real_smul,
        diracExteriorMotherLieAction_real_smul]
      rw [LinearMap.comp_smul, smul_smul, smul_smul,
        mul_comm (↑lapse * Complex.I) (r:ℂ)]
    rw [ssmul, LinearMap.smul_apply, map_smul, map_smul]
    exact (RCLike.real_smul_eq_coe_smul ..).symm

/-- The electromagnetic forcing read is the literal original 289-dimensional
    forcing covector restricted to the twelve gauge slots and contracted
    against the electromagnetic direction. -/
def emForcingRead (point : BasePoint) (left right : RestStateIndex)
    (mu : Fin 4) : ℂ :=
  ∑ a : Fin 12,
    (rawCoordinates (p286CoordinateEquiv emDirection) a : ℂ) *
      actualRestNativeComplexForcingCovector point left right
        (gaugeSlot mu a)

/-- The restricted forcing covector equals the source gauge-density weight
    times the actual electromagnetic current pairing, on every pair of rest
    states. -/
theorem em_forcing_current (point : BasePoint) (left right : RestStateIndex)
    (mu : Fin 4) :
    emForcingRead point left right mu =
      sourceGaugeDensityWeight mu * actual.conjugateMatter point
        (canonicalDual (actualRestStatePreparation left)
          (Stage9DEF.Compatibility.currentAction mu emDirection
            (actualRestStatePreparation right (actual.matter point)))) := by
  have slot (a : Fin 12) :
      (ActionNormalization.phaseMomentum : ℂ) *
        sourceRestGaugeVertexMixing mu
          (p286CoordinateEquiv.symm (originalUnit a)) left right =
      actual.conjugateMatter point
        (canonicalDual (actualRestStatePreparation left)
          (sourceGaugeDensityAction mu
            (p286CoordinateEquiv.symm (originalUnit a))
            (actualRestStatePreparation right (actual.matter point)))) :=
    (actualRestState_gaugeDensity_mixing mu _ point left right).symm
  have expansion : emDirection =
      ∑ a : Fin 12, rawCoordinates (p286CoordinateEquiv emDirection) a •
        p286CoordinateEquiv.symm (originalUnit a) := by
    have raw := congrArg (⇑p286CoordinateEquiv.symm)
      (raw_original_expansion (p286CoordinateEquiv emDirection))
    rw [LinearEquiv.symm_apply_apply] at raw
    rw [map_sum] at raw
    simp only [map_smul] at raw
    exact raw
  have collect : ∑ a : Fin 12,
      rawCoordinates (p286CoordinateEquiv emDirection) a •
        forcingReadLinear point left right mu
          (p286CoordinateEquiv.symm (originalUnit a)) =
      forcingReadLinear point left right mu emDirection := by
    calc ∑ a : Fin 12,
        rawCoordinates (p286CoordinateEquiv emDirection) a •
          forcingReadLinear point left right mu
            (p286CoordinateEquiv.symm (originalUnit a))
        = ∑ a : Fin 12,
          forcingReadLinear point left right mu
            (rawCoordinates (p286CoordinateEquiv emDirection) a •
              p286CoordinateEquiv.symm (originalUnit a)) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (LinearMap.map_smul _ _ _).symm
      _ = forcingReadLinear point left right mu
          (∑ a : Fin 12,
            rawCoordinates (p286CoordinateEquiv emDirection) a •
              p286CoordinateEquiv.symm (originalUnit a)) :=
        (map_sum _ _ _).symm
      _ = forcingReadLinear point left right mu emDirection :=
        congrArg _ expansion.symm
  unfold emForcingRead
  simp only [actualRestNativeComplexForcingCovector_gaugeSlot, slot]
  change ∑ a : Fin 12,
    (rawCoordinates (p286CoordinateEquiv emDirection) a : ℂ) *
      forcingReadLinear point left right mu
        (p286CoordinateEquiv.symm (originalUnit a)) = _
  simp only [← smul_eq_mul, coe_smul]
  rw [collect]
  change actual.conjugateMatter point
    (canonicalDual (actualRestStatePreparation left)
      (sourceGaugeDensityAction mu emDirection
        (actualRestStatePreparation right (actual.matter point)))) = _
  rw [sourceGaugeDensityAction_normal, LinearMap.smul_apply, map_smul,
    map_smul]

/-- The temporal forcing read on the charged source restriction is the source
    phase momentum times the generated column charge, `1` on the charged edge
    and `0` on the neutral edge. -/
theorem em_forcing_temporal_unit (side edge : Fin 2) :
    emForcingRead 0 (sourceChargedRestIndex side edge)
      (sourceChargedRestIndex side edge) 0 =
      (ActionNormalization.phaseMomentum : ℂ) *
        (sourceActualPhaseCharge edge : ℂ) := by
  have weight : sourceGaugeDensityWeight (0 : Fin 4) = 1 := rfl
  have state_prep : operator
        (actualRestStatePreparation (sourceChargedRestIndex side edge))
        (YangMills.FullPairing.prepared 0) =
      naturalCoordinates (sourceChargedRestriction side edge) := by
    rw [actualRestState_full_prepared]
    exact congrArg naturalCoordinates
      (show Stage9DEF.Compatibility.embed
          (actualRestStateCoordinates 0 (sourceChargedRestIndex side edge)) =
        sourceChargedRestriction side edge from
        (actualRestState_source 0 _).symm)
  have opX : operator (phaseInverse.comp
        ((Stage9DEF.Compatibility.currentAction 0 emDirection).comp
          (actualRestStatePreparation (sourceChargedRestIndex side edge))))
        (YangMills.FullPairing.prepared 0) =
      (sourceActualPhaseCharge edge : ℂ) •
        naturalCoordinates (sourceChargedRestriction side edge) := by
    have maker := em_charge_maker side edge
    conv_lhs at maker => rw [← state_prep]
    unfold emChargeFiber Electromagnetic.CanonicalPacket.densityReader at maker
    rw [show operator (phaseInverse.comp
          (Stage9DEF.Compatibility.currentAction 0 emDirection))
          (operator (actualRestStatePreparation
            (sourceChargedRestIndex side edge))
            (YangMills.FullPairing.prepared 0)) =
        operator (phaseInverse.comp
          ((Stage9DEF.Compatibility.currentAction 0 emDirection).comp
            (actualRestStatePreparation
              (sourceChargedRestIndex side edge))))
          (YangMills.FullPairing.prepared 0) by
      rw [← mul_apply_eq_comp, ← operator_mul]
      change operator ((phaseInverse.comp
          (Stage9DEF.Compatibility.currentAction 0 emDirection)).comp
        (actualRestStatePreparation (sourceChargedRestIndex side edge)))
          (YangMills.FullPairing.prepared 0) = _
      rw [LinearMap.comp_assoc]] at maker
    exact maker
  have unit_inner : inner ℂ
      (naturalCoordinates (sourceChargedRestriction side edge))
      (naturalCoordinates (sourceChargedRestriction side edge)) = 1 := by
    rw [← state_prep, actualRestState_orthonormal, if_pos rfl]
  rw [em_forcing_current, weight, one_mul,
    Electromagnetic.ExternalState.original_prepared_vertex,
    state_prep, opX, inner_smul_right, unit_inner, mul_one,
    ActionNormalization.phaseMomentum_source]
  push_cast
  ring
