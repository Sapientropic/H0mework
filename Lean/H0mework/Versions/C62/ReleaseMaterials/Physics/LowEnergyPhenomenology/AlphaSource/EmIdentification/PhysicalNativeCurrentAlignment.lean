import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldCoefficients
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalFullFieldRestReadout
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFieldEnergyAxes
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChannelTwoSpinPort

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalNativeCurrentAlignment
open PreparationVacuumElectromagneticIdentity PreparationVacuumMixedFieldReturn
open PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace HistoryPrepared
open CoframeResponse StateGreen
open Stage10.ChargedPreparation Stage10.CanonicalMatter Stage9C.Material.SpinPair
open YangMills.FullPairing Stage9DEF Stage9DEF.Compatibility Stage10
open Electromagnetic.CanonicalCoframe Electromagnetic.ExternalState
open LowEnergy.GaussComposite.PhysicalFullFieldScattering
open DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SU7ExteriorMatterRestriction SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open Filter
open scoped Matrix BigOperators Topology InnerProductSpace
local instance : DecidableEq Quantum.Index := Classical.decEq _

/-- The Dirac matrix-matter action is ℂ-linear in its matrix argument; the
    pointwise generated facts are lifted once to the endomorphism level. -/
private def diracMatterCLinear :
    DiracMatrix →ₗ[ℂ] YangMills.FullPairing.Mother where
  toFun := diracMatrixMatterAction
  map_add' A B := LinearMap.ext fun v =>
    StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_add_matrix
      A B v
  map_smul' a M := LinearMap.ext fun v =>
    StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_smul_matrix
      a M v

/-- `operator` is ℂ-linear in the mother action. -/
private theorem operator_smul (a : ℂ) (M : YangMills.FullPairing.Mother) :
    YangMills.FullPairing.operator (a • M) =
      a • YangMills.FullPairing.operator M := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [YangMills.FullPairing.operator,
    LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    LinearMap.smul_apply, smul_apply, map_smul]

/-- The carrier `•` is a `Function.hasSMul`/`Prod.instSMul`-derived instance,
    so the generic `neg_smul`/`neg_one_smul` rewrites do not match it
    syntactically; apply them in term mode instead. -/
private theorem carrier_neg_one_smul (v : DiracExteriorMatterCarrier) :
    (-1 : ℂ) • v = -v :=
  (neg_smul (1 : ℂ) v).trans (congrArg Neg.neg (one_smul ℂ v))

/-- Same instance obstacle for `DiracMatrix`-valued scalars. -/
private theorem dirac_neg_smul (a : ℂ) (X : DiracMatrix) :
    (-a) • X = -(a • X) := neg_smul a X

/-- The `i = 2` native first-jet axis of the generated energy channel, taken
    directly from the source axis field. -/
def nativeAxisField (k : Fin 4) : Field289 := sourceEnergyAxisField 2 k

/-- The axis is not a hand-fit table: it is the literal third channel of the
    original charged native frame jet, generated from the complete inverse. -/
theorem native_axis_original_frame (k : Fin 4) :
    (fun row => (nativeAxisField k row : ℂ)) =
      fun row => PreparationVacuumPhysicalChargedFieldFactor.sourceChargedNativeFrameJet
        (Pi.single k (1 : ℂ)) row (2 : Fin 289) := by
  have values : (fun j => ((Pi.single k (1 : ℝ) : Fin 4 → ℝ) j : ℂ)) =
      Pi.single k (1 : ℂ) := by
    funext j
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  funext row
  rw [show ((nativeAxisField k row : ℂ)) = ((sourceEnergyAxisField 2 k) row : ℂ) from rfl]
  rw [congrFun (sourceEnergyAxisField_cast 2 k) row]
  have ent := sourceEnergyChannelMatrix_entry
    (fun j => ((Pi.single k (1 : ℝ) : Fin 4 → ℝ) j : ℂ)) row (2 : Fin 3)
  rw [values] at ent
  exact ent

/-- The Hamiltonian vertex of the channel-two axis in original Clifford-matrix
    normal form, read off `sourceChannelTwoSpin_normal` rather than fit. -/
def nativeSpinVertex (k : Fin 4) : DiracMatrix :=
  (Complex.I*((Pi.single k (1 : ℝ) : Fin 4 → ℝ) 0 : ℂ)) • (1 : DiracMatrix)-
    (Complex.I*(Real.sqrt 30 : ℂ)/5) •
      (∑ j : Fin 3, ((Pi.single k (1 : ℝ) : Fin 4 → ℝ) j.succ : ℂ) •
        (diracGammaZero*diracGamma j.succ))

/-- On the third channel the coframe jet vanishes, so every coframe density
    coefficient at the zero coframe is zero. -/
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

/-- The `i = 0` Hamiltonian density coefficient of the third-channel axis is
    exactly the original spin-connection Hamiltonian of the Clifford vertex. -/
theorem native_axis_hamiltonian (k : Fin 4) :
    fieldHamiltonianCoefficients (sourceField (nativeAxisField k)) 0 =
      spinCoordinates (nativeSpinVertex k) := by
  have dcoframe : (sourceField (nativeAxisField k)).coframe = 0 :=
    (sourceEnergyAxisField_two_bosonic k).1
  have dscalar : (sourceField (nativeAxisField k)).scalar = 0 :=
    (sourceEnergyAxisField_two_bosonic k).2.2
  have dlorentz : (sourceField (nativeAxisField k)).lorentz =
      sourceChannelTwoLorentz (Pi.single k 1) :=
    sourceEnergyAxisField_two_lorentz k
  have dconn : ∀ mu : Fin 4,
      connectionDirection (sourceField (nativeAxisField k)) mu =
        spinCoordinates (sourceChannelTwoSpinConnection
          (fun j => ((Pi.single k (1 : ℝ) : Fin 4 → ℝ) j : ℂ)) mu) := by
    intro mu
    rw [connectionDirection, dlorentz, sourceChannelTwoDiracConnection_generated]
    rw [show (sourceField (nativeAxisField k)).gauge mu =
        p286CoordinateEquiv.symm (fieldGauge (nativeAxisField k) mu) from rfl]
    rw [show fieldGauge (nativeAxisField k) mu = 0 from
      (sourceEnergyAxisField_two_bosonic k).2.1 mu]
    rw [show p286CoordinateEquiv.symm (0 : P286CoordinateCarrier) = 0 from map_zero _]
    rw [show p286LieBlockEmbed (0 : P286LieBlockData) = 0 from
      map_zero p286EmbedLinear]
    rw [show diracExteriorMotherLieAction (0 : SU7MotherLieMatrix) = 0 from
      map_zero diracMotherLieLinear]
    rw [add_zero]
    rfl
  have dscalardir : scalarDirection (sourceField (nativeAxisField k)) = 0 := by
    rw [scalarDirection, dscalar]
    rw [show scalarCoordinateEquiv.symm (0 : ScalarCoordinateCarrier) = 0 from
      map_zero _]
    rw [show diracDualRightChiralYukawaAction 0 = 0 from
      map_zero diracYukawaLinear]
    exact map_zero _
  have volne : sourceVolume ≠ 0 := by
    rw [sourceVolume]
    exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (actual_coframe_nondegenerate 0))
  rw [fieldHamiltonianCoefficients, fieldDensityCoefficients, if_pos rfl]
  rw [dcoframe, coframeDensityCoefficients_zero, zero_add, dscalardir, add_zero]
  simp only [dconn]
  rw [Matrix.mul_smul, smul_smul]
  rw [show (-Complex.I*sourceVolume⁻¹)*sourceVolume = -Complex.I from by
    rw [mul_assoc, inv_mul_cancel₀ volne, mul_one]]
  rw [sourceSpinConnectionHamiltonian_original, sourceChannelTwoSpin_normal]
  rw [nativeSpinVertex]

/-- The frequency leg of the axis is the operator image of the Clifford
    vertex, through the source inverse-principal read. -/
theorem native_axis_frequency (k : Fin 4) :
    frequencyCoefficients (sourceField (nativeAxisField k)) 0 =
      operator (diracMatrixMatterAction (nativeSpinVertex k)) := by
  rw [frequencyCoefficients, native_axis_hamiltonian]
  congr 1
  change Quantum.operatorMatrix.toLinearEquiv.symm
      (Quantum.operatorMatrix (diracMatrixMatterAction (nativeSpinVertex k))) = _
  exact LinearEquiv.symm_apply_apply _ _

/-- The canonical-Y current weight of channel `k`: the time component is
    normalized to `1`, the three spatial axes carry the source `√30/5`. -/
def nativeCurrentWeight (k : Fin 4) : ℂ :=
  if k = 0 then 1 else (Real.sqrt 30 : ℂ)/5

/-- The current reader is the original `I`-shifted frequency coefficient of
    the third-channel axis on the source field carrier. -/
def nativeCurrentReader (k : Fin 4) : FiberOperators :=
  Complex.I • frequencyCoefficients (sourceField (nativeAxisField k)) 0

/-- The current reader is the pure `γ⁰γᵏ` mother action with the fixed source
    weight, on all exterior Hilbert data; no eight-state premise enters. -/
theorem native_current_spin (k : Fin 4) :
    nativeCurrentReader k =
      nativeCurrentWeight k •
        operator (diracMatrixMatterAction (diracGammaZero*diracGamma k)) := by
  have vertex : Complex.I • nativeSpinVertex k =
      nativeCurrentWeight k • (diracGammaZero*diracGamma k) := by
    have hcoeff : Complex.I*(Complex.I*(Real.sqrt 30 : ℂ)/5) =
        -((Real.sqrt 30 : ℂ)/5) := by
      rw [div_eq_mul_inv, ← mul_assoc, ← mul_assoc, Complex.I_mul_I,
        neg_one_mul]
      ring
    fin_cases k <;>
      simp [nativeSpinVertex, nativeCurrentWeight, Pi.single_apply,
        Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        diracGamma] <;>
      first
        | rw [smul_smul, Complex.I_mul_I, neg_one_smul]
        | rw [smul_smul, hcoeff, dirac_neg_smul, neg_neg]
  rw [nativeCurrentReader, native_axis_frequency, ← operator_smul]
  rw [show Complex.I • diracMatrixMatterAction (nativeSpinVertex k) =
      diracMatrixMatterAction (Complex.I • nativeSpinVertex k) from
      (diracMatterCLinear.map_smul Complex.I (nativeSpinVertex k)).symm]
  rw [vertex]
  rw [show diracMatrixMatterAction
        (nativeCurrentWeight k • (diracGammaZero*diracGamma k)) =
      nativeCurrentWeight k •
        diracMatrixMatterAction (diracGammaZero*diracGamma k) from
      diracMatterCLinear.map_smul _ _]
  rw [operator_smul]

/-- The hypercharge generator acts as `I` on every doublet state; the weight
    of the two-element basis is `1` by the public exterior charge law. -/
private theorem doublet_hypercharge_eigen (state : Fin 2) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (sourceColorDoubletMatter state) = Complex.I • sourceColorDoubletMatter state := by
  have weight : exteriorHyperchargeWeight (sourceColorDoubletIndex state) = 1 := by
    fin_cases state <;> decide
  simp [sourceColorDoubletMatter, exteriorSpinorMotherLieAction,
    HyperchargeResponse.exterior_charge_basis, weight]

/-- The hypercharge generator acts as `I` on every embedded source value, on
    the full source index carrier — not only on the canonical packet. -/
private theorem source_hypercharge_eigen (values : Stage9DEF.Source.Index → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (embed values) = Complex.I • embed values := by
  funext spin
  change exteriorSpinorMotherLieAction (p286LieBlockEmbed HyperchargeResponse.chargeDirection)
    (∑ color : Fin 2, values (spin, color) • sourceColorDoubletMatter color) =
      Complex.I • (∑ color : Fin 2, values (spin, color) • sourceColorDoubletMatter color)
  simp only [map_sum, map_smul, doublet_hypercharge_eigen, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro color _
  exact smul_comm _ _ _

/-- On source-embedded values the canonical density reader of the Y current is
    exactly the `γ⁰γμ` mother action: the charge eigen and the phase-inverse
    leg compose to the bounded carrier law. -/
private theorem native_density_reader_source (mu : Fin 4)
    (values : Stage9DEF.Source.Index → ℂ) :
    Electromagnetic.CanonicalPacket.densityReader
        (Compatibility.currentAction mu HyperchargeResponse.chargeDirection)
        (naturalCoordinates (embed values)) =
      operator (diracMatrixMatterAction (diracGammaZero*diracGamma mu))
        (naturalCoordinates (embed values)) := by
  rw [Electromagnetic.CanonicalPacket.densityReader,
    YangMills.FullPairing.operator_coordinates,
    YangMills.FullPairing.operator_coordinates]
  congr 1
  rw [LinearMap.comp_apply, Compatibility.currentAction, LinearMap.smul_apply,
    LinearMap.comp_apply, source_hypercharge_eigen]
  simp only [map_smul, smul_smul, Complex.I_mul_I]
  change (-1 : ℂ)•
      (-(diracMatrixMatterAction diracGammaZero
        (diracMatrixMatterAction (diracGamma mu) (embed values)))) =
    diracMatrixMatterAction (diracGammaZero*diracGamma mu) (embed values)
  rw [carrier_neg_one_smul, neg_neg]
  rw [SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul,
    LinearMap.comp_apply]

/-- The `operator`-image of a preparation followed by an action agrees with
    the composed mother action on the prepared point. -/
private theorem operator_prepared_comp (M : YangMills.FullPairing.Mother)
    (state : RestStateIndex) :
    operator M (operator (actualRestStatePreparation state)
        (YangMills.FullPairing.prepared 0)) =
      operator (M.comp (actualRestStatePreparation state))
        (YangMills.FullPairing.prepared 0) := by
  rw [YangMills.FullPairing.prepared]
  repeat rw [YangMills.FullPairing.operator_coordinates]
  rw [LinearMap.comp_apply]

/-- On every one of the eight generated rest states the native current reader
    is `w_k` times the canonical density reader of the `k`-th Y current. -/
theorem native_current_prepared (k : Fin 4) (state : RestStateIndex) :
    nativeCurrentReader k
        (operator (actualRestStatePreparation state)
          (YangMills.FullPairing.prepared 0)) =
      nativeCurrentWeight k •
        Electromagnetic.CanonicalPacket.densityReader
          (Compatibility.currentAction k HyperchargeResponse.chargeDirection)
          (operator (actualRestStatePreparation state)
            (YangMills.FullPairing.prepared 0)) := by
  rw [native_current_spin, smul_apply]
  rw [actualRestState_full_prepared]
  rw [native_density_reader_source]

/-- Bilateral eight-state Noether: the current reader pairing between any two
    generated rest states equals the source weight times the action scale
    times the original Lagrangian vertex. Off-diagonal included. -/
theorem native_current_noether (k : Fin 4) (left right : RestStateIndex) :
    inner ℂ
      (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared 0))
      (nativeCurrentReader k
        (operator (actualRestStatePreparation right) (YangMills.FullPairing.prepared 0))) =
      nativeCurrentWeight k*(Stage10.ActionNormalization.actionScale : ℂ)*
        actual.conjugateMatter 0
          (canonicalDual (actualRestStatePreparation left)
            (Compatibility.currentAction k HyperchargeResponse.chargeDirection
              (actualRestStatePreparation right (actual.matter 0)))) := by
  rw [native_current_prepared]
  rw [inner_smul_right]
  have step :
      Electromagnetic.CanonicalPacket.densityReader
        (Compatibility.currentAction k HyperchargeResponse.chargeDirection)
        (operator (actualRestStatePreparation right)
          (YangMills.FullPairing.prepared 0)) =
      operator
        (Stage10.CanonicalMatter.phaseInverse.comp
          ((Compatibility.currentAction k HyperchargeResponse.chargeDirection).comp
            (actualRestStatePreparation right)))
        (YangMills.FullPairing.prepared 0) := by
    rw [Electromagnetic.CanonicalPacket.densityReader,
      operator_prepared_comp, LinearMap.comp_assoc]
  rw [step]
  have vertex := Electromagnetic.ExternalState.original_prepared_vertex 0
    (actualRestStatePreparation left) (actualRestStatePreparation right)
    (Compatibility.currentAction k HyperchargeResponse.chargeDirection)
  have ne : (4*(spinScale : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr spinScale_pos.ne')
  apply_fun ((4*(spinScale : ℂ))⁻¹ * ·) at vertex
  rw [← mul_assoc, inv_mul_cancel₀ ne, one_mul] at vertex
  have hinv :
      inner ℂ
        (operator (actualRestStatePreparation left) (YangMills.FullPairing.prepared 0))
        (operator
          (Stage10.CanonicalMatter.phaseInverse.comp
            ((Compatibility.currentAction k HyperchargeResponse.chargeDirection).comp
              (actualRestStatePreparation right)))
          (YangMills.FullPairing.prepared 0)) =
      (Stage10.ActionNormalization.actionScale : ℂ)*
        actual.conjugateMatter 0
          (canonicalDual (actualRestStatePreparation left)
            (Compatibility.currentAction k HyperchargeResponse.chargeDirection
              (actualRestStatePreparation right (actual.matter 0)))) := by
    rw [← vertex]
    rw [show (Stage10.ActionNormalization.actionScale : ℂ) =
        (4*(spinScale : ℂ))⁻¹ from by
      rw [Stage10.ActionNormalization.actionScale_source]
      push_cast
      ring]
  rw [hinv]
  ring

/-- The temporal component of the native current on the certified rest state
    is the canonical charge `-1`. -/
theorem native_current_rest_temporal :
    inner ℂ PhysicalFullFieldRestReadout.restState
      (nativeCurrentReader 0 PhysicalFullFieldRestReadout.restState) = -1 := by
  have hp := native_current_prepared 0 (0, 0)
  have hr : PhysicalFullFieldRestReadout.restState =
      operator (actualRestStatePreparation (0, 0))
        (YangMills.FullPairing.prepared 0) := rfl
  rw [hr]
  rw [hp]
  simp only [nativeCurrentWeight, Fin.isValue, ↓reduceIte, one_smul]
  exact PhysicalFullFieldRestReadout.rest_charge_unit

end LowEnergy.GaussComposite.PhysicalNativeCurrentAlignment
