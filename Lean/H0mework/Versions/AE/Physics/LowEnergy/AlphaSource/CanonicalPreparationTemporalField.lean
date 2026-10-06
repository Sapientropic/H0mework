import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFieldLocalized

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTemporalCharge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open StageNineLorentzConnectionVariation StageNineLorentzConnectionVariationDensity
open StageNineDiracDualYukawaSpinJurisdiction StageNineDiracDualFormNativeConjugateMatterVariation
open SU7ExteriorYukawaMassSpectrum SU7ExteriorBreakingYukawa
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open SourceQuantumFockGauge GaussHistoryHilbert
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open Electromagnetic.CanonicalCoframe
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumLowerClassical
open CanonicalGradedSpatialSource
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators Topology
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

def temporalField (a : Fin 12) : Field289 := Pi.single (gaugeSlot 0 a) 1

theorem temporal_gauge_slot (a b : Fin 12) (mu : Fin 4) :
    temporalField a (gaugeSlot mu b)=if mu=0 ∧ b=a then 1 else 0 := by
  have same : gaugeSlot mu b=gaugeSlot 0 a ↔ mu=0 ∧ b=a := by
    constructor
    · intro h
      have hv:=congrArg Fin.val h
      simp only [gaugeSlot] at hv
      constructor <;> apply Fin.ext <;> omega
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [temporalField,Pi.single_apply,same]

theorem temporal_coframe (a : Fin 12) : fieldCoframe (temporalField a)=0 := by
  ext i j
  have ne : coframeSlot i j≠gaugeSlot 0 a := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [coframeSlot,gaugeSlot] at hv
    omega
  simp [fieldCoframe,temporalField,ne]

theorem temporal_lorentz (a : Fin 12) : fieldLorentz (temporalField a)=0 := by
  ext mu b
  have ne : lorentzSlot mu b≠gaugeSlot 0 a := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [lorentzSlot,gaugeSlot] at hv
    omega
  simp [fieldLorentz,temporalField,ne]

theorem temporal_scalar (a : Fin 12) : fieldScalar (temporalField a)=0 := by
  have ne (j : Fin 9) : scalarSlot j≠gaugeSlot 0 a := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [scalarSlot,gaugeSlot] at hv
    omega
  simp [fieldScalar,temporalField,ne]

theorem temporal_gauge (a : Fin 12) (mu : Fin 4) :
    fieldGauge (temporalField a) mu=if mu=0 then originalUnit a else 0 := by
  simp only [fieldGauge,temporal_gauge_slot]
  by_cases hm : mu=0 <;> simp [hm,ite_smul]

theorem temporal_connection (a : Fin 12) (mu : Fin 4) :
    connectionDirection (sourceField (temporalField a)) mu=
      if mu=0 then GaussNativeMatter.nativePrimal (originalUnit a) else 0 := by
  simp only [connectionDirection,sourceField,temporal_lorentz,temporal_gauge,
    lorentzSkewConnectionOfBivectorOneForm_zero,diracSpinConnectionLift_zero]
  have spin : diracMatrixMatterAction (0 : DiracCliffordRepresentation.DiracMatrix)=0 := by
    apply LinearMap.ext
    intro v
    exact diracMatrixMatterAction_zero_matrix v
  rw [spin,zero_add]
  split_ifs with hm
  · rfl
  · simp only [map_zero,SU7MotherGaugeTheory.p286LieBlockEmbed_zero]
    have zeroAction : diracExteriorMotherLieAction 0=0 := by
      apply LinearMap.ext
      intro v
      exact StageNineP286GaugeConnectionVariationDensity.diracExteriorMotherLieAction_zero_matrix v
    rw [zeroAction,map_zero]

theorem temporal_scalar_matrix (a : Fin 12) : scalarDirection (sourceField (temporalField a))=0 := by
  unfold scalarDirection sourceField
  rw [temporal_scalar,map_zero]
  have zero := diracDualRightChiralYukawaAction_smul (0:ℂ) (0:ExteriorBreakingScalarCarrier)
  simp only [zero_smul] at zero
  rw [zero,map_zero]

theorem temporal_direction (a : Fin 12) : fieldDirection (temporalField a)=
    (0,(fun mu=>if mu=0 then GaussNativeMatter.nativePrimal (originalUnit a) else 0),0) := by
  unfold fieldDirection
  rw [temporal_coframe,temporal_scalar_matrix]
  exact Prod.ext rfl (Prod.ext (funext (temporal_connection a)) rfl)

def temporalCurve (a : Fin 12) (s : ActionState) (r : ℝ) : ActionState :=
  s+r • fieldDirection (temporalField a)

theorem temporalCurve_coframe (a : Fin 12) (s : ActionState) (r : ℝ) :
    (temporalCurve a s r).1=s.1 := by simp [temporalCurve,temporal_direction]

theorem temporalCurve_scalar (a : Fin 12) (s : ActionState) (r : ℝ) :
    (temporalCurve a s r).2.2=s.2.2 := by simp [temporalCurve,temporal_direction]

theorem temporalCurve_connection (a : Fin 12) (s : ActionState) (r : ℝ) (mu : Fin 4) :
    (temporalCurve a s r).2.1 mu=s.2.1 mu+
      if mu=0 then r • GaussNativeMatter.nativePrimal (originalUnit a) else 0 := by
  rw [temporalCurve,temporal_direction]
  change s.2.1 mu+r • (if mu=0 then GaussNativeMatter.nativePrimal (originalUnit a) else 0)=_
  rw [smul_ite,smul_zero]

theorem temporal_lower (a : Fin 12) (s : ActionState) (r : ℝ) :
    stateLower (temporalCurve a s r)=stateLower s+
      r • (CoframeResponse.principalMatrix s.1*GaussNativeMatter.nativePrimal (originalUnit a)) := by
  unfold stateLower
  simp only [temporalCurve_coframe,temporalCurve_scalar,temporalCurve_connection,mul_add,mul_ite,mul_zero,
    Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_smul_comm]
  rw [CoframeResponse.principalMatrix_coefficient]
  abel

theorem temporal_volume (a : Fin 12) (s : ActionState) (r : ℝ) :
    stateVolume (temporalCurve a s r)=stateVolume s := by
  unfold stateVolume
  rw [temporalCurve_coframe]

theorem temporal_principal (a : Fin 12) (s : ActionState) (r : ℝ) (mu : Fin 4) :
    statePrincipal mu (temporalCurve a s r)=statePrincipal mu s := by
  rw [statePrincipal,statePrincipal,temporal_volume,temporalCurve_coframe]

theorem temporal_held_density (a : Fin 12) (s : ActionState) (r : ℝ) (i : Fin 4) :
    heldDensityCoefficient s (temporalCurve a s r) i=heldDensityCoefficient s s i+
      r • (if i=0 then stateVolume s •
        (CoframeResponse.principalMatrix s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0) := by
  unfold heldDensityCoefficient stateDensityLower
  rw [temporal_volume,temporal_lower]
  simp only [temporal_principal,smul_add]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Fin.cases_zero,if_true]
    rw [smul_comm (stateVolume s) r]
    abel
  · simp

theorem temporal_density (a : Fin 12) (s : ActionState) (nondegenerate : s.1.det≠0) (i : Fin 4) :
    densityVariation (temporalField a) s i=if i=0 then stateVolume s •
      (CoframeResponse.principalMatrix s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0 := by
  have actual:=densityVariation_generated (temporalField a) s nondegenerate i
  have affine:=((hasDerivAt_id (0:ℝ)).smul_const
    (if i=0 then stateVolume s •
      (CoframeResponse.principalMatrix s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0)).const_add
        (heldDensityCoefficient s s i)
  have generated : HasDerivAt (fun r=>heldDensityCoefficient s (temporalCurve a s r) i)
      (if i=0 then stateVolume s •
        (CoframeResponse.principalMatrix s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0) 0 := by
    convert! affine using 1 <;> simp only [temporal_held_density,one_smul,id_eq]
  exact actual.unique generated

theorem temporal_family_density (a : Fin 12) (z : physicalChart) (i : Fin 4) :
    familyDensity (temporalField a) z.val i=if i=0 then stateVolume (sourceState z.val) •
      (CoframeResponse.principalMatrix (sourceState z.val).1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0 :=
  temporal_density a (sourceState z.val) (coframe_nondegenerate z) i

theorem temporal_normalized_reader (a : Fin 12) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : StageNineCurrentCoframeMatterTemporalPrincipal.coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    statePhase s*densityVariation (temporalField a) s i=
      if i=0 then Complex.I • GaussNativeMatter.nativePrimal (originalUnit a) else 0 := by
  rw [temporal_density a s nondegenerate i]
  split_ifs with hi
  · have unit:=principalMatrix_regular s.1 regular
    have volume : stateVolume s≠0 := by
      unfold stateVolume
      exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nondegenerate)
    unfold statePhase
    rw [smul_mul_assoc,mul_smul_comm,←mul_assoc,Ring.inverse_mul_cancel _ unit,one_mul,smul_smul]
    congr 1
    field_simp
  · rw [mul_zero]

theorem temporal_family_reader (a : Fin 12) (z : physicalChart) (i : Fin 4) :
    familyReader (temporalField a) z.val i=
      if i=0 then Complex.I • GaussNativeMatter.nativePrimal (originalUnit a) else 0 :=
  temporal_normalized_reader a (sourceState z.val) (coframe_nondegenerate z)
    (temporal_noncharacteristic z) i

end LowEnergy.PreparationVacuumTemporalCharge
