import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalWardConsumer

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaugeSourceInjection
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
open PreparationVacuumTemporalCharge PreparationVacuumActionDecomposition GaussNativeMatter
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators Topology
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

def gaugeField (nu : Fin 4) (a : Fin 12) : Field289 := Pi.single (gaugeSlot nu a) 1

theorem gauge_gauge_slot (nu : Fin 4) (a b : Fin 12) (mu : Fin 4) :
    gaugeField nu a (gaugeSlot mu b)=if mu=nu ∧ b=a then 1 else 0 := by
  have same : gaugeSlot mu b=gaugeSlot nu a ↔ mu=nu ∧ b=a := by
    constructor
    · intro h
      have hv:=congrArg Fin.val h
      simp only [gaugeSlot] at hv
      constructor <;> apply Fin.ext <;> omega
    · rintro ⟨rfl,rfl⟩
      rfl
  simp only [gaugeField,Pi.single_apply,same]

theorem gauge_coframe (nu : Fin 4) (a : Fin 12) : fieldCoframe (gaugeField nu a)=0 := by
  ext i j
  have ne : coframeSlot i j≠gaugeSlot nu a := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [coframeSlot,gaugeSlot] at hv
    omega
  simp [fieldCoframe,gaugeField,ne]

theorem gauge_lorentz (nu : Fin 4) (a : Fin 12) : fieldLorentz (gaugeField nu a)=0 := by
  ext mu b
  have ne : lorentzSlot mu b≠gaugeSlot nu a := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [lorentzSlot,gaugeSlot] at hv
    omega
  simp [fieldLorentz,gaugeField,ne]

theorem gauge_scalar (nu : Fin 4) (a : Fin 12) : fieldScalar (gaugeField nu a)=0 := by
  have ne (j : Fin 9) : scalarSlot j≠gaugeSlot nu a := by
    intro h
    have hv:=congrArg Fin.val h
    simp only [scalarSlot,gaugeSlot] at hv
    omega
  simp [fieldScalar,gaugeField,ne]

theorem gauge_gauge (nu : Fin 4) (a : Fin 12) (mu : Fin 4) :
    fieldGauge (gaugeField nu a) mu=if mu=nu then originalUnit a else 0 := by
  simp only [fieldGauge,gauge_gauge_slot]
  by_cases hm : mu=nu <;> simp [hm,ite_smul]

theorem gauge_connection (nu : Fin 4) (a : Fin 12) (mu : Fin 4) :
    connectionDirection (sourceField (gaugeField nu a)) mu=
      if mu=nu then GaussNativeMatter.nativePrimal (originalUnit a) else 0 := by
  simp only [connectionDirection,sourceField,gauge_lorentz,gauge_gauge,
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

theorem gauge_scalar_matrix (nu : Fin 4) (a : Fin 12) : scalarDirection (sourceField (gaugeField nu a))=0 := by
  unfold scalarDirection sourceField
  rw [gauge_scalar,map_zero]
  have zero := diracDualRightChiralYukawaAction_smul (0:ℂ) (0:ExteriorBreakingScalarCarrier)
  simp only [zero_smul] at zero
  rw [zero,map_zero]

theorem gauge_direction (nu : Fin 4) (a : Fin 12) : fieldDirection (gaugeField nu a)=
    (0,(fun mu=>if mu=nu then GaussNativeMatter.nativePrimal (originalUnit a) else 0),0) := by
  unfold fieldDirection
  rw [gauge_coframe,gauge_scalar_matrix]
  exact Prod.ext rfl (Prod.ext (funext (gauge_connection nu a)) rfl)

def gaugeCurve (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) : ActionState :=
  s+r • fieldDirection (gaugeField nu a)

theorem gaugeCurve_coframe (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) :
    (gaugeCurve nu a s r).1=s.1 := by simp [gaugeCurve,gauge_direction]

theorem gaugeCurve_scalar (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) :
    (gaugeCurve nu a s r).2.2=s.2.2 := by simp [gaugeCurve,gauge_direction]

theorem gaugeCurve_connection (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) (mu : Fin 4) :
    (gaugeCurve nu a s r).2.1 mu=s.2.1 mu+
      if mu=nu then r • GaussNativeMatter.nativePrimal (originalUnit a) else 0 := by
  rw [gaugeCurve,gauge_direction]
  change s.2.1 mu+r • (if mu=nu then GaussNativeMatter.nativePrimal (originalUnit a) else 0)=_
  rw [smul_ite,smul_zero]

theorem gauge_lower (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) :
    stateLower (gaugeCurve nu a s r)=stateLower s+
      r • (coefficientMatrix nu s.1*GaussNativeMatter.nativePrimal (originalUnit a)) := by
  unfold stateLower
  simp only [gaugeCurve_coframe,gaugeCurve_scalar,gaugeCurve_connection,mul_add,mul_ite,mul_zero,
    Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,mul_smul_comm]
  abel

theorem gauge_volume (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) :
    stateVolume (gaugeCurve nu a s r)=stateVolume s := by
  unfold stateVolume
  rw [gaugeCurve_coframe]

theorem gauge_principal (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) (mu : Fin 4) :
    statePrincipal mu (gaugeCurve nu a s r)=statePrincipal mu s := by
  rw [statePrincipal,statePrincipal,gauge_volume,gaugeCurve_coframe]

theorem gauge_held_density (nu : Fin 4) (a : Fin 12) (s : ActionState) (r : ℝ) (i : Fin 4) :
    heldDensityCoefficient s (gaugeCurve nu a s r) i=heldDensityCoefficient s s i+
      r • (if i=0 then stateVolume s •
        (coefficientMatrix nu s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0) := by
  unfold heldDensityCoefficient stateDensityLower
  rw [gauge_volume,gauge_lower]
  simp only [gauge_principal,smul_add]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Fin.cases_zero,if_true]
    rw [smul_comm (stateVolume s) r]
    abel
  · simp

theorem gauge_density (nu : Fin 4) (a : Fin 12) (s : ActionState) (nondegenerate : s.1.det≠0) (i : Fin 4) :
    densityVariation (gaugeField nu a) s i=if i=0 then stateVolume s •
      (coefficientMatrix nu s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0 := by
  have actual:=densityVariation_generated (gaugeField nu a) s nondegenerate i
  have affine:=((hasDerivAt_id (0:ℝ)).smul_const
    (if i=0 then stateVolume s •
      (coefficientMatrix nu s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0)).const_add
        (heldDensityCoefficient s s i)
  have generated : HasDerivAt (fun r=>heldDensityCoefficient s (gaugeCurve nu a s r) i)
      (if i=0 then stateVolume s •
        (coefficientMatrix nu s.1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0) 0 := by
    convert! affine using 1 <;> simp only [gauge_held_density,one_smul,id_eq]
  exact actual.unique generated

theorem gauge_family_density (nu : Fin 4) (a : Fin 12) (z : physicalChart) (i : Fin 4) :
    familyDensity (gaugeField nu a) z.val i=if i=0 then stateVolume (sourceState z.val) •
      (coefficientMatrix nu (sourceState z.val).1*GaussNativeMatter.nativePrimal (originalUnit a)) else 0 :=
  gauge_density nu a (sourceState z.val) (coframe_nondegenerate z) i

def gaugePrimal (nu : Fin 4) (a : Fin 12) (z : SourceCoordinateSlice) : SourceMatrix :=
  -(leftTime z*coefficientMatrix nu (sourceCoframe z)*nativePrimal (originalUnit a))

theorem gauge_family_reader (nu : Fin 4) (a : Fin 12) (z : physicalChart) (i : Fin 4) :
    familyReader (gaugeField nu a) z.val i=if i=0 then gaugePrimal nu a z.val else 0 := by
  rw [familyReader,gauge_family_density]
  split_ifs with hi
  · have nonzero : stateVolume (sourceState z.val)≠0 := by
      unfold stateVolume
      exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (coframe_nondegenerate z))
    change statePhase (sourceState z.val)*
      (stateVolume (sourceState z.val) • (coefficientMatrix nu (sourceCoframe z.val)*nativePrimal (originalUnit a)))=_
    unfold statePhase gaugePrimal leftTime
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,sourceState,mul_assoc,neg_smul]
    have factor : stateVolume (sourceState z.val)*(Complex.I*(stateVolume (sourceState z.val))⁻¹)=Complex.I := by
      field_simp
    simp only [sourceState] at factor
    rw [factor,neg_mul,neg_neg,smul_mul_assoc]
  · rw [mul_zero]

def primalGaugeTerm (j b : Fin 3) (a : Fin 12) (z : SourceCoordinateSlice) : SourceMatrix :=
  (GaussMatterCore.coefficient j b z:ℂ) •
    ((Complex.I • GaussCoframeSpin.primal (Fin.castAdd 4 b))*nativePrimal (originalUnit a))

theorem spatial_primal (j : Fin 3) (a : Fin 12) (z : physicalChart) :
    gaugePrimal j.succ a z.val= -(∑ b : Fin 3,primalGaugeTerm j b a z.val) := by
  rw [gaugePrimal,spatialLeft_source z j,Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [primalGaugeTerm,Matrix.smul_mul,smul_smul]

theorem primalGaugeTerm_branches (j b : Fin 3) (a : Fin 12) (z : SourceCoordinateSlice) :
    SourceRealScalarFock.branches (primalGaugeTerm j b a z)=
      (GaussMatterCore.coefficient j b z:ℂ) • GaussMatterCore.matrixTerm b (originalUnit a) := by
  change SourceRealScalarFock.branches ((GaussMatterCore.coefficient j b z:ℂ) •
    ((Complex.I • GaussCoframeSpin.primal (Fin.castAdd 4 b))*nativePrimal (originalUnit a)))=
    (GaussMatterCore.coefficient j b z:ℂ) •
      ((Complex.I • GaussCoframeSpin.full (Fin.castAdd 4 b))*nativeFull (originalUnit a))
  have hb : (Fin.castAdd 4 b).val<3:=b.isLt
  simp only [GaussCoframeSpin.full,hb,if_true,nativeFull,LinearMap.coe_mk,AddHom.coe_mk,Matrix.smul_mul]
  rw [Matrix.fromBlocks_multiply]
  ext u v
  cases u <;> cases v <;>
    simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.smul_apply,Matrix.mul_apply,smul_smul] <;> ring

theorem gauge_full_family (nu : Fin 4) (a : Fin 12) (p : PhysicalMomentum) (z : physicalChart) :
    fullFamily (gaugeField nu a) p z.val=
      CanonicalGradedCurrent.gaugeMatrix z.val (Fin.cases .temporal .spatial nu) (originalUnit a) := by
  refine Fin.cases ?_ (fun j=>?_) nu
  · exact temporal_full_family a p z
  · have coefficients : familyReader (gaugeField j.succ a) z.val=
        fun i=>if i=0 then gaugePrimal j.succ a z.val else 0 := funext (gauge_family_reader j.succ a z)
    rw [fullFamily,coefficients]
    have affine (q : PhysicalMomentum) :
        affineMatrix (fun i=>if i=0 then gaugePrimal j.succ a z.val else 0) q=gaugePrimal j.succ a z.val := by
      simp [affineMatrix]
    rw [realFourierMatrix,affine,affine]
    change SourceRealScalarFock.branches (gaugePrimal j.succ a z.val)=_
    rw [spatial_primal j a z]
    have neg (A : SourceMatrix) : SourceRealScalarFock.branches (-A)= -SourceRealScalarFock.branches A := by
      ext u v
      cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.map_apply]
    rw [neg,branches_sum]
    simp_rw [primalGaugeTerm_branches]
    rfl

theorem gauge_source_core (nu : Fin 4) (a : Fin 12) (p : PhysicalMomentum)
    (f : GaussCoreDifferential.QuantumTest) :
    familyCore (gaugeField nu a) p f=
      CanonicalGradedLocalCurrent.sourceAction (Fin.cases .temporal .spatial nu) (originalUnit a) f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change GaussQuantumMultiplier.quantized (fullFamily (gaugeField nu a) p z) (f z)=_
    rw [gauge_full_family nu a p ⟨z,hz⟩]
    rfl
  · have zero : f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change GaussQuantumMultiplier.quantized (fullFamily (gaugeField nu a) p z) (f z)=
      GaussQuantumMultiplier.quantized (CanonicalGradedCurrent.gaugeMatrix z _ (originalUnit a)) (f z)
    rw [zero,map_zero,map_zero]

end LowEnergy.PreparationVacuumGaugeSourceInjection
