import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugeFields

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaugeSourceInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open StageNineDiracDualYukawaSpinJurisdiction SU7ExteriorBreakingYukawa
open StageNineDiracDualFormNativeConjugateMatterVariation
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open SourceQuantumFockGauge GaussHistoryHilbert GaussNativeMatter
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse Electromagnetic.CanonicalCoframe
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceFieldFamily PreparationVacuumLowerClassical CanonicalGradedMixedSource
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators Topology
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

abbrev PrimitiveIndex := SourceScalarFock.ScalarIndex ⊕ ((Fin 4×Fin 12) ⊕ ((Fin 4×Fin 4) ⊕ (Fin 4×Fin 6)))
abbrev FieldData := Scalar × (Fin 4→NativeLie) × LorentzianCoframe × LorentzBivectorOneForm

theorem primitive_count : Fintype.card PrimitiveIndex=158 := by
  change Fintype.card (SourceScalarFock.ScalarIndex ⊕ ((Fin 4×Fin 12) ⊕ ((Fin 4×Fin 4) ⊕ (Fin 4×Fin 6))))=158
  rw [Fintype.card_sum,SourceScalarFock.scalar_index_card]
  norm_num

def sourceData (f : Field289) : FieldData := (fieldScalar f,fieldGauge f,fieldCoframe f,fieldLorentz f)

def primitiveData : PrimitiveIndex→FieldData
  | .inl a => (scalarCoordinate a,0,0,0)
  | .inr (.inl a) => (0,Pi.single a.1 (originalUnit a.2),0,0)
  | .inr (.inr (.inl a)) => (0,0,Pi.single a.1 (Pi.single a.2 1),0)
  | .inr (.inr (.inr a)) => (0,0,0,Pi.single a.1 (Pi.single a.2 1))

def primitiveWeight (f : Field289) : PrimitiveIndex→ℝ
  | .inl a => scalarWeight f a
  | .inr (.inl a) => f (gaugeSlot a.1 a.2)
  | .inr (.inr (.inl a)) => f (coframeSlot a.1 a.2)
  | .inr (.inr (.inr a)) => f (lorentzSlot a.1 a.2)

theorem original_source_data (f : Field289) :
    (∑ a : PrimitiveIndex,primitiveWeight f a • primitiveData a)=sourceData f := by
  apply Prod.ext
  · let ev : FieldData →ₗ[ℝ] Scalar := LinearMap.fst ℝ _ _
    change ev (∑ a : PrimitiveIndex,primitiveWeight f a • primitiveData a)=fieldScalar f
    rw [map_sum]
    simp only [map_smul,Fintype.sum_sum_type,primitiveWeight,primitiveData]
    change (∑ a,scalarWeight f a • scalarCoordinate a)+
      ((∑ a : Fin 4×Fin 12,_ • (0 : Scalar))+
        ((∑ a : Fin 4×Fin 4,_ • (0 : Scalar))+(∑ a : Fin 4×Fin 6,_ • (0 : Scalar))))=fieldScalar f
    simp only [smul_zero,Finset.sum_const_zero,add_zero]
    exact fieldScalar_seventy f
  · apply Prod.ext
    · funext mu
      let ev : FieldData →ₗ[ℝ] NativeLie :=
        { toFun:=fun d=>d.2.1 mu,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
      change ev (∑ a : PrimitiveIndex,primitiveWeight f a • primitiveData a)=fieldGauge f mu
      rw [map_sum]
      simp only [map_smul,Fintype.sum_sum_type,primitiveWeight,primitiveData]
      simp [ev,Fintype.sum_prod_type,Pi.single_apply,fieldGauge]
    · apply Prod.ext
      · funext i mu
        let ev : FieldData →ₗ[ℝ] ℝ :=
          { toFun:=fun d=>d.2.2.1 i mu,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
        change ev (∑ a : PrimitiveIndex,primitiveWeight f a • primitiveData a)=f (coframeSlot i mu)
        rw [map_sum]
        simp [ev,Fintype.sum_sum_type,Fintype.sum_prod_type,primitiveWeight,primitiveData,Pi.single_apply,ite_apply]
      · funext mu b
        let ev : FieldData →ₗ[ℝ] ℝ :=
          { toFun:=fun d=>d.2.2.2 mu b,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
        change ev (∑ a : PrimitiveIndex,primitiveWeight f a • primitiveData a)=f (lorentzSlot mu b)
        rw [map_sum]
        simp [ev,Fintype.sum_sum_type,Fintype.sum_prod_type,primitiveWeight,primitiveData,Pi.single_apply,ite_apply]

def lorentzLinear : LorentzBivectorOneForm →ₗ[ℝ] PointwiseLorentzSpinConnection where
  toFun:=lorentzSkewConnectionOfBivectorOneForm
  map_add':=lorentzSkewConnectionOfBivectorOneForm_add
  map_smul':=lorentzSkewConnectionOfBivectorOneForm_smul

def spinLinear (mu : Fin 4) : LorentzBivectorOneForm →ₗ[ℝ] SourceMatrix :=
  (spinCoordinates.restrictScalars ℝ).comp ((diracSpinConnectionLiftLinear mu).comp lorentzLinear)

def scalarLinear : Scalar →ₗ[ℂ] SourceMatrix where
  toFun s:=Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s))
  map_add' s t:=by simp only [map_add,diracDualRightChiralYukawaAction_add]
  map_smul' c s:=by simp only [map_smul,diracDualRightChiralYukawaAction_smul,RingHom.id_apply]

def stateDirectionMap : FieldData →ₗ[ℝ] ActionState where
  toFun d:=(d.2.2.1,(fun mu=>spinLinear mu d.2.2.2+nativePrimal (d.2.1 mu)),scalarLinear d.1)
  map_add' d e:=by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext mu
      change spinLinear mu (d.2.2.2+e.2.2.2)+nativePrimal (d.2.1 mu+e.2.1 mu)=_
      rw [map_add,map_add]
      change _=(spinLinear mu d.2.2.2+nativePrimal (d.2.1 mu))+(spinLinear mu e.2.2.2+nativePrimal (e.2.1 mu))
      abel
    · exact map_add scalarLinear _ _
  map_smul' r d:=by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext mu
      change spinLinear mu (r • d.2.2.2)+nativePrimal (r • d.2.1 mu)=r • _
      rw [map_smul,map_smul,smul_add]
    · exact (scalarLinear.restrictScalars ℝ).map_smul r d.1

theorem stateDirection_source (f : Field289) : stateDirectionMap (sourceData f)=fieldDirection f := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix _+Quantum.operatorMatrix _=Quantum.operatorMatrix (_+_)
    exact (Quantum.operatorMatrix.map_add _ _).symm
  · rfl

def primitiveDirection (a : PrimitiveIndex) : ActionState := stateDirectionMap (primitiveData a)

theorem original_direction_injection (f : Field289) :
    (∑ a : PrimitiveIndex,primitiveWeight f a • primitiveDirection a)=fieldDirection f := by
  have h:=congrArg stateDirectionMap (original_source_data f)
  simp only [map_sum,map_smul,stateDirection_source] at h
  convert! h using 1

def primitiveDensity (a : PrimitiveIndex) (s : ActionState) (i : Fin 4) : SourceMatrix :=
  Fin.cases (fderiv ℝ stateDensityLower s (primitiveDirection a))
    (fun j=>Complex.I • fderiv ℝ (statePrincipal j.succ) s (primitiveDirection a)) i-
      Complex.I • (fderiv ℝ (statePrincipal 0) s (primitiveDirection a)*stateHamiltonian s i)

theorem original_density_injection (f : Field289) (s : ActionState) (i : Fin 4) :
    densityVariation f s i=∑ a : PrimitiveIndex,primitiveWeight f a • primitiveDensity a s i := by
  unfold densityVariation lowerVariation principalVariation
  rw [←original_direction_injection]
  simp only [map_sum,map_smul,Finset.sum_mul,Finset.smul_sum]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Fin.cases_zero,primitiveDensity,smul_mul_assoc,smul_comm (Complex.I),smul_sub,Finset.sum_sub_distrib]
  · simp only [Fin.cases_succ,primitiveDensity,smul_mul_assoc,smul_comm (Complex.I),smul_sub,Finset.sum_sub_distrib]

theorem gauge_injection_direct (nu : Fin 4) (a : Fin 12) (s : ActionState) (nondegenerate : s.1.det≠0) (i : Fin 4) :
    (∑ b : PrimitiveIndex,primitiveWeight (gaugeField nu a) b • primitiveDensity b s i)=
      if i=0 then stateVolume s • (coefficientMatrix nu s.1*nativePrimal (originalUnit a)) else 0 := by
  rw [←original_density_injection]
  exact gauge_density nu a s nondegenerate i

/-- The original 97 bosonic matter-source rows, retaining scalar Ward and Lorentz rows. -/
def sourceSlot (a : Fin 97) : Fin 289 := if a.val<73 then ⟨a.val,by omega⟩ else ⟨a.val+48,by omega⟩

def sourceFieldUnit (a : Fin 97) : Field289 := Pi.single (sourceSlot a) 1

theorem sourceSlot_gauge (nu : Fin 4) (a : Fin 12) :
    sourceSlot ⟨9+12*nu.val+a.val,by omega⟩=gaugeSlot nu a := by
  apply Fin.ext
  simp only [sourceSlot,show 9+12*nu.val+a.val<73 by omega,if_true,gaugeSlot]

def injectSource (j : Fin 97→ℂ) (row : Fin 289) : ℂ :=
  ∑ a : Fin 97,if row=sourceSlot a then j a else 0

theorem actual_source_pairing (j : Fin 97→ℂ) (f : Field289) :
    (∑ row : Fin 289,(f row:ℂ)*injectSource j row)=∑ a : Fin 97,(f (sourceSlot a):ℂ)*j a := by
  simp only [injectSource,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem original_action_normalization (a : Fin 97) (i : Fin 4) (point : BasePoint)
    (preparation : YangMills.FullPairing.Mother) :
    Stage9C.Material.SpinPair.actual.conjugateMatter point
      (Stage10.CanonicalMatter.canonicalDual preparation
        (sourceDensityMother (sourceFieldUnit a) i (preparation (Stage9C.Material.SpinPair.actual.matter point))))=
      4*(Stage9C.Material.SpinPair.spinScale:ℂ)*inner ℂ
        (YangMills.FullPairing.operator preparation (YangMills.FullPairing.prepared point))
        (YangMills.FullPairing.operator ((Stage10.CanonicalMatter.phaseInverse.comp
          (sourceDensityMother (sourceFieldUnit a) i)).comp preparation) (YangMills.FullPairing.prepared point)) :=
  source_field_action_gram (sourceFieldUnit a) i point preparation

end LowEnergy.PreparationVacuumGaugeSourceInjection
