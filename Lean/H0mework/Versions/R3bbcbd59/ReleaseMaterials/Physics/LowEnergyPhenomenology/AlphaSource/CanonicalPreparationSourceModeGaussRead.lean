import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceModeRestCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRawJointReaderCompression
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalRawActionDensity

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalModeChargeRead
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumRawJointFeedback PreparationVacuumOriginalDensity
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalZeroRead
open PreparationVacuumGaugeSourceInjection PreparationVacuumFullFieldRiesz
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumPhysicalPoleLegDynamics
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge CanonicalGradedSpatialSource
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert MeasureTheory Filter Set
open Electromagnetic.CanonicalCoframe SourceQuantumGaugeSliceCoordinates GaussQuantumMultiplier
open PreparationVacuumElectromagneticIdentity PreparationVacuumPropagationPencil PreparationVacuumJointFieldResponse
open PreparationVacuumSourceActionJets PreparationVacuumMovingPoleGaussReturn PreparationVacuumOriginalGreenFeedback
open PreparationVacuumNativePoleTensor PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open Electromagnetic.ExternalState Stage10.CanonicalMatter
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] sourceModeConnection sourceModeMother rawReader rawForm frameTest frameVector
  finiteRiesz sourceMatterActionOperator sourcePoleRead

def sourceModeConnectionDirection (f : Field289) : ActionState :=
  (0,(fun mu=>Quantum.operatorMatrix (sourceModeMother (fun j=>(f j:ℂ)) mu)),0)

/-- The remaining source direction retains the full coframe and scalar variations. -/
def sourceModeRemainingDirection (f : Field289) : ActionState :=
  (fieldCoframe f,0,scalarDirection (PreparationVacuumMixedFieldReturn.sourceField f))

theorem sourceModeDirection_generated (f : Field289) :
    fieldDirection f=sourceModeConnectionDirection f+sourceModeRemainingDirection f := by
  simp only [sourceModeConnectionDirection,sourceModeRemainingDirection,sourceModeMother_generated,
    sourceModeConnection_real,fieldDirection,Prod.mk_add_mk,add_zero,zero_add]

def sourceModeDirectionDensity (s d : ActionState) (k : Fin 4) : SourceMatrix :=
  Fin.cases (fderiv ℝ stateDensityLower s d)
    (fun j=>Complex.I • (fderiv ℝ (statePrincipal j.succ) s d)) k-
      Complex.I • ((fderiv ℝ (statePrincipal 0) s d)*stateHamiltonian s k)

theorem sourceModeDensity_generated (f : Field289) (s : ActionState) (k : Fin 4) :
    densityVariation f s k=sourceModeDirectionDensity s (sourceModeConnectionDirection f) k+
      sourceModeDirectionDensity s (sourceModeRemainingDirection f) k := by
  unfold densityVariation lowerVariation principalVariation
  rw [sourceModeDirection_generated]
  unfold sourceModeDirectionDensity
  simp only [map_add,add_mul,smul_add]
  cases k using Fin.cases <;> simp only [Fin.cases_zero,Fin.cases_succ] <;> abel

/-- The pure connection contribution is generated on the same actual density, before CAR. -/
theorem sourceModeConnectionDensity_generated (f : Field289) (s : ActionState)
    (nondegenerate : s.1.det≠0) (k : Fin 4) :
    sourceModeDirectionDensity s (sourceModeConnectionDirection f) k=
      if k=0 then stateVolume s • (∑mu : Fin 4,coefficientMatrix mu s.1*
        Quantum.operatorMatrix (sourceModeMother (fun j=>(f j:ℂ)) mu)) else 0 := by
  let d:=sourceModeConnectionDirection f
  let curve (r : ℝ) : ActionState:=s+r • d
  let A:=∑mu : Fin 4,coefficientMatrix mu s.1*
    Quantum.operatorMatrix (sourceModeMother (fun j=>(f j:ℂ)) mu)
  have coframe (r : ℝ) : (curve r).1=s.1 := by simp [curve,d,sourceModeConnectionDirection]
  have volume (r : ℝ) : stateVolume (curve r)=stateVolume s := by unfold stateVolume;rw [coframe]
  have lower (r : ℝ) : stateLower (curve r)=stateLower s+r • A := by
    simp only [stateLower,curve,d,sourceModeConnectionDirection,Prod.smul_fst,Prod.smul_snd,
      Prod.fst_add,Prod.snd_add,Pi.add_apply,Pi.smul_apply,smul_zero,add_zero,mul_add,
      Finset.sum_add_distrib,mul_smul_comm,←Finset.smul_sum,A]
    abel
  have path : HasDerivAt curve d 0:=state_line s d
  have lowerDerivative : fderiv ℝ stateDensityLower s d=stateVolume s • A := by
    have generated:=((stateDensityLower_smooth s nondegenerate).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp [curve])
    have affine:=((hasDerivAt_id (0:ℝ)).smul_const (stateVolume s • A)).const_add (stateDensityLower s)
    have identity (r : ℝ) : stateDensityLower (curve r)=stateDensityLower s+r • (stateVolume s • A) := by
      unfold stateDensityLower
      rw [volume,lower,smul_add,smul_comm (stateVolume s) r]
    exact generated.unique (by simpa only [Function.comp_def,identity,one_smul,id_eq] using affine)
  have principalDerivative (mu : Fin 4) : fderiv ℝ (statePrincipal mu) s d=0 := by
    have generated:=((statePrincipal_smooth mu s nondegenerate).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp [curve])
    have identity (r : ℝ) : statePrincipal mu (curve r)=statePrincipal mu s := by
      unfold statePrincipal
      rw [volume,coframe]
    exact generated.unique (by simpa only [Function.comp_def,identity] using hasDerivAt_const (0:ℝ) (statePrincipal mu s))
  unfold sourceModeDirectionDensity
  rw [lowerDerivative,principalDerivative]
  simp only [zero_mul,smul_zero,sub_zero]
  cases k using Fin.cases with
  | zero => rfl
  | succ j =>
    change Complex.I • (fderiv ℝ (statePrincipal j.succ) s d)=0
    rw [principalDerivative,smul_zero]

def sourceModeConnectionSymbol (f : Field289) (p : PhysicalMomentum) (s : ActionState) : FullMatrix :=
  rawFourier p (fun k=>densityActionMatrix*sourceModeDirectionDensity s (sourceModeConnectionDirection f) k)

def sourceModeRemainingSymbol (f : Field289) (p : PhysicalMomentum) (s : ActionState) : FullMatrix :=
  rawFourier p (fun k=>densityActionMatrix*sourceModeDirectionDensity s (sourceModeRemainingDirection f) k)

theorem sourceModeRawSymbol_generated (f : Field289) (p : PhysicalMomentum) (s : ActionState) :
    rawActionSymbol f p s=sourceModeConnectionSymbol f p s+sourceModeRemainingSymbol f p s := by
  unfold rawActionSymbol sourceModeConnectionSymbol sourceModeRemainingSymbol
  simp only [sourceModeDensity_generated,mul_add]
  exact (rawFourier p).map_add _ _

def sourceModeConnectionCoefficient (f : Field289) (s : ActionState) : SourceMatrix :=
  densityActionMatrix*(stateVolume s • (∑mu : Fin 4,coefficientMatrix mu s.1*
    Quantum.operatorMatrix (sourceModeMother (fun j=>(f j:ℂ)) mu)))

theorem sourceModeConnectionSymbol_mother (f : Field289) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    sourceModeConnectionSymbol f p s=oppositeDual*SourceRealScalarFock.branches
      (sourceModeConnectionCoefficient f s) := by
  unfold sourceModeConnectionSymbol rawFourier
  simp only [sourceModeConnectionDensity_generated f s nondegenerate]
  change oppositeDual*realFourierMatrix
    (fun k=>densityActionMatrix*(if k=0 then stateVolume s • (∑mu : Fin 4,coefficientMatrix mu s.1*
      Quantum.operatorMatrix (sourceModeMother (fun j=>(f j:ℂ)) mu)) else 0)) p=_
  simp [realFourierMatrix,affineMatrix,sourceModeConnectionCoefficient,SourceRealScalarFock.branches]

/-- Both original independent-dual blocks and every occupation sector consume the complete split. -/
theorem sourceModeActualDensity_generated (f : Field289) (p : PhysicalMomentum) (s : ActionState) :
    actualDensity f p s=Fermion.quantize (sourceModeConnectionSymbol f p s)+
      Fermion.quantize (sourceModeRemainingSymbol f p s) := by
  rw [actualDensity_source,sourceModeRawSymbol_generated]
  simp only [Fermion.quantize,Matrix.add_apply,add_smul,Finset.sum_add_distrib]

/-- The full independent-dual density consumes the generated mother connection and the exact remaining source. -/
theorem sourceModeActualDensity_mother (f : Field289) (p : PhysicalMomentum)
    (s : ActionState) (nondegenerate : s.1.det≠0) :
    actualDensity f p s=Fermion.quantize (oppositeDual*SourceRealScalarFock.branches
      (sourceModeConnectionCoefficient f s))+Fermion.quantize (sourceModeRemainingSymbol f p s) := by
  rw [sourceModeActualDensity_generated,sourceModeConnectionSymbol_mother f p s nondegenerate]

theorem sourceModeRawFiber_generated (f : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    rawStateFiber f p (sourceState z)=quantizer (sourceModeConnectionSymbol f p (sourceState z))+
      quantizer (sourceModeRemainingSymbol f p (sourceState z)) := by
  rw [←rawActionSymbol_actual,sourceModeRawSymbol_generated,map_add]

def sourceModeGaussReader (V : Fin 289→ℂ) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ] H :=
  ∑j : Fin 289,V j • rawReader (fieldUnit j) p F 0

/-- Complex pole fields consume the original full Gauss reader with its actual action normalization. -/
theorem sourceModeGaussReader_real (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceModeGaussReader (fun j=>(f j:ℂ)) p F=rawReader f p F 0 := by
  have basis : f=∑j : Fin 289,f j • fieldUnit j := by
    funext k
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply]
  have generated:=congrArg (fderiv ℝ (sourceMatterActionOperator p F) 0) basis
  simp only [map_sum,map_smul,sourceMatterActionOperator_gradient] at generated
  rw [sourceModeGaussReader]
  calc
    _=∑j : Fin 289,f j • rawReader (fieldUnit j) p F 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (f j) (rawReader (fieldUnit j) p F 0)).symm
    _=_ := generated.symm

/-- The same Gauss measure consumes both generated CAR contributions inside the complete density. -/
theorem sourceModeGaussForm_generated (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    rawForm f p a b 0=∫z,pairSample z (a z)
      ((quantizer (sourceModeConnectionSymbol f p (sourceState z))+
        quantizer (sourceModeRemainingSymbol f p (sourceState z))) (b z)) ∂GaussHistoryHilbert.configurationMeasure := by
  rw [rawForm_original]
  simp_rw [sourceModeRawFiber_generated]

/-- No Gauss frame entries are discarded by the complexified full-field reader. -/
theorem sourceModeGaussReader_density (V : Fin 289→ℂ) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceModeGaussReader V p F=∑j : Fin 289,V j • finiteRiesz F
      (fun a b=>∫z,pairSample z (frameTest F a z)
        ((quantizer (sourceModeConnectionSymbol (fieldUnit j) p (sourceState z))+
          quantizer (sourceModeRemainingSymbol (fieldUnit j) p (sourceState z))) (frameTest F b z))
            ∂GaussHistoryHilbert.configurationMeasure) := by
  unfold sourceModeGaussReader
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold rawReader
  simp_rw [sourceModeGaussForm_generated]

def sourceModeGaussKernel (V : Fin 289→ℂ) (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (t : ℝ) : H→L[ℂ] H :=
  physicalTime (pR+(pL-pR)) q.F (-t) 0*jointResolvent (pR+(pL-pR)) q.F q.z 0*
    sourceModeGaussReader V pR q.F*jointResolvent pR q.F q.w 0*physicalTime pR q.F t 0

theorem sourceModeGaussKernel_generated (V : Fin 289→ℂ) (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (t : ℝ) :
    sourceModeGaussKernel V q pL pR t=∑j : Fin 289,V j •
      fiveKernel (fieldUnit j) pR (pL-pR) q.F q.z q.w t 0 := by
  unfold sourceModeGaussKernel sourceModeGaussReader fiveKernel
  simp only [Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]

/-- The generated full-field mode contracts the original actual current, including every source remainder. -/
theorem sourceModeGaussCurrent_generated (V : Fin 289→ℂ) (q : PhysicalResponsePoint)
    (pL pR : PhysicalMomentum) (left right : RestStateIndex) (t : ℝ) :
    (∑j : Fin 289,V j*sourcePoleActionEuler q pL pR left right 0 t j)=
      -sourcePoleRead q.epsilon q.precision pL pR left right (sourceModeGaussKernel V q pL pR t) := by
  rw [sourceModeGaussKernel_generated,map_sum]
  simp only [map_smul,smul_eq_mul,Finset.sum_neg_distrib,sourcePoleActionEuler_source,mul_neg]

/-- The original whole matrix of constraints is consumed; no row or remainder is erased. -/
theorem sourceModeWholeConstraints_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ)
    (V : Fin 289→ℂ) :
    (∑row : Fin 289,V row*(originalReadback (fullMomentum spatial lambda)*ᵥ
      sourcePoleCurrentWindow q pL pR left right lambda T) row)=
      ∑row : Fin 289,V row*sourceActualCurrentCosource q pL pR left right spatial lambda T row := by
  rw [sourceActualCurrentWindow_ward]

/-- Both actual native pole branches feed the same full connection, independent-dual matrix and Gauss current. -/
theorem sourceModeActualSheet_generated (q : PhysicalResponsePoint) (branch : Fin 2)
    (n p : PhysicalMomentum) (unit : spatialSquare n=1) (l r : RestStateIndex) (T : ℝ)
    (mu : Fin 4) :
    ∀ᶠ e in scaleApproach,
      Tendsto (fun t=>((t-sourceSheet branch n unit e.val:ℝ):ℂ) •
        sourceModeConnection mu (actualSheetField q e.val t n p l r T))
        (𝓝[≠] (sourceSheet branch n unit e.val))
        (𝓝 (sourceModeConnection mu (actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p l r T))) ∧
      (∀ (point : BasePoint) (left right : RestStateIndex),
        actual.conjugateMatter point (canonicalDual (actualRestStatePreparation left)
          (sourceModeCurrent (actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p l r T) mu
            (actualRestStatePreparation right (actual.matter point))))=
          (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceModeRestMixing
            (actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p l r T) mu left right) ∧
      (∀ (pL pR : PhysicalMomentum) (left right : RestStateIndex) (t : ℝ),
        (∑j : Fin 289,actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p l r T j*
          sourcePoleActionEuler q pL pR left right 0 t j)=
          -sourcePoleRead q.epsilon q.precision pL pR left right
            (sourceModeGaussKernel (actualSheetResidue q e.val (sourceSheet branch n unit e.val) n p l r T)
              q pL pR t)) := by
  filter_upwards [sourceActualSheetConnection_residue q branch n p unit l r T mu] with e pole
  exact ⟨pole,actualSheetRest_current q e.val (sourceSheet branch n unit e.val) n p l r T mu,
    sourceModeGaussCurrent_generated _ q⟩

end LowEnergy.PreparationVacuumPhysicalModeChargeRead
