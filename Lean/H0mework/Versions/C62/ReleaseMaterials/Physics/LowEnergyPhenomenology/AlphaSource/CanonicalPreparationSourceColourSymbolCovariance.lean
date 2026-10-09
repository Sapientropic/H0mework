import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActualGaussMaterialRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalGaussMaterialContact
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff



open PreparationVacuumPhysicalGaussColorTorque



open FullQuantum
open scoped Matrix.Norms.L2Operator

local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

private theorem inverse_commutes {A : Type*} [MonoidWithZero A] {a b : A} (h : Commute a b) :
    Commute a (Ring.inverse b) := by
  by_cases unit : IsUnit b
  · obtain ⟨u,rfl⟩:=unit
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ unit]
    exact Commute.zero_right _

theorem sourceColour_coefficient (e : LorentzianCoframe) (mu : Fin 4) :
    Commute (nativePrimal (colorGenerator 2)) (coefficientMatrix mu e) := by
  have h:=GaussMatterCore.spin_native_commute
    (DiracExteriorMatterAction.inverseCoframeDiracGamma { coframe:=e,derivative:=0 } mu) (colorGenerator 2)
  rw [←GaussCoframeSpin.spinLift_source] at h
  change spinCoordinates _*nativePrimal (colorGenerator 2)=nativePrimal (colorGenerator 2)*spinCoordinates _ at h
  change nativePrimal (colorGenerator 2)*(Complex.I • spinCoordinates _)=
    (Complex.I • spinCoordinates _)*nativePrimal (colorGenerator 2)
  rw [mul_smul_comm,smul_mul_assoc,h]

theorem sourceColour_principal (e : LorentzianCoframe) :
    Commute (nativePrimal (colorGenerator 2)) (CoframeResponse.principalMatrix e) := by
  rw [CoframeResponse.principalMatrix_coefficient]
  exact sourceColour_coefficient e 0

theorem sourceColour_inversePrincipal (e : LorentzianCoframe) :
    Commute (nativePrimal (colorGenerator 2)) (Ring.inverse (CoframeResponse.principalMatrix e)) :=
  inverse_commutes (sourceColour_principal e)

theorem sourceColour_contact_frame (s : ActionState) :
    (stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).1=0 := by
  have frame : nativeFrameGenerator (Fin.castAdd 6 (2:Fin 3))=0:=rfl
  simp only [stateContact,frame,one_smul,zero_mul]


private theorem lower_commutator {ι A : Type*} [Fintype ι] [Ring A]
    (G S : A) (C Γ : ι→A) (h : ∀ i,G*C i=C i*G) :
    (∑ i,C i*(G*Γ i-Γ i*G))+(G*S-S*G)=
      G*((∑ i,C i*Γ i)+S)-((∑ i,C i*Γ i)+S)*G := by
  have term (i : ι) : C i*(G*Γ i-Γ i*G)=G*(C i*Γ i)-(C i*Γ i)*G := by
    rw [mul_sub,←mul_assoc (C i) G,←h i]
    noncomm_ring
  simp only [term,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul]
  noncomm_ring

theorem sourceColourLower_contact (s : ActionState) :
    (∑ mu : Fin 4,coefficientMatrix mu s.1*(stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).2.1 mu)+
      (stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).2.2=
      nativePrimal (colorGenerator 2)*stateLower s-stateLower s*nativePrimal (colorGenerator 2) := by
  have generator : nativeMatterGenerator (Fin.castAdd 6 (2:Fin 3))=nativePrimal (colorGenerator 2):=rfl
  change (∑ mu : Fin 4,coefficientMatrix mu s.1*(1 • (nativeMatterGenerator (Fin.castAdd 6 (2:Fin 3))*s.2.1 mu-
      s.2.1 mu*nativeMatterGenerator (Fin.castAdd 6 (2:Fin 3)))))+
    1 • (nativeMatterGenerator (Fin.castAdd 6 (2:Fin 3))*s.2.2-s.2.2*nativeMatterGenerator (Fin.castAdd 6 (2:Fin 3)))=_
  rw [generator]
  simp only [one_smul]
  exact lower_commutator _ _ _ _ (fun mu=>(sourceColour_coefficient s.1 mu).eq)

theorem sourceColourLower_line (s : ActionState) (r : ℝ) :
    stateLower (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s)=stateLower s+
      r • (nativePrimal (colorGenerator 2)*stateLower s-stateLower s*nativePrimal (colorGenerator 2)) := by
  have frame : (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).1=s.1 := by
    change s.1+r • (stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).1=s.1
    rw [sourceColour_contact_frame,smul_zero,add_zero]
  unfold stateLower
  rw [frame]
  change (∑ mu : Fin 4,coefficientMatrix mu s.1*(s.2.1 mu+r • (stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).2.1 mu))+
    (s.2.2+r • (stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).2.2)=_
  simp only [mul_add,mul_smul_comm,Finset.sum_add_distrib,←Finset.smul_sum]
  have lower:=sourceColourLower_contact s
  unfold stateLower at lower
  simp only [mul_add] at lower
  rw [←lower,smul_add]
  abel


theorem sourceColourHamiltonian_line (s : ActionState) (r : ℝ) (i : Fin 4) :
    stateHamiltonian (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s) i=stateHamiltonian s i+
      r • (nativePrimal (colorGenerator 2)*stateHamiltonian s i-stateHamiltonian s i*nativePrimal (colorGenerator 2)) := by
  have frame : (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).1=s.1 := by
    change s.1+r • (stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s).1=s.1
    rw [sourceColour_contact_frame,smul_zero,add_zero]
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [stateHamiltonian,Fin.cases_zero]
    rw [frame,sourceColourLower_line]
    simp only [timeSymbol,mul_add,mul_sub,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub,smul_comm (-Complex.I) r]
    congr 1
    congr 1
    rw [←mul_assoc (nativePrimal (colorGenerator 2)),(sourceColour_inversePrincipal s.1).eq]
    all_goals simp only [mul_assoc]
  · simp only [stateHamiltonian,Fin.cases_succ]
    rw [frame]
    have h := (sourceColour_inversePrincipal s.1).mul_right (sourceColour_coefficient s.1 j.succ)
    rw [h.eq,sub_self,smul_zero,add_zero]


private theorem affine_commutator (G : SourceMatrix) (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) :
    affineMatrix (fun i=>G*A i-A i*G) p=G*affineMatrix A p-affineMatrix A p*G := by
  simp only [affineMatrix,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,smul_sub,mul_smul_comm,smul_mul_assoc,Finset.sum_sub_distrib]
  abel

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks (A-B) 0 0 (C-D)=Matrix.fromBlocks A 0 0 C-Matrix.fromBlocks B 0 0 D := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

theorem sourceColour_fourier_commutator (p : PhysicalMomentum) (A : Fin 4→SourceMatrix) :
    fourierLinear p (fun i=>nativePrimal (colorGenerator 2)*A i-A i*nativePrimal (colorGenerator 2))=
      nativeFull (colorGenerator 2)*fourierLinear p A-fourierLinear p A*nativeFull (colorGenerator 2) := by
  change realFourierMatrix (fun i=>nativePrimal (colorGenerator 2)*A i-A i*nativePrimal (colorGenerator 2)) p=
    Matrix.fromBlocks (nativePrimal (colorGenerator 2)) 0 0 ((nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))*realFourierMatrix A p-
      realFourierMatrix A p*Matrix.fromBlocks (nativePrimal (colorGenerator 2)) 0 0 ((nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))
  rw [realFourierMatrix,affine_commutator,affine_commutator,realFourierMatrix]
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
  rw [←blocks_sub]
  congr 1
  change -((nativePrimal (colorGenerator 2)*affineMatrix A (-p)-affineMatrix A (-p)*nativePrimal (colorGenerator 2)).map (starRingEnd ℂ))=_
  rw [Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul,Matrix.map_mul]
  simp only [Matrix.mul_neg,Matrix.neg_mul]
  abel

theorem sourceColourSymbol_line (p : PhysicalMomentum) (s : ActionState) (r : ℝ) :
    sourceSymbol p (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s)=sourceSymbol p s+
      r • (nativeFull (colorGenerator 2)*sourceSymbol p s-sourceSymbol p s*nativeFull (colorGenerator 2)) := by
  have line : stateHamiltonian (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s)=stateHamiltonian s+
      r • (fun i=>nativePrimal (colorGenerator 2)*stateHamiltonian s i-stateHamiltonian s i*nativePrimal (colorGenerator 2)) :=
    funext (sourceColourHamiltonian_line s r)
  unfold sourceSymbol
  rw [line,map_add,map_smul,sourceColour_fourier_commutator]

theorem sourceColourFirst_generated (p : PhysicalMomentum) (z : physicalChart) :
    nativeFirst (Fin.castAdd 6 (2:Fin 3)) 1 0 p (sourceState z.val)=
      nativeFull (colorGenerator 2)*sourceSymbol p (sourceState z.val)-
        sourceSymbol p (sourceState z.val)*nativeFull (colorGenerator 2) := by
  have original:=nativeFirst_generated (Fin.castAdd 6 (2:Fin 3)) 1 0 p z
  have variation : stateVariation (Fin.castAdd 6 (2:Fin 3)) 1 0 (sourceState z.val)=
      stateContact (Fin.castAdd 6 (2:Fin 3)) 1 (sourceState z.val) := by
    simp only [stateVariation,stateContact,Pi.zero_apply,zero_smul,sub_zero]
  rw [variation] at original
  have generated := ((hasDerivAt_id (0:ℝ)).smul_const
    (nativeFull (colorGenerator 2)*sourceSymbol p (sourceState z.val)-sourceSymbol p (sourceState z.val)*nativeFull (colorGenerator 2))).const_add
      (sourceSymbol p (sourceState z.val))
  simp only [one_smul] at generated
  exact original.unique (generated.congr_of_eventuallyEq (Eventually.of_forall
    (fun r=>sourceColourSymbol_line p (sourceState z.val) r)))

end LowEnergy.PreparationVacuumPhysicalGaussMaterialContact
