import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNativePreparedResponse
import H0mework.Physics.GaugeStanding.LieRepresentation
import H0mework.Physics.Matter.ExteriorMotherLieYukawaDerivation

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeFieldInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse StageNineEnrichedProofFreeSource
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorBreakingYukawa SU7ExteriorMatterRepresentation
open StageNineExteriorMotherLieYukawaDerivation StageNineP286LinkedActiveLieRepresentation
open StageNineDiracDualYukawaSpinJurisdiction StageNineP286GaugeAuxiliaryVariation
open Stage9C.Material.SpinPair SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open GaussNativeMatter GaussHistoryHilbert PreparationVacuumSourceFieldFamily
open PreparationVacuumGaugeSourceInjection PreparationVacuumNativeLocalWard
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional

def nativeMother (a : NativeLie) : SU7MotherLieMatrix:=p286LieBlockEmbed (p286CoordinateEquiv.symm a)

theorem nativePrimal_mother (a : NativeLie) :
    nativePrimal a=Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a)) :=rfl

private theorem internal_spin_commute (M : SU7MotherLieMatrix) (D : DiracMatrix) (v : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction M (diracMatrixMatterAction D v)=
      diracMatrixMatterAction D (diracExteriorMotherLieAction M v) :=by
  simpa only [diracExteriorMotherLieAction,LinearMap.comp_apply] using
    (LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal D (exteriorSpinorMotherLieAction M)) v).symm

theorem repairedYukawa_motherLeibniz (M : SU7MotherLieMatrix) (phi : ExteriorBreakingScalarCarrier)
    (v : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction M (diracDualRightChiralYukawaAction phi v)=
      diracDualRightChiralYukawaAction (exteriorMotherLieAction 4 M phi) v+
        diracDualRightChiralYukawaAction phi (diracExteriorMotherLieAction M v) :=by
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  rw [diracExteriorYukawaInternalAction_motherLieAction,internal_spin_commute]

theorem scalarAction_mother (a : NativeLie) (phi : Scalar) :
    scalarCoordinateEquiv.symm (action phi a)=
      exteriorMotherLieAction 4 (nativeMother a) (scalarCoordinateEquiv.symm phi) :=by
  change scalarCoordinateEquiv.symm (scalarCoordinateEquiv _)=_
  exact scalarCoordinateEquiv.symm_apply_apply _

theorem originalScalar_commutator (a : NativeLie) (phi : Scalar) :
    scalarLinear (action phi a)=nativePrimal a*scalarLinear phi-scalarLinear phi*nativePrimal a :=by
  rw [nativePrimal_mother]
  change Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (action phi a)))=
    Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a))*
      Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm phi))-
    Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm phi))*
      Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a))
  rw [←Quantum.matrix_composition,←Quantum.matrix_composition,←map_sub]
  apply congrArg Quantum.operatorMatrix
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,scalarAction_mother]
  have source:=repairedYukawa_motherLeibniz (nativeMother a) (scalarCoordinateEquiv.symm phi) v
  rw [source]
  abel

theorem originalGauge_commutator (a b : NativeLie) :
    nativePrimal (show NativeLie from p286CoordinateLieBracket a b)=
      nativePrimal a*nativePrimal b-nativePrimal b*nativePrimal a :=by
  rw [nativePrimal_mother,nativePrimal_mother,nativePrimal_mother,
    ←Quantum.matrix_composition,←Quantum.matrix_composition,←map_sub]
  have source : nativeMother (show NativeLie from p286CoordinateLieBracket a b)=
      suLieBracket (nativeMother a) (nativeMother b):=by
    unfold nativeMother p286CoordinateLieBracket
    rw [LinearEquiv.symm_apply_apply,p286LieBlockEmbed_bracket]
  rw [source,diracExteriorMotherLieAction_bracket]

def colorLie (g : Fin 3) : NativeLie:=p286CoordinateEquiv (sourceColorP286Generator g)

theorem colorLie_original (g : Fin 3) : nativePrimal (colorLie g)=nativeMatterGenerator (Fin.castAdd 6 g) :=by
  simp only [nativeMatterGenerator,Fin.addCases_left,colorLie]

def scalarDirection (g : Fin 3) (theta : ℝ) (phi : Scalar) : Scalar:=theta • action phi (colorLie g)

def gaugeDirection (g : Fin 3) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (A : Fin 4→NativeLie) : Fin 4→NativeLie:=
  fun mu=>theta • (show NativeLie from p286CoordinateLieBracket (colorLie g) (A mu))-
    parameterDerivative mu • colorLie g

theorem scalarDirection_source (g : Fin 3) (theta : ℝ) (phi : Scalar) :
    scalarLinear (scalarDirection g theta phi)=
      theta • (nativeMatterGenerator (Fin.castAdd 6 g)*scalarLinear phi-
        scalarLinear phi*nativeMatterGenerator (Fin.castAdd 6 g)) :=by
  change (scalarLinear.restrictScalars ℝ) (theta • action phi (colorLie g))=_
  rw [map_smul]
  change theta • scalarLinear (action phi (colorLie g))=_
  rw [originalScalar_commutator,colorLie_original]

theorem gaugeDirection_source (g : Fin 3) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (A : Fin 4→NativeLie) (mu : Fin 4) :
    nativePrimal (gaugeDirection g theta parameterDerivative A mu)=
      theta • (nativeMatterGenerator (Fin.castAdd 6 g)*nativePrimal (A mu)-
        nativePrimal (A mu)*nativeMatterGenerator (Fin.castAdd 6 g))-
      parameterDerivative mu • nativeMatterGenerator (Fin.castAdd 6 g) :=by
  rw [gaugeDirection,map_sub,map_smul,map_smul,originalGauge_commutator,colorLie_original]

theorem scalarDirection_vacuum (g : Fin 3) (theta : ℝ) : scalarDirection g theta vacuum=0 :=by
  have source:=sourceColorP286Generator_vacuum_zero g
  change scalarMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator g))
    (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)=0 at source
  unfold scalarDirection action colorLie vacuum
  change theta • scalarMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator g))))
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)=0
  rw [LinearEquiv.symm_apply_apply,source,smul_zero]

theorem originalSpin_gauge_commute (a : NativeLie) (omega : StageNineLorentzConnectionVariation.LorentzBivectorOneForm)
    (mu : Fin 4) : nativePrimal a*spinLinear mu omega=spinLinear mu omega*nativePrimal a :=by
  rw [nativePrimal_mother]
  change Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a))*
    Quantum.operatorMatrix (diracMatrixMatterAction (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift
      (StageNineLorentzConnectionVariation.lorentzSkewConnectionOfBivectorOneForm omega) mu))=
    Quantum.operatorMatrix (diracMatrixMatterAction (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift
      (StageNineLorentzConnectionVariation.lorentzSkewConnectionOfBivectorOneForm omega) mu))*
        Quantum.operatorMatrix (diracExteriorMotherLieAction (nativeMother a))
  rw [←Quantum.matrix_composition,←Quantum.matrix_composition]
  apply congrArg Quantum.operatorMatrix
  apply LinearMap.ext
  intro v
  exact internal_spin_commute _ _ _

def colorFieldDirection (g : Fin 3) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d : FieldData) : FieldData:=
  (scalarDirection g theta d.1,gaugeDirection g theta parameterDerivative d.2.1,0,0)

theorem colorFieldDirection_state (g : Fin 3) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d : FieldData) : stateDirectionMap (colorFieldDirection g theta parameterDerivative d)=
      stateVariation (Fin.castAdd 6 g) theta parameterDerivative (stateDirectionMap d) :=by
  apply Prod.ext
  · change 0=
      (theta • nativeFrameGenerator (Fin.castAdd 6 g))*d.2.2.1
    simp [nativeFrameGenerator]
  apply Prod.ext
  · funext mu
    change spinLinear mu 0+nativePrimal (gaugeDirection g theta parameterDerivative d.2.1 mu)=
      theta • (nativeMatterGenerator (Fin.castAdd 6 g)*(spinLinear mu d.2.2.2+nativePrimal (d.2.1 mu))-
        (spinLinear mu d.2.2.2+nativePrimal (d.2.1 mu))*nativeMatterGenerator (Fin.castAdd 6 g))-
          parameterDerivative mu • nativeMatterGenerator (Fin.castAdd 6 g)
    rw [map_zero,zero_add,gaugeDirection_source,←colorLie_original,mul_add,add_mul,
      originalSpin_gauge_commute]
    congr 2
    abel
  · change scalarLinear (scalarDirection g theta d.1)=_
    exact scalarDirection_source g theta d.1

theorem colorNativeCurrent_originalFields (g : Fin 3) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d : FieldData) (p : CanonicalGradedSpatialSource.PhysicalMomentum)
    (valid : stateDirectionMap d∈PreparationVacuumNonlinearFieldCurve.validStates) :
    HasDerivAt (fun r : ℝ=>PreparationVacuumActionFieldLift.sourceSymbol p
      (stateDirectionMap d+r • stateDirectionMap (colorFieldDirection g theta parameterDerivative d)))
      (nativeFirst (Fin.castAdd 6 g) theta parameterDerivative p (stateDirectionMap d)) 0 :=by
  rw [colorFieldDirection_state]
  exact PreparationVacuumActionFieldLift.symbol_first_generated p _ _ valid

end LowEnergy.PreparationVacuumNativeFieldInjection
