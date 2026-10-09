import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSpinConnectionLie

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumLorentzFieldInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction DiracCliffordRepresentation
open SU7MotherLieAlgebra FullQuantum.StateGreen FullQuantum.CoframeResponse
open PointwiseDiracSpinConnectionLift StageNineLorentzConnectionVariation
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussNativeMatter
open PreparationVacuumSourceFieldFamily PreparationVacuumGaugeSourceInjection PreparationVacuumNativeLocalWard
open PreparationVacuumNativeFieldInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional

/-- The actual original internal two-form action induced by the frame generator. -/
def bivectorGenerator (a : Fin 6) (i j : Fin 6) : ℝ:=
  frameGenerator a (pairFirst i) (pairFirst j)*(if pairSecond i=pairSecond j then 1 else 0)+
  frameGenerator a (pairSecond i) (pairSecond j)*(if pairFirst i=pairFirst j then 1 else 0)-
  frameGenerator a (pairFirst i) (pairSecond j)*(if pairSecond i=pairFirst j then 1 else 0)-
  frameGenerator a (pairSecond i) (pairFirst j)*(if pairFirst i=pairSecond j then 1 else 0)

def bivectorDirection (a : Fin 6) (theta : ℝ) (B : PhysicalBivector) : PhysicalBivector:=
  fun i p=>theta*∑j : Fin 6,bivectorGenerator a i j*B j p

def bivectorMetric (i : Fin 6) : ℝ:=minkowskiInternalSign (pairFirst i)*minkowskiInternalSign (pairSecond i)

 theorem bivectorGenerator_originalAdjoint (a i j : Fin 6) :
    lorentzBracketCoordinates (Pi.single a 1) (Pi.single j 1) i= -bivectorGenerator a j i :=by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [bivectorGenerator,lorentzBracketCoordinates,lorentzMatrix,frameGenerator,lorentzGenerator,
      lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst,lorentzBivectorSecond,pairFirst,pairSecond,minkowskiInternalSign,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_six,Pi.single_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]

 theorem bivectorGenerator_originalMetric (a i j : Fin 6) :
    bivectorMetric i*bivectorGenerator a i j+bivectorMetric j*bivectorGenerator a j i=0 :=by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [bivectorGenerator,bivectorMetric,frameGenerator,lorentzGenerator,
      lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst,lorentzBivectorSecond,pairFirst,pairSecond,minkowskiInternalSign,
      Fin.sum_univ_six,Pi.single_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]

 theorem bivectorDirection_originalBF (a : Fin 6) (theta : ℝ) (B : PhysicalBivector)
    (R : Fin 6→ℝ) (p : Fin 6) :
    (∑i : Fin 6,bivectorDirection a theta B i p*R i)+
      (∑i : Fin 6,B i p*(theta*∑j : Fin 6,lorentzBracketCoordinates (Pi.single a 1) (Pi.single j 1) i*R j))=0 :=by
  simp only [bivectorDirection,Finset.mul_sum,Finset.sum_mul,bivectorGenerator_originalAdjoint,mul_neg,Finset.sum_neg_distrib]
  have exchange : (∑i : Fin 6,∑j : Fin 6,(theta*(bivectorGenerator a i j*B j p))*R i)=
      ∑i : Fin 6,∑j : Fin 6,B i p*(theta*(bivectorGenerator a j i*R j)):=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [exchange]
  simp

 def lorentzFieldDirection (a : Fin 6) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d : FieldData) : FieldData:=
  (0,0,(theta • frameGenerator a)*d.2.2.1,connectionBivectorDirection a theta parameterDerivative d.2.2.2)

 theorem lorentzFieldDirection_state (a : Fin 6) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d : FieldData) : stateDirectionMap (lorentzFieldDirection a theta parameterDerivative d)=
      stateVariation (Fin.natAdd 3 a) theta parameterDerivative (stateDirectionMap d) :=by
  apply Prod.ext
  · change (theta • frameGenerator a)*d.2.2.1=(theta • nativeFrameGenerator (Fin.natAdd 3 a))*d.2.2.1
    rw [frameGenerator_original]
  apply Prod.ext
  · funext mu
    change spinLinear mu (connectionBivectorDirection a theta parameterDerivative d.2.2.2)+nativePrimal 0=
      theta • (nativeMatterGenerator (Fin.natAdd 3 a)*(spinLinear mu d.2.2.2+nativePrimal (d.2.1 mu))-
        (spinLinear mu d.2.2.2+nativePrimal (d.2.1 mu))*nativeMatterGenerator (Fin.natAdd 3 a))-
          parameterDerivative mu • nativeMatterGenerator (Fin.natAdd 3 a)
    rw [map_zero,add_zero,connectionBivectorDirection_state,mul_add,add_mul]
    have source:=spinGauge_direction_original a (d.2.1 mu)
    rw [sub_eq_zero.mp source]
    congr 2
    abel
  · change scalarLinear 0=theta • (nativeMatterGenerator (Fin.natAdd 3 a)*scalarLinear d.1-
      scalarLinear d.1*nativeMatterGenerator (Fin.natAdd 3 a))
    exact spinScalar_direction_original a theta d.1

 def configurationFromFields (c : StageNineHolonomicConfiguration) (d : BasePoint→FieldData) : StageNineHolonomicConfiguration:=
  {c with
    coframe:=fun x=>(d x).2.2.1
    scalar:=fun x=>(d x).1
    gaugeConnection:=fun x mu=>p286CoordinateEquiv.symm ((d x).2.1 mu)
    gravityConnection:=fun x=>lorentzSkewConnectionOfBivectorOneForm ((d x).2.2.2)}

 theorem configurationFromFields_state (c : StageNineHolonomicConfiguration) (d : BasePoint→FieldData) (x : BasePoint) :
    configurationState (configurationFromFields c d) x=stateDirectionMap (d x) :=by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (configurationFromFields c d) x mu)=_
    rw [originalConnection_source]
    change spinCoordinates (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm ((d x).2.2.2)) mu)+
      nativePrimal (show NativeLie from p286CoordinateEquiv (p286CoordinateEquiv.symm ((d x).2.1 mu)))=_
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · rfl

 def lorentzPrimitiveDirection (a : Fin 6) (theta : BasePoint→ℝ) (parameterDerivative : BasePoint→Fin 4→ℝ)
    (c : StageNineHolonomicConfiguration) (d : BasePoint→FieldData) : StageNineHolonomicConfiguration where
  coframe x:=(theta x • frameGenerator a)*(d x).2.2.1
  gravityConnection x:=lorentzSkewConnectionOfBivectorOneForm
    (connectionBivectorDirection a (theta x) (parameterDerivative x) (d x).2.2.2)
  gravityAuxiliary x:=bivectorDirection a (theta x) (c.gravityAuxiliary x)
  gravitySimplicityMultiplier x:=bivectorDirection a (theta x) (c.gravitySimplicityMultiplier x)
  gaugeConnection:=0
  gaugeAuxiliary:=0
  scalar:=0
  matter x:=(theta x:ℂ) • diracMatrixMatterAction (spinGenerator a) (c.matter x)
  conjugateMatter x:=-(theta x:ℂ) • ((c.conjugateMatter x).comp (diracMatrixMatterAction (spinGenerator a)))

 theorem lorentzPrimitive_state (a : Fin 6) (theta : BasePoint→ℝ) (parameterDerivative : BasePoint→Fin 4→ℝ)
    (c : StageNineHolonomicConfiguration) (d : BasePoint→FieldData) (x : BasePoint) :
    configurationState (lorentzPrimitiveDirection a theta parameterDerivative c d) x=
      stateVariation (Fin.natAdd 3 a) (theta x) (parameterDerivative x)
        (configurationState (configurationFromFields c d) x) :=by
  rw [configurationFromFields_state,←lorentzFieldDirection_state]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext mu
    change Quantum.operatorMatrix (FullQuantum.connection (lorentzPrimitiveDirection a theta parameterDerivative c d) x mu)=_
    rw [originalConnection_source]
    change spinCoordinates (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm
        (connectionBivectorDirection a (theta x) (parameterDerivative x) (d x).2.2.2)) mu)+
      nativePrimal (show NativeLie from p286CoordinateEquiv 0)=
        spinLinear mu (connectionBivectorDirection a (theta x) (parameterDerivative x) (d x).2.2.2)+nativePrimal 0
    rw [p286CoordinateEquiv.map_zero,nativePrimal.map_zero,add_zero,add_zero]
    rfl
  · rfl

 theorem lorentzPrimitive_independent_pair (a : Fin 6) (theta : BasePoint→ℝ) (parameterDerivative : BasePoint→Fin 4→ℝ)
    (c : StageNineHolonomicConfiguration) (d : BasePoint→FieldData) (x : BasePoint) :
    (lorentzPrimitiveDirection a theta parameterDerivative c d).conjugateMatter x (c.matter x)+
      c.conjugateMatter x ((lorentzPrimitiveDirection a theta parameterDerivative c d).matter x)=0 :=by
  change (-(theta x:ℂ)) • c.conjugateMatter x (diracMatrixMatterAction (spinGenerator a) (c.matter x))+
      c.conjugateMatter x ((theta x:ℂ) • diracMatrixMatterAction (spinGenerator a) (c.matter x))=0
  rw [map_smul,neg_smul]
  exact neg_add_cancel _

 theorem lorentzField_current_generated (a : Fin 6) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d : FieldData) (p : CanonicalGradedSpatialSource.PhysicalMomentum) (valid : stateDirectionMap d∈validStates) :
    HasDerivAt (fun r : ℝ=>sourceSymbol p (stateDirectionMap d+r • stateDirectionMap (lorentzFieldDirection a theta parameterDerivative d)))
      (nativeFirst (Fin.natAdd 3 a) theta parameterDerivative p (stateDirectionMap d)) 0 :=by
  rw [lorentzFieldDirection_state]
  exact symbol_first_generated p _ _ valid

 theorem lorentzField_stateContact_generated (a : Fin 6) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (d h : FieldData) :
    HasDerivAt (fun r : ℝ=>stateDirectionMap (lorentzFieldDirection a theta parameterDerivative (d+r • h)))
      (stateContact (Fin.natAdd 3 a) theta (stateDirectionMap h)) 0 :=by
  have original:=stateContact_generated (Fin.natAdd 3 a) theta parameterDerivative (stateDirectionMap d) (stateDirectionMap h)
  simpa only [lorentzFieldDirection_state,map_add,map_smul] using original

end LowEnergy.PreparationVacuumLorentzFieldInjection
