import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMixedFieldMap
import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.CanonicalCoframe

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedFieldReturn
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open Electromagnetic.CanonicalCoframe
open scoped BigOperators Matrix Matrix.Norms.L2Operator ContDiff
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

abbrev NativeField := SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalCoframe.FieldDirection

def sourceField (f : Field289) : NativeField where
  coframe:=fieldCoframe f
  lorentz:=fieldLorentz f
  gauge:=fun mu=>p286CoordinateEquiv.symm (fieldGauge f mu)
  scalar:=fieldScalar f


def densityPrincipalAt (mu : Fin 4) (e : LorentzianCoframe) : SourceMatrix :=
  ((|e.det|:ℝ):ℂ) • coefficientMatrix mu e

def densityPrincipalFirstAt (reader : NativeField) (mu : Fin 4) (e : LorentzianCoframe) : SourceMatrix :=
  ((|e.det|:ℝ):ℂ) • coefficientJetAt reader.coframe mu e+
    (volumeJetAt reader.coframe e:ℂ) • coefficientMatrix mu e

theorem firstPrincipal_at_source (reader : NativeField) (mu : Fin 4) :
    densityPrincipalFirstAt reader mu (actual.coframe 0)=densityPrincipalJet reader mu := rfl

theorem densityPrincipal_parameter (force : NativeField) (mu : Fin 4) :
    HasDerivAt (fun t=>densityPrincipalAt mu (coframePath 0 force.coframe t))
      (densityPrincipalJet force mu) 0 := by
  have volume:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (volume_parameter 0 force.coframe)
  have derivative:=volume.smul (coefficientJet_parameter force.coframe mu)
  unfold densityPrincipalAt densityPrincipalJet sourceVolume
  convert! derivative using 1
  simp only [Function.comp_apply,Complex.ofRealCLM_apply,coframePath_zero]

theorem mixedPrincipal_generated (reader force : NativeField) (mu : Fin 4) :
    HasDerivAt (fun t=>densityPrincipalFirstAt reader mu (coframePath 0 force.coframe t))
      (densityPrincipalSecond reader force mu) 0 := by
  have volume:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (volume_parameter 0 force.coframe)
  have second:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (volumeSecond_parameter reader.coframe force.coframe)
  have derivative:=(volume.smul (coefficientSecond_parameter reader.coframe force.coframe mu)).add
    (second.smul (coefficientJet_parameter force.coframe mu))
  unfold densityPrincipalFirstAt densityPrincipalSecond sourceVolume
  convert! derivative using 1
  simp only [Function.comp_apply,Complex.ofRealCLM_apply,coframePath_zero,coefficientJetAt,coefficientJet,
    volumeJetAt,volumeDirection]
  abel

def connectionPath (force : NativeField) (mu : Fin 4) (t : ℝ) : SourceMatrix :=
  sourceConnection mu+t • connectionDirection force mu

def scalarPath (force : NativeField) (t : ℝ) : SourceMatrix :=
  sourceScalar+t • scalarDirection force

theorem connectionPath_derivative (force : NativeField) (mu : Fin 4) :
    HasDerivAt (connectionPath force mu) (connectionDirection force mu) 0 := by
  unfold connectionPath
  convert! ((hasDerivAt_id (0:ℝ)).smul_const (connectionDirection force mu)).const_add (sourceConnection mu) using 1
  simp

theorem scalarPath_derivative (force : NativeField) :
    HasDerivAt (scalarPath force) (scalarDirection force) 0 := by
  unfold scalarPath
  convert! ((hasDerivAt_id (0:ℝ)).smul_const (scalarDirection force)).const_add sourceScalar using 1
  simp

def lowerFirstPath (reader force : NativeField) (t : ℝ) : SourceMatrix :=
  (∑ mu : Fin 4,
    (densityPrincipalFirstAt reader mu (coframePath 0 force.coframe t)*connectionPath force mu t+
      densityPrincipalAt mu (coframePath 0 force.coframe t)*connectionDirection reader mu))+
    (volumeJetAt reader.coframe (coframePath 0 force.coframe t):ℂ) • scalarPath force t+
    ((|(coframePath 0 force.coframe t).det|:ℝ):ℂ) • scalarDirection reader

theorem mixedLower_generated (reader force : NativeField) :
    HasDerivAt (lowerFirstPath reader force) (mixedLowerZero reader force) 0 := by
  have connection (mu : Fin 4) :=
    ((mixedPrincipal_generated reader force mu).mul (connectionPath_derivative force mu)).add
      ((densityPrincipal_parameter force mu).mul_const (connectionDirection reader mu))
  have firstScalar := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (volumeSecond_parameter reader.coframe force.coframe)).smul (scalarPath_derivative force)
  have secondScalar := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
    (volume_parameter 0 force.coframe)).smul_const (scalarDirection reader)
  have derivative := ((HasDerivAt.fun_sum (fun mu (_ : mu∈(Finset.univ : Finset (Fin 4)))=>connection mu)).add firstScalar).add secondScalar
  unfold lowerFirstPath mixedLowerZero
  convert! derivative using 1
  simp only [connectionPath,scalarPath,zero_smul,add_zero,coframePath_zero,firstPrincipal_at_source,
    Function.comp_apply,Complex.ofRealCLM_apply,volumeJetAt,volumeDirection]
  simp only [Finset.sum_add_distrib,add_assoc]
  abel

def densityFirstPath (reader force : NativeField) (i : Fin 4) (t : ℝ) : SourceMatrix :=
  (Fin.cases (lowerFirstPath reader force t)
    (fun j=>Complex.I • densityPrincipalFirstAt reader j.succ (coframePath 0 force.coframe t)) i)-
    Complex.I • (densityPrincipalFirstAt reader 0 (coframePath 0 force.coframe t)*sourceHamiltonianCoefficients i)

theorem mixedDensity_generated (reader force : NativeField) (i : Fin 4) :
    HasDerivAt (densityFirstPath reader force i) (mixedDensityCoefficients reader force i) 0 := by
  have low : HasDerivAt
      (fun t : ℝ=>Fin.cases (motive:=fun _ : Fin 4=>SourceMatrix) (lowerFirstPath reader force t)
        (fun j=>Complex.I • densityPrincipalFirstAt reader j.succ (coframePath 0 force.coframe t)) i)
      (Fin.cases (motive:=fun _ : Fin 4=>SourceMatrix) (mixedLowerZero reader force) (fun j=>Complex.I • densityPrincipalSecond reader force j.succ) i) 0 := by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact mixedLower_generated reader force
    · exact (mixedPrincipal_generated reader force j.succ).const_smul Complex.I
  exact low.sub (((mixedPrincipal_generated reader force 0).mul_const (sourceHamiltonianCoefficients i)).const_smul Complex.I)

-- The varying ket-shell term is distinct from the density seagull above.
def shellFirstPath (reader force : NativeField) (i : Fin 4) (t : ℝ) : SourceMatrix :=
  (-Complex.I) • (densityPrincipalFirstAt reader 0 (coframePath 0 force.coframe t)*
    (t • fieldHamiltonianCoefficients force i))

theorem shellContact_generated (reader force : NativeField) (i : Fin 4) :
    HasDerivAt (shellFirstPath reader force i) (shellContactCoefficients reader force i) 0 := by
  have shell := (hasDerivAt_id (0:ℝ)).smul_const (fieldHamiltonianCoefficients force i)
  have derivative := ((mixedPrincipal_generated reader force 0).mul shell).const_smul (-Complex.I)
  unfold shellFirstPath shellContactCoefficients
  convert! derivative using 1
  simp only [id_eq,zero_smul,mul_zero,zero_add,one_smul,coframePath_zero,firstPrincipal_at_source]

end LowEnergy.PreparationVacuumMixedFieldReturn
