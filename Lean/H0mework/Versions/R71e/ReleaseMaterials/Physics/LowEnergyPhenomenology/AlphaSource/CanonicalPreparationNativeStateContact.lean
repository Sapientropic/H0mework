import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationWeightedChargePreparedActionReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeLocalWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair StageNineLorentzConnectionVariation
open DiracExteriorMatterAction SU7MotherLieAlgebra StageNineHolonomicField SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert GaussNativeMatter
open FullQuantum.StateGreen PreparationVacuumGaugeSourceInjection PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback PreparationVacuumMixedFieldReturn
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

/-- The original three source-color generators and the six primitive spin lifts. -/
def nativeMatterGenerator (n : Fin 9) : SourceMatrix:=
  Fin.addCases (fun g : Fin 3=>nativePrimal (show NativeLie from p286CoordinateEquiv (sourceColorP286Generator g)))
    (fun a : Fin 6=>spinLinear 0 (Pi.single 0 (Pi.single a 1))) n

def nativeFrameGenerator (n : Fin 9) : LorentzianCoframe:=
  Fin.addCases (fun _ : Fin 3=>0)
    (fun a : Fin 6=>fun i j=>lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 (Pi.single a 1)) 0 i j) n

theorem nativeMatterGenerator_color_original (g : Fin 3) :
    nativeMatterGenerator (Fin.castAdd 6 g)=Quantum.operatorMatrix
      (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator g))) :=by
  simp only [nativeMatterGenerator,Fin.addCases_left]
  change Quantum.operatorMatrix (diracExteriorMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator g)))))=_
  rw [LinearEquiv.symm_apply_apply]

theorem nativeMatterGenerator_spin_original (a : Fin 6) :
    nativeMatterGenerator (Fin.natAdd 3 a)=spinLinear 0 (Pi.single 0 (Pi.single a 1)) :=by
  simp [nativeMatterGenerator]

theorem nativeFrameGenerator_spin_original (a : Fin 6) :
    nativeFrameGenerator (Fin.natAdd 3 a)=
      lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 (Pi.single a 1)) 0 :=by
  simp [nativeFrameGenerator]

/-- The affine local source action keeps the parameter derivative separate from field contact. -/
def stateVariation (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ) (s : ActionState) : ActionState:=
  ((theta • nativeFrameGenerator n)*s.1,
    (fun mu=>theta • (nativeMatterGenerator n*s.2.1 mu-s.2.1 mu*nativeMatterGenerator n)-
      derivative mu • nativeMatterGenerator n),
    theta • (nativeMatterGenerator n*s.2.2-s.2.2*nativeMatterGenerator n))

def stateContact (n : Fin 9) (theta : ℝ) (d : ActionState) : ActionState:=
  ((theta • nativeFrameGenerator n)*d.1,
    (fun mu=>theta • (nativeMatterGenerator n*d.2.1 mu-d.2.1 mu*nativeMatterGenerator n)),
    theta • (nativeMatterGenerator n*d.2.2-d.2.2*nativeMatterGenerator n))

theorem stateVariation_affine (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (s d : ActionState) (r : ℝ) :
    stateVariation n theta derivative (s+r • d)=stateVariation n theta derivative s+r • stateContact n theta d :=by
  apply Prod.ext
  · change (theta • nativeFrameGenerator n)*(s.1+r • d.1)=
      (theta • nativeFrameGenerator n)*s.1+r • ((theta • nativeFrameGenerator n)*d.1)
    simp only [mul_add,mul_smul_comm]
  apply Prod.ext
  · funext mu
    change theta • (nativeMatterGenerator n*(s.2.1 mu+r • d.2.1 mu)-
      (s.2.1 mu+r • d.2.1 mu)*nativeMatterGenerator n)-derivative mu • nativeMatterGenerator n=
      (theta • (nativeMatterGenerator n*s.2.1 mu-s.2.1 mu*nativeMatterGenerator n)-
        derivative mu • nativeMatterGenerator n)+
          r • (theta • (nativeMatterGenerator n*d.2.1 mu-d.2.1 mu*nativeMatterGenerator n))
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub]
    module
  · change theta • (nativeMatterGenerator n*(s.2.2+r • d.2.2)-
      (s.2.2+r • d.2.2)*nativeMatterGenerator n)=
      theta • (nativeMatterGenerator n*s.2.2-s.2.2*nativeMatterGenerator n)+
        r • (theta • (nativeMatterGenerator n*d.2.2-d.2.2*nativeMatterGenerator n))
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_add,smul_sub]
    module

theorem stateContact_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (s d : ActionState) :
    HasDerivAt (fun r : ℝ=>stateVariation n theta derivative (s+r • d)) (stateContact n theta d) 0 :=by
  have actual:=((hasDerivAt_id (0:ℝ)).smul_const (stateContact n theta d)).const_add (stateVariation n theta derivative s)
  convert! actual using 1
  · funext r;exact stateVariation_affine n theta derivative s d r
  · simp only [one_smul]

theorem sourceStateContact_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (z : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ=>stateVariation n theta derivative (ambientState (r • force,z)))
      (stateContact n theta (fieldDirection force)) 0 :=by
  have source:=stateContact_generated n theta derivative (sourceState z) (fieldDirection force)
  have ray (r : ℝ) : ambientState (r • force,z)=sourceState z+r • fieldDirection force:=by
    simp only [ambientState,map_smul]
    rfl
  simpa only [ray] using source

theorem stateContact_coordinate_complement (n : Fin 9) (theta : ℝ) (force : Field289) (z : SourceCoordinateSlice) :
    stateContact n theta (fieldDirection force)=
      stateContact n theta (sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z))+
        stateContact n theta (complement force z) :=by
  have source:=stateVariation_affine n theta (0:Fin 4→ℝ)
    (sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z)) (complement force z) 1
  have split : sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z)+complement force z=fieldDirection force:=by
    rw [complement]
    module
  simpa only [one_smul,split,stateVariation,stateContact,Pi.zero_apply,zero_smul,sub_zero] using source

end LowEnergy.PreparationVacuumNativeLocalWard
