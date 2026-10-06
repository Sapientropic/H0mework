import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Density

/-! Primitive coframe jets generate the actual on-shell current vertex and
its parameter derivative, including the inverse-principal contact. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator ContDiff
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StateGreen CoframeResponse
noncomputable section
local instance readerIndex : DecidableEq Quantum.Index := Classical.decEq _
local instance readerCoframeNormed : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance readerCoframeSeminormed : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance readerCoframeReal : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance readerSourceReal : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

def principalJet (reader : LorentzianCoframe) (e : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ principalMatrix e reader

def lowerJet (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe) (e : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ (lowerMatrix point k) e reader

theorem principalJet_smooth (reader e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    ContDiffAt ℝ ∞ (principalJet reader) e := by
  have generated := (principalMatrix_smooth e nondegenerate).fderiv_right (m := ∞) (by simp)
  exact generated.clm_apply contDiffAt_const

theorem lowerJet_smooth (point : BasePoint) (k : Fin 3 → ℝ) (reader e : LorentzianCoframe)
    (nondegenerate : e.det≠0) : ContDiffAt ℝ ∞ (lowerJet point k reader) e := by
  have generated := (lowerMatrix_smooth point k e nondegenerate).fderiv_right (m := ∞) (by simp)
  exact generated.clm_apply contDiffAt_const

def principalSecond (point : BasePoint) (direction reader : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ (principalJet reader) (actual.coframe point) direction

def lowerSecond (point : BasePoint) (k : Fin 3 → ℝ) (direction reader : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ (lowerJet point k reader) (actual.coframe point) direction

theorem principalJet_parameter (point : BasePoint) (direction reader : LorentzianCoframe) :
    HasDerivAt (fun epsilon => principalJet reader (coframePath point direction epsilon))
      (principalSecond point direction reader) 0 := by
  have generated := (principalJet_smooth reader (actual.coframe point)
    (actual_coframe_nondegenerate point)).differentiableAt (by simp)
  exact generated.hasFDerivAt.comp_hasDerivAt_of_eq 0 (coframePath_derivative point direction)
    (coframePath_zero point direction).symm

theorem lowerJet_parameter (point : BasePoint) (k : Fin 3 → ℝ) (direction reader : LorentzianCoframe) :
    HasDerivAt (fun epsilon => lowerJet point k reader (coframePath point direction epsilon))
      (lowerSecond point k direction reader) 0 := by
  have generated := (lowerJet_smooth point k reader (actual.coframe point)
    (actual_coframe_nondegenerate point)).differentiableAt (by simp)
  exact generated.hasFDerivAt.comp_hasDerivAt_of_eq 0 (coframePath_derivative point direction)
    (coframePath_zero point direction).symm

def onShellCurrent (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (e : LorentzianCoframe) : SourceMatrix :=
  lowerJet point k reader e-Complex.I • (principalJet reader e*coframeHamiltonian point k e)

def onShellCurrentDirection (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) : SourceMatrix :=
  lowerSecond point k direction reader-Complex.I •
    (principalSecond point direction reader*coframeHamiltonian point k (actual.coframe point)+
      principalJet reader (actual.coframe point)*hamiltonianDirection point k direction)

theorem onShellCurrent_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) :
    HasDerivAt (fun epsilon => onShellCurrent point k reader (coframePath point direction epsilon))
      (onShellCurrentDirection point k direction reader) 0 := by
  have product := (principalJet_parameter point direction reader).mul
    (coframeHamiltonian_parameter point k direction)
  have generated := (lowerJet_parameter point k direction reader).sub (product.const_smul Complex.I)
  unfold onShellCurrentDirection onShellCurrent
  rw [coframePath_zero] at generated
  exact generated

def currentForce (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe)
    (e : LorentzianCoframe) : SourceMatrix :=
  (-Complex.I) • (Ring.inverse (principalMatrix e)*onShellCurrent point k reader e)

def currentForceDirection (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) : SourceMatrix :=
  -(Ring.inverse (principalMatrix (actual.coframe point))*principalDirection point direction*
      currentForce point k reader (actual.coframe point))-
    Complex.I • (Ring.inverse (principalMatrix (actual.coframe point))*onShellCurrentDirection point k direction reader)

theorem currentForce_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction reader : LorentzianCoframe) :
    HasDerivAt (fun epsilon => currentForce point k reader (coframePath point direction epsilon))
      (currentForceDirection point k direction reader) 0 := by
  have regular : IsUnit (principalMatrix (coframePath point direction 0)) := by
    rw [coframePath_zero]
    exact principalMatrix_regular (actual.coframe point) (actual_noncharacteristic point)
  have generated := timeSymbol_parameter
    (fun epsilon => principalMatrix (coframePath point direction epsilon))
    (fun epsilon => onShellCurrent point k reader (coframePath point direction epsilon))
    (principalDirection point direction) (onShellCurrentDirection point k direction reader) 0 regular
    (principal_parameter point direction) (onShellCurrent_parameter point k direction reader)
  unfold currentForceDirection currentForce
  rw [coframePath_zero] at generated
  exact generated

theorem currentForce_actual (point : BasePoint) (k : Fin 3 → ℝ) (reader : LorentzianCoframe) :
    currentForce point k reader (actual.coframe point)=hamiltonianDirection point k reader := by
  unfold currentForce onShellCurrent principalJet lowerJet hamiltonianDirection
  exact (timeSymbol_on_shell (principalMatrix (actual.coframe point)) (lowerMatrix point k (actual.coframe point))
    (principalDirection point reader) (lowerDirection point k reader)).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
