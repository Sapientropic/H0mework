import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationActualMixedPreparedKernel
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerClassicalRawFields

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedFieldReturn
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineDynamicBreakingVacuum SU7MotherLieAlgebra
open StageNineLorentzConnectionVariation
open SourceQuantumScalarChart PreparationVacuumLowerClassical
open CanonicalGradedMixedSource PreparationVacuumActualPreparedMixed
open scoped BigOperators

abbrev Field289 := Fin 289→ℝ

-- These offsets are the literal original active-gauge fields order.
def scalarSlot (j : Fin 9) : Fin 289 := ⟨j.val,by omega⟩
def gaugeSlot (mu : Fin 4) (a : Fin 12) : Fin 289 := ⟨9+12*mu.val+a.val,by omega⟩
def coframeSlot (a mu : Fin 4) : Fin 289 := ⟨57+4*a.val+mu.val,by omega⟩
def primalSlot (part : Fin 2) (spin : Fin 4) (color : Fin 3) : Fin 289 :=
  ⟨73+12*part.val+3*spin.val+color.val,by omega⟩
def dualSlot (part : Fin 2) (spin : Fin 4) (color : Fin 3) : Fin 289 :=
  ⟨97+12*part.val+3*spin.val+color.val,by omega⟩
def lorentzSlot (mu : Fin 4) (a : Fin 6) : Fin 289 := ⟨121+6*mu.val+a.val,by omega⟩
def gravitySlot (pair a : Fin 6) : Fin 289 := ⟨145+6*pair.val+a.val,by omega⟩
def multiplierSlot (pair a : Fin 6) : Fin 289 := ⟨181+6*pair.val+a.val,by omega⟩
def gaugeBSlot (pair : Fin 6) (a : Fin 12) : Fin 289 := ⟨217+12*pair.val+a.val,by omega⟩

def originalJColumns : Fin 9→Fin 12 := ![2,3,4,5,6,8,9,10,11]

def fieldScalar (f : Field289) : Scalar :=
  ∑ j : Fin 9,f (scalarSlot j) • orbit (originalUnit (originalJColumns j))

def fieldGauge (f : Field289) (mu : Fin 4) : NativeLie :=
  ∑ a : Fin 12,f (gaugeSlot mu a) • originalUnit a

def fieldCoframe (f : Field289) : LorentzianCoframe := fun a mu=>f (coframeSlot a mu)
def fieldLorentz (f : Field289) : LorentzBivectorOneForm := fun mu a=>f (lorentzSlot mu a)

-- Matter endpoints and auxiliary constraints remain independent restrictions
-- of Field289; they are not silently folded into a bosonic density insertion.
def fieldPrimal (f : Field289) (part : Fin 2) (spin : Fin 4) (color : Fin 3) : ℝ := f (primalSlot part spin color)
def fieldDual (f : Field289) (part : Fin 2) (spin : Fin 4) (color : Fin 3) : ℝ := f (dualSlot part spin color)
def fieldGravityB (f : Field289) (pair a : Fin 6) : ℝ := f (gravitySlot pair a)
def fieldMultiplier (f : Field289) (pair a : Fin 6) : ℝ := f (multiplierSlot pair a)
def fieldGaugeB (f : Field289) (pair : Fin 6) (a : Fin 12) : ℝ := f (gaugeBSlot pair a)

def fieldPrimalComplex (f : Field289) (spin : Fin 4) (color : Fin 3) : ℂ :=
  (fieldPrimal f 0 spin color:ℂ)+Complex.I*(fieldPrimal f 1 spin color:ℂ)

def fieldDualComplex (f : Field289) (spin : Fin 4) (color : Fin 3) : ℂ :=
  (fieldDual f 0 spin color:ℂ)+Complex.I*(fieldDual f 1 spin color:ℂ)

theorem primal_dual_distinct (part part' : Fin 2) (spin spin' : Fin 4) (color color' : Fin 3) :
    primalSlot part spin color≠dualSlot part' spin' color' := by
  intro h
  have same:=congrArg Fin.val h
  simp only [primalSlot,dualSlot] at same
  omega

theorem dual_entry_independent (part : Fin 2) (spin : Fin 4) (color : Fin 3) (value : ℝ) :
    fieldDual (Pi.single (dualSlot part spin color) value) part spin color=value ∧
    ∀ part' spin' color',fieldPrimal (Pi.single (dualSlot part spin color) value) part' spin' color'=0 := by
  constructor
  · simp [fieldDual]
  · intro part' spin' color'
    simp only [fieldPrimal,Pi.single_apply,if_neg (primal_dual_distinct part' part spin' spin color' color)]

theorem fieldScalar_add (f g : Field289) : fieldScalar (f+g)=fieldScalar f+fieldScalar g := by
  simp only [fieldScalar,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem fieldScalar_smul (c : ℝ) (f : Field289) : fieldScalar (c • f)=c • fieldScalar f := by
  simp only [fieldScalar,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

theorem fieldGauge_add (f g : Field289) (mu : Fin 4) : fieldGauge (f+g) mu=fieldGauge f mu+fieldGauge g mu := by
  simp only [fieldGauge,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem fieldGauge_smul (c : ℝ) (f : Field289) (mu : Fin 4) : fieldGauge (c • f) mu=c • fieldGauge f mu := by
  simp only [fieldGauge,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

def scalarWeight (f : Field289) (a : SourceScalarFock.ScalarIndex) : ℝ :=
  SourceScalarFock.scalarCoefficient (scalarCoordinateEquiv.symm (fieldScalar f)) a

theorem fieldScalar_seventy (f : Field289) :
    ∑ a : SourceScalarFock.ScalarIndex,scalarWeight f a • scalarCoordinate a=fieldScalar f := by
  have original:=SourceScalarFock.full_real_scalar_reconstruction (scalarCoordinateEquiv.symm (fieldScalar f))
  have read:=congrArg scalarCoordinateEquiv original
  simp only [map_sum,map_smul,scalarCoordinateEquiv.apply_symm_apply] at read
  apply PiLp.ext
  intro b
  have value:=congrArg (fun v : ScalarCoordinateCarrier=>v b) read
  simpa [scalarCoordinate,scalarWeight,WithLp.ofLp_sum,Finset.sum_apply] using value

theorem gauge_basis_readback (f : Field289) (mu : Fin 4) :
    p286CoordinateEquiv (p286CoordinateEquiv.symm (fieldGauge f mu))=
      ∑ a : Fin 12,f (gaugeSlot mu a) • originalUnit a := by
  exact p286CoordinateEquiv.apply_symm_apply _

theorem scalar_basis_readback (f : Field289) :
    fieldScalar f=∑ j : Fin 9,f (scalarSlot j) • orbit (originalUnit (originalJColumns j)) := rfl

end LowEnergy.PreparationVacuumMixedFieldReturn
