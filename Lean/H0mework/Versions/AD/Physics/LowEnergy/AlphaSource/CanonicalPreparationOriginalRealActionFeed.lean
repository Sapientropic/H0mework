import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationOrderedConjugatedSignal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumOrderedRealSignal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumOriginalDensity PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open CanonicalPreparationCore.Completed GaussComposite.SourceGraph
open PreparationVacuumSourceFieldFamily PreparationVacuumFullFieldRiesz
open Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
attribute [local irreducible] noetherReader noetherReaderContact preparedDual preparedPrimal noetherPreparedCurrent
  oppositeCurrent historyConjugation

abbrev PhysicalPosition:=Fin 3→ℝ
abbrev MomentumCoefficients:=PhysicalMomentum→₀ℂ

def phase (k : PhysicalMomentum) (x : PhysicalPosition) : ℂ:=
  Complex.exp (Complex.I*(((∑i : Fin 3,k i*x i):ℝ):ℂ))

theorem phase_add (p k : PhysicalMomentum) (x : PhysicalPosition) : phase (p+k) x=phase p x*phase k x :=by
  unfold phase
  have dot : (∑i : Fin 3,((p+k) i*x i : ℝ))=(∑i : Fin 3,p i*x i)+(∑i : Fin 3,k i*x i):=by
    simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  rw [dot,Complex.ofReal_add,mul_add,Complex.exp_add]

theorem phase_star (k : PhysicalMomentum) (x : PhysicalPosition) : phase (-k) x=star (phase k x) :=by
  unfold phase
  simp only [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib,Complex.ofReal_neg,mul_neg]
  change Complex.exp _=(starRingEnd ℂ) (Complex.exp _)
  rw [←Complex.exp_conj]
  simp only [map_mul,Complex.conj_I,Complex.conj_ofReal,neg_mul]

def positionRead (x : PhysicalPosition) : MomentumCoefficients→ₗ[ℂ] ℂ:=
  Finsupp.linearCombination ℂ (fun k=>phase k x)

theorem positionRead_single (x : PhysicalPosition) (k : PhysicalMomentum) (c : ℂ) :
    positionRead x (Finsupp.single k c)=c*phase k x :=Finsupp.linearCombination_single _ _ _

/-- All four coefficients use the same source profile, preparation and fixed-pi chart. -/
def crossRight (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual (oppositeCoordinates q) h age (noetherReader reader q.p q.F h (preparedPrimal q h age))

def crossLeft (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age (noetherReader reader (-q.p) q.F h (preparedPrimal (oppositeCoordinates q) h age))

def momentumWave (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) (x : PhysicalPosition) : H→L[ℂ] ℂ:=
  phase (-(q.p+q.k)) x • preparedDual q h age+
    phase (q.p+q.k) x • preparedDual (oppositeCoordinates q) h age

def readerWave (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) (x : PhysicalPosition) : H:=
  phase q.p x • noetherReader reader q.p q.F h (preparedPrimal q h age)+
    phase (-q.p) x • noetherReader reader (-q.p) q.F h (preparedPrimal (oppositeCoordinates q) h age)

def complexDensity (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) (x : PhysicalPosition) : ℂ:=
  momentumWave q h age x (readerWave q reader h age x)

def complexDensityCoefficients (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : MomentumCoefficients:=
  Finsupp.single (-q.k) (noetherPreparedCurrent q reader h age)+
    Finsupp.single q.k (oppositeCurrent q reader h age)+
    Finsupp.single (2 • q.p+q.k) (crossRight q reader h age)+
    Finsupp.single (-(2 • q.p+q.k)) (crossLeft q reader h age)

theorem complexDensity_source (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) (x : PhysicalPosition) :
    positionRead x (complexDensityCoefficients q reader h age)=complexDensity q reader h age x :=by
  have forward : -(q.p+q.k)+q.p= -q.k:=by abel
  have reverse : (q.p+q.k)+ -q.p=q.k:=by abel
  have cr : (q.p+q.k)+q.p=2 • q.p+q.k:=by module
  have cl : -(q.p+q.k)+ -q.p= -(2 • q.p+q.k):=by module
  unfold complexDensityCoefficients complexDensity momentumWave readerWave
  simp only [map_add,positionRead_single,add_apply,smul_apply,
    map_smul,smul_eq_mul,noetherPreparedCurrent,crossRight,crossLeft,oppositeCurrent_actual]
  have pf:=phase_add (-(q.p+q.k)) q.p x
  have pr:=phase_add (q.p+q.k) (-q.p) x
  have pc:=phase_add (q.p+q.k) q.p x
  have pd:=phase_add (-(q.p+q.k)) (-q.p) x
  rw [forward] at pf
  rw [reverse] at pr
  rw [cr] at pc
  rw [cl] at pd
  have oppositeMomentum : (oppositeCoordinates q).p= -q.p:=rfl
  have oppositeFrame : (oppositeCoordinates q).F=q.F:=rfl
  rw [oppositeMomentum,oppositeFrame,pf,pr,pc,pd]
  ring

/-- This is the original Re-density of the independent canonical momentum and primal waves. -/
def realDensity (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) (x : PhysicalPosition) : ℂ:=
  ((complexDensity q reader h age x).re : ℂ)

/-- Physical momentum keys are actual: overlapping modes add before any readout. -/
def realDensityCoefficients (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : MomentumCoefficients:=
  Finsupp.single (-q.k) ((1/2:ℂ)*(noetherPreparedCurrent q reader h age+star (oppositeCurrent q reader h age)))+
    Finsupp.single q.k ((1/2:ℂ)*(oppositeCurrent q reader h age+star (noetherPreparedCurrent q reader h age)))+
    Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(crossRight q reader h age+star (crossLeft q reader h age)))+
    Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(crossLeft q reader h age+star (crossRight q reader h age)))

theorem realDensity_generated (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) (x : PhysicalPosition) :
    positionRead x (realDensityCoefficients q reader h age)=realDensity q reader h age x :=by
  rw [realDensity,Complex.re_eq_add_conj,←complexDensity_source]
  simp only [realDensityCoefficients,complexDensityCoefficients,map_add,positionRead_single,map_mul,map_add,
    ←Complex.star_def,star_star]
  rw [←phase_star,←phase_star,←phase_star,←phase_star]
  simp only [neg_neg]
  ring

theorem realDensity_whole_reverse (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    realDensityCoefficients q reader h age=
      Finsupp.single (-q.k) ((1/2:ℂ)*(noetherPreparedCurrent q reader h age+conjugatedOppositeCurrent q reader h age))+
        Finsupp.single q.k ((1/2:ℂ)*(oppositeCurrent q reader h age+star (noetherPreparedCurrent q reader h age)))+
        Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(crossRight q reader h age+star (crossLeft q reader h age)))+
        Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(crossLeft q reader h age+star (crossRight q reader h age))) :=by
  rw [conjugatedOppositeCurrent_source]
  rfl

def crossRightCoordinates (q : PhysicalResponsePoint) : PhysicalResponsePoint:=
  {q with
    k := -(2 • q.p+q.k)
    z := q.w
    w := q.w
    left := q.right
    lc := q.rc
    ls := q.rs}

def crossLeftCoordinates (q : PhysicalResponsePoint) : PhysicalResponsePoint:=
  {q with
    p := -q.p
    k := 2 • q.p+q.k
    z := q.z
    w := q.z
    right := q.left
    rc := q.lc
    rs := q.ls}

theorem crossRight_actual (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    crossRight q reader h age=noetherPreparedCurrent (crossRightCoordinates q) reader h age :=by
  have momenta : (crossRightCoordinates q).p+(crossRightCoordinates q).k=
      (oppositeCoordinates q).p+(oppositeCoordinates q).k:=by change q.p+ -(2 • q.p+q.k)= -q.p+ -q.k;module
  unfold crossRight noetherPreparedCurrent preparedDual independentDual preparedPrimal
  rw [momenta]
  rfl

theorem crossLeft_actual (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) :
    crossLeft q reader h age=noetherPreparedCurrent (crossLeftCoordinates q) reader h age :=by
  have momenta : (crossLeftCoordinates q).p+(crossLeftCoordinates q).k=q.p+q.k:=by
    change -q.p+(2 • q.p+q.k)=q.p+q.k
    module
  unfold crossLeft noetherPreparedCurrent preparedDual independentDual preparedPrimal
  rw [momenta]
  rfl

def coefficientSlope (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ) : MomentumCoefficients:=
  let F:=noetherPreparedSlope q reader force age
  let R:=noetherPreparedSlope (oppositeCoordinates q) reader force age
  let DR:=noetherPreparedSlope (crossRightCoordinates q) reader force age
  let DL:=noetherPreparedSlope (crossLeftCoordinates q) reader force age
  Finsupp.single (-q.k) ((1/2:ℂ)*(F+star R))+Finsupp.single q.k ((1/2:ℂ)*(R+star F))+
    Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(DR+star DL))+
      Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(DL+star DR))

private theorem star_derivative {f : ℝ→ℂ} {d : ℂ} {r : ℝ} (source : HasDerivAt f d r) :
    HasDerivAt (fun s=>star (f s)) (star d) r :=by
  have generated:=Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r source
  convert! generated using 1

private theorem single_derivative {f : ℝ→ℂ} {d : ℂ} {r : ℝ}
    (k wave : PhysicalMomentum) (source : HasDerivAt f d r) :
    HasDerivAt (fun s=>Finsupp.single k (f s) wave) (Finsupp.single k d wave) r :=by
  by_cases same : k=wave
  · simpa only [Finsupp.single_apply,if_pos same] using source
  · simp only [Finsupp.single_apply,if_neg same]
    exact hasDerivAt_const r (0:ℂ)

theorem realDensityCoefficients_generated (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (momentum : PhysicalMomentum) :
    HasDerivAt (fun r : ℝ=>realDensityCoefficients q reader (r • force) age momentum)
      (coefficientSlope q reader force age momentum) 0 :=by
  have F:=noetherPreparedCurrent_generated q reader force age hz hw
  have R:=noetherPreparedCurrent_generated (oppositeCoordinates q) reader force age hw hz
  have DR:=noetherPreparedCurrent_generated (crossRightCoordinates q) reader force age hw hw
  have DL:=noetherPreparedCurrent_generated (crossLeftCoordinates q) reader force age hz hz
  have a:=(F.add (star_derivative R)).const_mul (1/2:ℂ)
  have b:=(R.add (star_derivative F)).const_mul (1/2:ℂ)
  have c:=(DR.add (star_derivative DL)).const_mul (1/2:ℂ)
  have d:=(DL.add (star_derivative DR)).const_mul (1/2:ℂ)
  have sa:=single_derivative (-q.k) momentum a
  have sb:=single_derivative q.k momentum b
  have sc:=single_derivative (2 • q.p+q.k) momentum c
  have sd:=single_derivative (-(2 • q.p+q.k)) momentum d
  convert! ((sa.add sb).add sc).add sd using 1
  all_goals simp only [realDensityCoefficients,coefficientSlope,Finsupp.add_apply,
    oppositeCurrent_actual,crossRight_actual,crossLeft_actual,Pi.add_apply]
  all_goals funext r;rfl

/-- Literal collision-safe all289 Euler feed; the source minus occurs once. -/
def realEulerCoefficients (q : PhysicalResponsePoint) (h : Field289) (age : ℝ) (momentum : PhysicalMomentum) : Fin 289→ℂ:=
  fun i=> -realDensityCoefficients q (PreparationVacuumActionFieldLift.fieldUnit i) h age momentum

def realEulerSlope (q : PhysicalResponsePoint) (force : Field289) (age : ℝ) (momentum : PhysicalMomentum) : Fin 289→ℂ:=
  fun i=> -coefficientSlope q (PreparationVacuumActionFieldLift.fieldUnit i) force age momentum

theorem realEulerCoefficients_generated (q : PhysicalResponsePoint) (force : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (momentum : PhysicalMomentum) :
    HasDerivAt (fun r : ℝ=>realEulerCoefficients q (r • force) age momentum)
      (realEulerSlope q force age momentum) 0 :=
  hasDerivAt_pi.mpr fun i=>(realDensityCoefficients_generated q (PreparationVacuumActionFieldLift.fieldUnit i) force age hz hw momentum).neg

end LowEnergy.PreparationVacuumOrderedRealSignal
