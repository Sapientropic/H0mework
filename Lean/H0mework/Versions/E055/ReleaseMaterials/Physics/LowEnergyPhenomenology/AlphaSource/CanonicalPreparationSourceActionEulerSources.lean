import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceFixedMomentumEuler
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalRealReaction
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNoetherSourceWardChannels

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMatterEulerFeedback
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumIndependentMomentumReturn
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity PreparationVacuumRealReaction
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumOrderedRealSignal PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumActionFieldLift PreparationVacuumMixedFieldReturn
open Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
local instance : DecidableEq PhysicalMomentum:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceMatterEulerPrepared preparedDual preparedPrimal noetherPreparedCurrent

/-- The original Euler minus follows the actual fixed-pi action variation once. -/
def actionEulerSource (q : PhysicalResponsePoint) (age : ℝ) (h : Field289) : Fin 289→ℂ:=
  fun i=> -sourceMatterEulerPrepared q (fieldUnit i) h age

theorem actionEulerSource_C2 (q : PhysicalResponsePoint) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) : ContDiffAt ℝ 2 (actionEulerSource q age) 0 :=
  contDiffAt_pi.mpr (fun _=>(sourceMatterEulerPrepared_C2 q _ age hz hw).neg)

theorem actionEulerSource_actualInitial (q : PhysicalResponsePoint) (age : ℝ) :
    actionEulerSource q age 0=actualSource q age 0 :=by
  funext i
  change -sourceMatterEulerPrepared q (fieldUnit i) 0 age=actualSource q age 0 i
  rw [sourceMatterEulerPrepared_source,densityRead_actual]
  rfl

def actionEulerJacobian (q : PhysicalResponsePoint) (age : ℝ) : Field289→L[ℝ] (Fin 289→ℂ):=
  fderiv ℝ (actionEulerSource q age) 0

theorem actionEulerJacobian_generated (q : PhysicalResponsePoint) (age : ℝ) (force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    actionEulerJacobian q age force=(fun i=> -noetherPreparedSlope q (fieldUnit i) force age) :=by
  have actual:=((actionEulerSource_C2 q age hz hw).differentiableAt (by norm_num)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have original : HasDerivAt (fun r : ℝ=>actionEulerSource q age (r • force))
      (fun i=> -noetherPreparedSlope q (fieldUnit i) force age) 0:=
    hasDerivAt_pi.mpr (fun i=>(sourceMatterEulerPrepared_response q (fieldUnit i) force age hz hw).neg)
  exact actual.unique original

theorem actionEulerJacobian_originalCorrection (q : PhysicalResponsePoint) (age : ℝ) (force : Field289)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    actionEulerJacobian q age force i=sourceJacobian q age force i+
      preparedDual q 0 age (rawReaderContact (fieldUnit i) force q.p q.F (preparedPrimal q 0 age))-
        preparedDual q 0 age (noetherReaderContact (fieldUnit i) force q.p q.F (preparedPrimal q 0 age)) :=by
  rw [actionEulerJacobian_generated q age force hz hw,sourceJacobian_actual q age force hz hw]
  change -noetherPreparedSlope q (fieldUnit i) force age=(sourceSlopeJet q force age i).value+
    preparedDual q 0 age (rawReaderContact (fieldUnit i) force q.p q.F (preparedPrimal q 0 age))-
      preparedDual q 0 age (noetherReaderContact (fieldUnit i) force q.p q.F (preparedPrimal q 0 age))
  have original : (sourceSlopeJet q force age i).value= -densitySlope q (fieldUnit i) force age:=by
    rw [densitySlope_actual]
    simp only [sourceSlopeJet,negativeJet,pairJet,slopeKernelJet_value,rawPreparedSlope,responseLeft,responseRight]
  rw [original,noetherPreparedSlope]
  abel

theorem actionEulerJacobian_arbitraryForce (q : PhysicalResponsePoint) (age : ℝ) (force : Field289) :
    actionEulerJacobian q age force=∑j : Fin 289,force j • actionEulerJacobian q age (fieldUnit j) :=by
  have coordinates : force=∑j : Fin 289,force j • fieldUnit j:=by
    funext i
    simp [fieldUnit,Finset.sum_apply,Pi.single_apply]
  have generated:=congrArg (actionEulerJacobian q age) coordinates
  simpa only [map_sum,map_smul] using generated

theorem actionEulerInsertion_uniform (q : PhysicalResponsePoint) (reader : Field289) :
    ∀ᶠh : Field289 in 𝓝 0,∀age : ℝ,
      sourceMatterEulerPrepared q reader h age=noetherPreparedCurrent q reader h age :=by
  filter_upwards [sourceMatterActionOperator_gradient_near reader q.p q.F] with h same
  intro age
  simp only [sourceMatterEulerPrepared,noetherPreparedCurrent,same]

/-- The four physical modes are assembled from the original action Euler insertions. -/
def actionRealCoefficients (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : MomentumCoefficients:=
  let F:=sourceMatterEulerPrepared q reader h age
  let R:=sourceMatterEulerPrepared (oppositeCoordinates q) reader h age
  let DR:=sourceMatterEulerPrepared (crossRightCoordinates q) reader h age
  let DL:=sourceMatterEulerPrepared (crossLeftCoordinates q) reader h age
  Finsupp.single (-q.k) ((1/2:ℂ)*(F+star R))+Finsupp.single q.k ((1/2:ℂ)*(R+star F))+
    Finsupp.single (2 • q.p+q.k) ((1/2:ℂ)*(DR+star DL))+
      Finsupp.single (-(2 • q.p+q.k)) ((1/2:ℂ)*(DL+star DR))

theorem actionRealCoefficients_near (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    (fun h=>actionRealCoefficients q reader h age)=ᶠ[𝓝 0]
      (fun h=>realDensityCoefficients q reader h age) :=by
  have forward:=(sourceMatterEulerPrepared_near q reader age).trans (sourceMovingIndependentPrepared_near q reader age)
  have reverse:=(sourceMatterEulerPrepared_near (oppositeCoordinates q) reader age).trans
    (sourceMovingIndependentPrepared_near (oppositeCoordinates q) reader age)
  have cr:=(sourceMatterEulerPrepared_near (crossRightCoordinates q) reader age).trans
    (sourceMovingIndependentPrepared_near (crossRightCoordinates q) reader age)
  have cl:=(sourceMatterEulerPrepared_near (crossLeftCoordinates q) reader age).trans
    (sourceMovingIndependentPrepared_near (crossLeftCoordinates q) reader age)
  filter_upwards [forward,reverse,cr,cl] with h hF hR hCR hCL
  simp only [actionRealCoefficients,realDensityCoefficients,hF,hR,hCR,hCL,
    oppositeCurrent_actual,crossRight_actual,crossLeft_actual]

theorem actionRealCoefficients_uniform (q : PhysicalResponsePoint) (reader : Field289) :
    ∀ᶠh : Field289 in 𝓝 0,∀age : ℝ,
      actionRealCoefficients q reader h age=realDensityCoefficients q reader h age :=by
  filter_upwards [actionEulerInsertion_uniform q reader,
    actionEulerInsertion_uniform (oppositeCoordinates q) reader,
    actionEulerInsertion_uniform (crossRightCoordinates q) reader,
    actionEulerInsertion_uniform (crossLeftCoordinates q) reader] with h hF hR hCR hCL
  intro age
  simp only [actionRealCoefficients,realDensityCoefficients,hF age,hR age,hCR age,hCL age,
    oppositeCurrent_actual,crossRight_actual,crossLeft_actual]

def actionRealEulerSource (q : PhysicalResponsePoint) (age : ℝ) (wave : PhysicalMomentum)
    (h : Field289) : Fin 289→ℂ:=fun i=> -actionRealCoefficients q (fieldUnit i) h age (-wave)

theorem actionRealEulerSource_near (q : PhysicalResponsePoint) (age : ℝ) (wave : PhysicalMomentum) :
    actionRealEulerSource q age wave=ᶠ[𝓝 0] (fun h=>realEulerCoefficients q h age (-wave)) :=by
  have nearby:=Filter.eventually_all.mpr (fun i=>actionRealCoefficients_near q (fieldUnit i) age)
  filter_upwards [nearby] with h hh
  funext i
  exact congrArg (fun C : MomentumCoefficients=> -C (-wave)) (hh i)

theorem actionRealEulerSource_generated (q : PhysicalResponsePoint) (age : ℝ) (wave : PhysicalMomentum)
    (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>actionRealEulerSource q age wave (r • force))
      (realEulerSlope q force age (-wave)) 0 :=by
  apply (realEulerCoefficients_generated q force age hz hw (-wave)).congr_of_eventuallyEq
  exact (actionRealEulerSource_near q age wave).comp_tendsto
    (by simpa using ((show Continuous (fun r : ℝ=>r • force) from
      continuous_id.smul continuous_const).tendsto (0:ℝ)))

theorem actionRealEulerSource_timePort (q : PhysicalResponsePoint) (age : ℝ) (wave : PhysicalMomentum)
    (force : Field289) (i : Fin 289) :
    actionRealEulerSource q age wave 0 i=(realEulerTimeJet q force false age (-wave) i).value :=by
  rw [realEulerTimeJet_value]
  exact congrFun (actionRealEulerSource_near q age wave).self_of_nhds i

theorem actionRealEulerSource_responseTimePort (q : PhysicalResponsePoint) (age : ℝ) (wave : PhysicalMomentum)
    (force : Field289) (hz : q.z.im≠0) (hw : q.w.im≠0) (i : Fin 289) :
    deriv (fun r : ℝ=>actionRealEulerSource q age wave (r • force) i) 0=
      (realEulerTimeJet q force true age (-wave) i).value :=by
  have actual:=(hasDerivAt_pi.mp (actionRealEulerSource_generated q age wave force hz hw)) i
  rw [actual.deriv,realEulerTimeJet_value]
  rfl

end LowEnergy.PreparationVacuumMatterEulerFeedback
