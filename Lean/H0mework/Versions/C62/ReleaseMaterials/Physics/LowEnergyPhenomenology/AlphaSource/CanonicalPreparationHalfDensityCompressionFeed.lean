import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationHalfDensitySourceJets
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaObservedLimit

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumHalfDensityFiber
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceActionJets SourceQuantumScalarChart GaussLiveMomentum
open PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearFieldCurve
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open CanonicalGradedLocalCurrent Filter Set
open GaussUnitaryHistory (Index)
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators Distributions InnerProductSpace Interval
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationVacuumGradedTransport GaussDensityCore GaussYukawaCoefficient GaussNativePotential
open MeasureTheory

open PreparationVacuumFieldCovector PreparationVacuumActionFieldLift

open PreparationVacuumYukawaTransport CanonicalPhysicalYResolvent
open CanonicalPreparationCore.Completed PreparationVacuumSourcePreparedResponse
open NativeHistoryGrade (Label)
abbrev Index:=GaussUnitaryHistory.Index
local instance : Fintype Label:=Fintype.ofFinite _

def diagonalFiber (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberMap:=
  actualFiber p z-retainedCoefficient z-yukawaFiber z

theorem diagonalFiber_source (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    diagonalFiber p z=actualFiber p z-actualFiber 0 z+matterFiber z :=by
  unfold diagonalFiber retainedCoefficient yukawaFiber matterFiber
  abel

theorem diagonalFiber_smooth (p : PhysicalMomentum) (z : physicalChart) : ContDiffAt ℝ ∞ (diagonalFiber p) z.val :=
  ((actualFiber_smooth p z).sub (retainedCoefficient_smooth z)).sub (yukawaFiber_smooth z)

theorem matterFiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ matterFiber z.val :=
  ContDiffAt.sum (fun i _=>ContDiffAt.sum (fun j _=>GaussMatterCore.local_smooth i j z))

theorem diagonalFiber_derivative (p : PhysicalMomentum) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (diagonalFiber p) z.val h=
      fderiv ℝ (actualFiber p) z.val h-fderiv ℝ (actualFiber 0) z.val h+fderiv ℝ matterFiber z.val h :=by
  have hp:=(actualFiber_smooth p z).differentiableAt (by simp) |>.hasFDerivAt
  have h0:=(actualFiber_smooth 0 z).differentiableAt (by simp) |>.hasFDerivAt
  have hm:=(matterFiber_smooth z).differentiableAt (by simp) |>.hasFDerivAt
  have hs:=((hp.sub h0).add hm).congr_of_eventuallyEq (Filter.Eventually.of_forall (diagonalFiber_source p))
  exact congrArg (fun D : SourceCoordinateSlice→L[ℝ] FiberMap=>D h) hs.fderiv

theorem diagonalFiber_mother (f : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    fderiv ℝ (diagonalFiber p) z.val (fieldVector f z.val)=
      -fiberFamily f p z.val+fiberFamily f 0 z.val+
      quantizer (symbolFirst 0 (sourceState z.val) (complement f z.val))-
      quantizer (symbolFirst p (sourceState z.val) (complement f z.val))+
      fderiv ℝ matterFiber z.val (fieldVector f z.val) :=by
  rw [diagonalFiber_derivative]
  have hp:=eq_sub_of_add_eq (PreparationVacuumFieldCovector.mother_current_slice f p z)
  have h0:=eq_sub_of_add_eq (PreparationVacuumFieldCovector.mother_current_slice f 0 z)
  rw [hp,h0]
  abel

def fixedDiagonalForm (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (r : ℝ) : ℂ:=
  nativeIntegral f a b r+coframeIntegral f a b r+fixedFiber (diagonalFiber p) f a b r

def fixedDiagonalJets (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : TwoJets (fixedDiagonalForm f p a b):=
  ((nativeIntegralJets f a b).add (coframeIntegralJets f a b)).add (fixedJets (diagonalFiber p) (diagonalFiber_smooth p) f a b)

theorem transportedForm_fixed (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    transportedForm f p a b=ᶠ[𝓝 0] fixedDiagonalForm f p a b :=by
  have small : ∀ᶠr : ℝ in 𝓝 0,|r|<fieldRadius f a:=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  filter_upwards [actualFiber_fixed f p a b,retained_fixed f a b,
    fiberIntegral_fixed_germ yukawaFiber yukawaFiber_number f a b,small] with r ha hb hc hr
  change nativeIntegral f a b r+coframeIntegral f a b r+fiberIntegral f a b (actualFiber p) r-
    fiberIntegral f a b retainedCoefficient r-fiberIntegral f a b yukawaFiber r=_
  rw [ha,hb,hc]
  unfold fixedDiagonalForm diagonalFiber
  rw [fixedFiber_sub (fun z=>actualFiber p z-retainedCoefficient z) yukawaFiber
    (fun z=>(actualFiber_smooth p z).sub (retainedCoefficient_smooth z)) yukawaFiber_smooth f a b r hr,
    fixedFiber_sub (actualFiber p) retainedCoefficient (actualFiber_smooth p) retainedCoefficient_smooth f a b r hr]
  abel

theorem transported_first_fixed (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (transportedJets f p a b).first 0=(fixedDiagonalJets f p a b).first 0 :=
  (transportedJets f p a b).actual.1.unique
    ((fixedDiagonalJets f p a b).actual.1.congr_of_eventuallyEq (transportedForm_fixed f p a b))

theorem transported_second_fixed (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (transportedJets f p a b).second=(fixedDiagonalJets f p a b).second :=
  (transportedJets f p a b).actual.2.unique
    ((fixedDiagonalJets f p a b).actual.2.congr_of_eventuallyEq (transportedForm_fixed f p a b).deriv)

theorem compression_fixed_source (f : Field289) (p : PhysicalMomentum) (F : Index) :
    transportedCompression f p F=ᶠ[𝓝 0] fun r=>sourceAssembly p F
      (fun i j=>fixedDiagonalForm f p (bareTest p F i) (bareTest p F j) r) :=by
  have all:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr
    (fun j=>transportedForm_fixed f p (bareTest p F i) (bareTest p F j)))
  filter_upwards [all] with r hr
  exact congrArg (sourceAssembly p F) (funext (fun i=>funext (fun j=>hr i j)))

def fixedCurrentEntry (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  (nativeIntegralJets f a b).first 0+(coframeIntegralJets f a b).first 0+
    ∫z,fixedCurrent (diagonalFiber p) f a b z ∂GaussHistoryHilbert.configurationMeasure

theorem fixedCurrentEntry_source (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (fixedDiagonalJets f p a b).first 0=fixedCurrentEntry f p a b :=by
  change (nativeIntegralJets f a b).first 0+(coframeIntegralJets f a b).first 0+
    (fixedJets (diagonalFiber p) (diagonalFiber_smooth p) f a b).first 0=_
  rw [fixedJets_first];rfl

theorem compression_current_source (f : Field289) (p : PhysicalMomentum) (F : Index) :
    transportedCurrent f p F 0=sourceAssembly p F
      (fun i j=>fixedCurrentEntry f p (bareTest p F i) (bareTest p F j)) :=by
  apply congrArg (sourceAssembly p F)
  funext i j
  exact (transported_first_fixed f p _ _).trans (fixedCurrentEntry_source f p _ _)

theorem compression_contact_source (f : Field289) (p : PhysicalMomentum) (F : Index) :
    transportedContact f p F=sourceAssembly p F
      (fun i j=>(fixedDiagonalJets f p (bareTest p F i) (bareTest p F j)).second) :=by
  apply congrArg (sourceAssembly p F)
  funext i j;exact transported_second_fixed f p _ _

def fixedFullCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>fixedCurrentEntry f p (bareTest p F i) (bareTest p F j))+
    jetOperator f n 1 (finiteRetainer p F) 0

theorem fullCurrent_source (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) :
    PreparationVacuumYukawaTransport.fullCurrent f p F n 0=fixedFullCurrent f p F n :=by
  rw [PreparationVacuumYukawaTransport.fullCurrent,compression_current_source];rfl

theorem trueVertex_source (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) :
    trueVertex f p k F n z w=finiteFull (p+k) F n z*fixedFullCurrent f p F n*finiteFull p F n w :=by
  rw [trueVertex,fullCurrent_source]

theorem prepared_full_source (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (truePreparedResponse epsilon precision f p F n z left right a s b t)
      (-inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        ((finiteFull p F n z*fixedFullCurrent f p F n*finiteFull p F n z)
          (completedLeg right b t (sourceProfile epsilon precision)))) 0 :=by
  rw [←fullCurrent_source]
  exact truePreparedResponse_first epsilon precision f p F n z hz left right a s b t

def fixedFullContact (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>(fixedDiagonalJets f p (bareTest p F i) (bareTest p F j)).second)+
    jetOperator f n 2 (finiteRetainer p F) 0

theorem fullContact_source (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) :
    fullContact f p F n=fixedFullContact f p F n :=by
  rw [fullContact,compression_contact_source];rfl

def fixedResolventContact (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) : H→L[ℂ] H:=
  -(finiteFull p F n z*fixedFullContact f p F n*finiteFull p F n z-
    finiteFull p F n z*fixedFullCurrent f p F n*finiteFull p F n z*fixedFullCurrent f p F n*finiteFull p F n z-
    finiteFull p F n z*fixedFullCurrent f p F n*finiteFull p F n z*fixedFullCurrent f p F n*finiteFull p F n z)

theorem fullResolventContact_source (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) :
    fullResolventContact f p F n z=fixedResolventContact f p F n z :=by
  simp only [fullResolventContact,fullContact_source,fullCurrent_source,fixedResolventContact]

attribute [local irreducible] fixedFullCurrent fixedFullContact fixedResolventContact sourceProfile finiteFull truePreparedResponse

theorem prepared_full_contact (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (deriv (truePreparedResponse epsilon precision f p F n z left right a s b t))
      (inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        (fixedResolventContact f p F n z (completedLeg right b t (sourceProfile epsilon precision)))) 0 :=by
  rw [←fullResolventContact_source]
  have source:=(truePreparedJets epsilon precision f p F n z hz left right a s b t).actual.2
  exact source

def fixedPreparedSlope (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) : ℂ:=
  -inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    ((finiteFull p F n z*fixedFullCurrent f p F n*finiteFull p F n z)
      (completedLeg right b t (sourceProfile epsilon precision)))

theorem curvature_full_source (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t)
      (fixedPreparedSlope epsilon precision (readerReal sourceMomentum row) p F n z left right a s b t+
        Complex.I*fixedPreparedSlope epsilon precision (readerImag sourceMomentum row) p F n z left right a s b t) 0 :=by
  unfold trueCurvatureResponse fixedPreparedSlope
  have realPart:=prepared_full_source epsilon precision (readerReal sourceMomentum row) p F n z hz left right a s b t
  have imagPart:=prepared_full_source epsilon precision (readerImag sourceMomentum row) p F n z hz left right a s b t
  have result:=realPart.add ((imagPart.sub_const
    (truePreparedResponse epsilon precision (readerImag sourceMomentum row) p F n z left right a s b t 0)).const_mul Complex.I)
  exact result

theorem trueVertex_source_price (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ)
    (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    ‖finiteFull (p+k) F n z*fixedFullCurrent f p F n*finiteFull p F n w‖≤
      normBound n z*fullCurrentPrice f p F n*normBound n w :=by
  rw [←trueVertex_source]
  exact trueVertex_price f p k F n z w hz hw

open PreparationVacuumUncutYukawa

def fixedSourceCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>fixedCurrentEntry f p (bareTest p F i) (bareTest p F j))+
    sourceYJet f p F o 1 0

def fixedSourceContact (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) : H→L[ℂ] H:=
  sourceAssembly p F (fun i j=>(fixedDiagonalJets f p (bareTest p F i) (bareTest p F j)).second)+
    sourceYJet f p F o 2 0

theorem sourceCurrent_fixed (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) :
    PreparationVacuumUncutYukawa.sourceCurrent f p F o 0=fixedSourceCurrent f p F o :=by
  rw [PreparationVacuumUncutYukawa.sourceCurrent,compression_current_source];rfl

theorem sourceContact_fixed (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) :
    PreparationVacuumUncutYukawa.sourceContact f p F o=fixedSourceContact f p F o :=by
  rw [PreparationVacuumUncutYukawa.sourceContact,compression_contact_source];rfl

theorem observed_fixed_source (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (observedResponse epsilon precision f p F o z left right a s b t)
      (-inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        ((sourceResolvent f p F o z 0*fixedSourceCurrent f p F o*sourceResolvent f p F o z 0)
          (completedLeg right b t (sourceProfile epsilon precision)))) 0 :=by
  have h:=(observedJets epsilon precision f p F o z hz left right a s b t).actual.1
  simpa only [observedJets,sourceInsertion,sourceCurrent_fixed,neg_apply,inner_neg_right] using h

def fixedSourceResolventContact (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) : H→L[ℂ] H:=
  -(sourceResolvent f p F o z 0*fixedSourceContact f p F o*sourceResolvent f p F o z 0-
    sourceResolvent f p F o z 0*fixedSourceCurrent f p F o*sourceResolvent f p F o z 0*fixedSourceCurrent f p F o*sourceResolvent f p F o z 0-
    sourceResolvent f p F o z 0*fixedSourceCurrent f p F o*sourceResolvent f p F o z 0*fixedSourceCurrent f p F o*sourceResolvent f p F o z 0)

theorem sourceInverseContact_fixed (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) :
    sourceInverseContact f p F o z=fixedSourceResolventContact f p F o z :=by
  simp only [sourceInverseContact,sourceContact_fixed,sourceCurrent_fixed,fixedSourceResolventContact]

theorem observed_fixed_contact (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (deriv (observedResponse epsilon precision f p F o z left right a s b t))
      (inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        (fixedSourceResolventContact f p F o z (completedLeg right b t (sourceProfile epsilon precision)))) 0 :=by
  rw [←sourceInverseContact_fixed]
  have source:=(observedJets epsilon precision f p F o z hz left right a s b t).actual.2
  exact source

end LowEnergy.PreparationVacuumHalfDensityFiber
