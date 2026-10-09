import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSpatialRatioDerivative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSpatialDensityTransport
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

open CanonicalPreparationCore PreparationVacuumHalfDensityFiber

open GaussNativeMatter GaussCoframeForm

def correctedDerivative (f : Field289) (a : QuantumTest) (u : Parameter) (v : SourceCoordinateSlice) : FockFiber:=
  fderiv ℝ a u.2 v+spatialCorrection f u v (a u.2)

def correctedMomentum (f : Field289) (a : QuantumTest) (v : Ambient) (u : Parameter) : FockFiber:=
  (-Complex.I) • (correctedDerivative f a u (direction v (fieldCoordinateCurve f u.1 u.2))+
    connection v (fieldCoordinateCurve f u.1 u.2) (a u.2))

def correctedCoframe (f : Field289) (a : QuantumTest) (i : Fin 6) (u : Parameter) : FockFiber:=
  (-Complex.I) • correctedDerivative f a u (GaussCoframeCore.coframeDirection i)

def correctedSpin (a : QuantumTest) (k : Fin 7) (u : Parameter) : FockFiber:=
  quantized (GaussCoframeSpin.full k) (a u.2)

def correctedNumber (a : QuantumTest) (u : Parameter) : FockFiber:=fiberNumber (a u.2)

theorem movingMomentum_source (f : Field289) (a : QuantumTest) (v : Ambient) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    movingMomentum f (transportedSection f a) v (r,z.val)=transportFiber f z.val r (correctedMomentum f a v (r,z.val)) :=by
  have commutes:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (a z.val))
    (native_weight_commute (fun N=>halfRatio f N z.val r) (inverseL (fieldCoordinateCurve f r z.val) v).1).eq
  change transportFiber f z.val r (connection v (fieldCoordinateCurve f r z.val) (a z.val))=
    connection v (fieldCoordinateCurve f r z.val) (transportFiber f z.val r (a z.val)) at commutes
  unfold movingMomentum
  rw [transportedSection_spatial f a r z moved]
  change (-Complex.I) • (transportFiber f z.val r (correctedDerivative f a (r,z.val) _)+
    connection v (fieldCoordinateCurve f r z.val) (transportFiber f z.val r (a z.val)))=_
  rw [←commutes,←map_add,←map_smul]
  rfl

theorem movingCoframe_source (f : Field289) (a : QuantumTest) (i : Fin 6) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    movingCoframe (transportedSection f a) i (r,z.val)=transportFiber f z.val r (correctedCoframe f a i (r,z.val)) :=by
  unfold movingCoframe
  rw [transportedSection_spatial f a r z moved,←map_smul]
  rfl

theorem movingSpin_source (f : Field289) (a : QuantumTest) (k : Fin 7) (r : ℝ) (z : SourceCoordinateSlice) :
    movingSpin (transportedSection f a) k (r,z)=transportFiber f z r (correctedSpin a k (r,z)) :=by
  have h:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (a z)) (weight_commute (fun N=>halfRatio f N z r) (GaussCoframeSpin.full k)).eq
  exact h.symm

theorem movingNumber_source (f : Field289) (a : QuantumTest) (r : ℝ) (z : SourceCoordinateSlice) :
    movingNumber (transportedSection f a) (r,z)=transportFiber f z r (correctedNumber a (r,z)) :=by
  apply PiLp.ext;intro word
  simp only [movingNumber,transportedSection,transportFiber,correctedNumber,fiberNumber_apply,weight_apply]
  ring

theorem correction_apply_smooth (f : Field289) (U : Parameter→FockFiber) (V : Parameter→SourceCoordinateSlice)
    (u : Parameter) (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hU : ContDiffAt ℝ ∞ U u) (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w=>spatialCorrection f w (V w) (U w)) u :=by
  apply (contDiffAt_piLp 2).mpr;intro word
  let P : FockFiber→L[ℝ] ℂ:=(PiLp.proj (𝕜:=ℂ) 2 (fun _ : Occupation=>ℂ) word).restrictScalars ℝ
  exact (ratio_smooth f word.card u base moved V hV).mul (P.contDiff.contDiffAt.comp u hU)

theorem correctedDerivative_smooth (f : Field289) (a : QuantumTest) (V : Parameter→SourceCoordinateSlice)
    (u : Parameter) (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart)
    (hV : ContDiffAt ℝ ∞ V u) : ContDiffAt ℝ ∞ (fun w=>correctedDerivative f a w (V w)) u :=by
  have ha:=a.contDiff.contDiffAt.comp u contDiffAt_snd
  have d:=(a.contDiff.fderiv_right (m:=∞) (by simp)).contDiffAt.comp u contDiffAt_snd
  exact (d.clm_apply hV).add (correction_apply_smooth f _ V u base moved ha hV)

theorem correctedMomentum_smooth (f : Field289) (a : QuantumTest) (v : Ambient) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (correctedMomentum f a v) u :=by
  have curve:=field_curve_smooth f u.1 ⟨u.2,base⟩
  have hd:=(direction_smooth v ⟨_,moved⟩).comp u curve
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have hc:=R.contDiff.contDiffAt.comp u ((connection_smooth v ⟨_,moved⟩).comp u curve)
  exact ((correctedDerivative_smooth f a _ u base moved hd).add
    (hc.clm_apply (a.contDiff.contDiffAt.comp u contDiffAt_snd))).const_smul (-Complex.I)

theorem correctedCoframe_smooth (f : Field289) (a : QuantumTest) (i : Fin 6) (u : Parameter)
    (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (correctedCoframe f a i) u :=
  (correctedDerivative_smooth f a _ u base moved contDiffAt_const).const_smul (-Complex.I)

theorem correctedSpin_smooth (a : QuantumTest) (k : Fin 7) (u : Parameter) :
    ContDiffAt ℝ ∞ (correctedSpin a k) u :=
  ((quantized (GaussCoframeSpin.full k)).restrictScalars ℝ).contDiff.contDiffAt.comp u (a.contDiff.contDiffAt.comp u contDiffAt_snd)

theorem correctedNumber_smooth (a : QuantumTest) (u : Parameter) : ContDiffAt ℝ ∞ (correctedNumber a) u :=
  (fiberNumber.restrictScalars ℝ).contDiff.contDiffAt.comp u (a.contDiff.contDiffAt.comp u contDiffAt_snd)

theorem correctedDerivative_zero (f : Field289) (a : QuantumTest) (r : ℝ) (z v : SourceCoordinateSlice)
    (outside : z∉tsupport a) : correctedDerivative f a (r,z) v=0 :=by
  simp only [correctedDerivative,fderiv_of_notMem_tsupport ℝ outside,zero_apply,
    image_eq_zero_of_notMem_tsupport outside,map_zero,add_zero]

theorem correctedMomentum_zero (f : Field289) (a : QuantumTest) (v : Ambient) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : correctedMomentum f a v (r,z)=0 :=by
  simp only [correctedMomentum,correctedDerivative_zero f a r z _ outside,
    image_eq_zero_of_notMem_tsupport outside,map_zero,add_zero,smul_zero]

theorem correctedCoframe_zero (f : Field289) (a : QuantumTest) (i : Fin 6) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : correctedCoframe f a i (r,z)=0 :=by
  simp only [correctedCoframe,correctedDerivative_zero f a r z _ outside,smul_zero]

theorem correctedMomentum_initial (f : Field289) (a : QuantumTest) (v : Ambient) (z : physicalChart) :
    correctedMomentum f a v (0,z.val)=covariantMomentum v a z.val :=by
  have zero : spatialCorrection f (0,z.val) (direction v z.val) (a z.val)=0 :=by
    apply PiLp.ext;intro word
    simp only [spatialCorrection,weight_apply,spatialRatio_zero,zero_mul,PiLp.zero_apply]
  simp only [correctedMomentum,correctedDerivative,curve_zero,zero,add_zero]
  rfl

end LowEnergy.PreparationVacuumSpatialDensityTransport
