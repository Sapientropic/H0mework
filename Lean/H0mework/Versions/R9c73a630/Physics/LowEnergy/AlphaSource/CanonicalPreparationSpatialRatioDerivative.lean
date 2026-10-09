import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationHalfDensityFixedFiber

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

attribute [local irreducible] coreHalfDensity fieldVector

def shiftedDirection (f : Field289) (r : ℝ) (z v : SourceCoordinateSlice) : SourceCoordinateSlice:=
  v+r • fderiv ℝ (fieldVector f) z v

def spatialRatio (f : Field289) (N : ℕ) (r : ℝ) (z v : SourceCoordinateSlice) : ℂ:=
  fderiv ℝ (fun u : Parameter=>halfRatio f N u.2 u.1) (r,z) (0,v) / halfRatio f N z r

theorem halfRatio_ne_zero (f : Field289) (N : ℕ) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) : halfRatio f N z.val r≠0 :=
  div_ne_zero (coreHalfDensity_ne_zero N z) (coreHalfDensity_ne_zero N ⟨_,moved⟩)

theorem curve_spatial_derivative (f : Field289) (r : ℝ) (z : physicalChart) (v : SourceCoordinateSlice) :
    HasDerivAt (fun t : ℝ=>fieldCoordinateCurve f r (z.val+t • v)) (shiftedDirection f r z.val v) 0 :=by
  have line : HasDerivAt (fun t : ℝ=>z.val+t • v) v 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val using 1
    simp
  have hf : HasFDerivAt (fieldVector f) (fderiv ℝ (fieldVector f) z.val) (z.val+(0:ℝ) • v) :=by
    simpa only [zero_smul,add_zero] using (fieldVector_smooth f z).differentiableAt (by simp) |>.hasFDerivAt
  exact line.add ((hf.comp_hasDerivAt 0 line).const_smul r)

theorem halfRatio_spatial_derivative (f : Field289) (N : ℕ) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    fderiv ℝ (fun u : Parameter=>halfRatio f N u.2 u.1) (r,z.val) (0,v)=
      (fderiv ℝ (coreHalfDensity N) z.val v*coreHalfDensity N (fieldCoordinateCurve f r z.val)-
        coreHalfDensity N z.val*fderiv ℝ (coreHalfDensity N) (fieldCoordinateCurve f r z.val) (shiftedDirection f r z.val v))/
          (coreHalfDensity N (fieldCoordinateCurve f r z.val))^2 :=by
  have line : HasDerivAt (fun t : ℝ=>z.val+t • v) v 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val using 1
    simp
  have hbase : HasFDerivAt (coreHalfDensity N) (fderiv ℝ (coreHalfDensity N) z.val) (z.val+(0:ℝ) • v) :=by
    simpa only [zero_smul,add_zero] using (coreHalfDensity_smooth N z).differentiableAt (by simp) |>.hasFDerivAt
  have hmove : HasFDerivAt (coreHalfDensity N) (fderiv ℝ (coreHalfDensity N) (fieldCoordinateCurve f r z.val))
      (fieldCoordinateCurve f r (z.val+(0:ℝ) • v)) :=by
    simpa only [zero_smul,add_zero] using (coreHalfDensity_smooth N ⟨_,moved⟩).differentiableAt (by simp) |>.hasFDerivAt
  have numerator:=hbase.comp_hasDerivAt 0 line
  have denominator:=hmove.comp_hasDerivAt 0 (curve_spatial_derivative f r z v)
  have nz : coreHalfDensity N (fieldCoordinateCurve f r (z.val+(0:ℝ) • v))≠0:=by
    simpa only [zero_smul,add_zero] using coreHalfDensity_ne_zero N ⟨_,moved⟩
  have quotient:=numerator.div denominator nz
  have pairLine : HasDerivAt (fun t : ℝ=>(r,z.val+t • v)) (0,v) 0 :=(hasDerivAt_const 0 r).prodMk line
  have hs : HasFDerivAt (fun u : Parameter=>halfRatio f N u.2 u.1)
      (fderiv ℝ (fun u : Parameter=>halfRatio f N u.2 u.1) (r,z.val)) (r,z.val+(0:ℝ) • v) :=by
    simpa only [zero_smul,add_zero] using (halfRatio_param_smooth f N (r,z.val) z.property moved).differentiableAt (by simp) |>.hasFDerivAt
  have generated:=hs.comp_hasDerivAt 0 pairLine
  have same:=generated.unique quotient
  simpa only [Function.comp_apply,zero_smul,add_zero] using same

theorem spatialRatio_source (f : Field289) (N : ℕ) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    spatialRatio f N r z.val v=
      fderiv ℝ (coreHalfDensity N) z.val v/coreHalfDensity N z.val-
        fderiv ℝ (coreHalfDensity N) (fieldCoordinateCurve f r z.val) (shiftedDirection f r z.val v)/
          coreHalfDensity N (fieldCoordinateCurve f r z.val) :=by
  rw [spatialRatio,halfRatio_spatial_derivative f N r z moved v,halfRatio]
  have h0:=coreHalfDensity_ne_zero N z
  have h1:=coreHalfDensity_ne_zero N ⟨_,moved⟩
  field_simp [h0,h1]

def spatialCorrection (f : Field289) (u : Parameter) (v : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber:=
  weight (fun N=>spatialRatio f N u.1 u.2 v)

theorem ratio_smooth (f : Field289) (N : ℕ) (u : Parameter) (base : u.2∈physicalChart)
    (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) (V : Parameter→SourceCoordinateSlice)
    (hV : ContDiffAt ℝ ∞ V u) :
    ContDiffAt ℝ ∞ (fun w : Parameter=>spatialRatio f N w.1 w.2 (V w)) u :=by
  have hs:=halfRatio_param_smooth f N u base moved
  have hd:=(hs.fderiv_right (m:=∞) (by simp)).clm_apply ((contDiffAt_const (c:=(0:ℝ))).prodMk hV)
  convert! hd.mul (hs.inv (halfRatio_ne_zero f N u.1 ⟨u.2,base⟩ moved)) using 1

theorem transportedSection_spatial (f : Field289) (a : QuantumTest) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) (v : SourceCoordinateSlice) :
    spatialJet (transportedSection f a) (r,z.val) v=
      transportFiber f z.val r (fderiv ℝ a z.val v+spatialCorrection f (r,z.val) v (a z.val)) :=by
  apply PiLp.ext;intro word
  let P : FockFiber→L[ℝ] ℂ:=(PiLp.proj (𝕜:=ℂ) 2 (fun _ : Occupation=>ℂ) word).restrictScalars ℝ
  have hU:=(transportedSection_smooth f a (r,z.val) z.property moved).differentiableAt (by simp) |>.hasFDerivAt
  have read:=P.hasFDerivAt.comp (r,z.val) hU
  have hr:=(halfRatio_param_smooth f word.card (r,z.val) z.property moved).differentiableAt (by simp) |>.hasFDerivAt
  have ha:=P.hasFDerivAt.comp z.val (a.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hsnd : HasFDerivAt (Prod.snd : Parameter→SourceCoordinateSlice) (ContinuousLinearMap.snd ℝ ℝ SourceCoordinateSlice) (r,z.val):=hasFDerivAt_snd
  have has:=ha.comp (r,z.val) hsnd
  have product:=hr.mul has
  have eq:=congrArg (fun D : Parameter→L[ℝ] ℂ=>D (0,v)) (read.unique product)
  change (spatialJet (transportedSection f a) (r,z.val) v) word=
    halfRatio f word.card z.val r*(fderiv ℝ a z.val v) word+
      a z.val word*fderiv ℝ (fun u : Parameter=>halfRatio f word.card u.2 u.1) (r,z.val) (0,v) at eq
  change (spatialJet (transportedSection f a) (r,z.val) v) word=
    halfRatio f word.card z.val r*((fderiv ℝ a z.val v) word+spatialRatio f word.card r z.val v*a z.val word)
  rw [eq,spatialRatio]
  have nz:=halfRatio_ne_zero f word.card r z moved
  field_simp

theorem spatialRatio_zero (f : Field289) (N : ℕ) (z : physicalChart) (v : SourceCoordinateSlice) :
    spatialRatio f N 0 z.val v=0 :=by
  rw [spatialRatio_source f N 0 z (by rw [curve_zero];exact z.property) v]
  simp only [curve_zero,shiftedDirection,zero_smul,add_zero,sub_self]

end LowEnergy.PreparationVacuumSpatialDensityTransport
