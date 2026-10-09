import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeColorSource

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open FullQuantum.StateGreen PreparationVacuumFixedMomentumActionReturn PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization SourceQuantumFockGauge PreparationVacuumNonlinearFieldCurve
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActionFieldLift PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction
open PreparationVacuumLowerClassical PreparationVacuumTemporalCharge PreparationVacuumGaugeSourceInjection
open PreparationVacuumNoetherChart PreparationVacuumSourceActionJets PreparationVacuumFullFieldRiesz
open SourcePropagationNativeActionHessian GaussNativeMatter GaussCoreHilbert
open ActualDressedNativeConstraint ActualDressedNullNative ActualDressedLockedWard ActualDressedConstraintRead
open ActualDressedTemporalCurrent PreparationVacuumWeightedChargeActionWard
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.L2Operator
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] nativeSourceColumn noetherReader nativeReader nativeReaderContact

open GaussHistoryHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumNonlinearFieldCurve PreparationVacuumHalfDensityFiber
open MeasureTheory Set
open scoped InnerProductSpace
private abbrev NativeOp:=H→L[ℂ]H
local instance : NormedAlgebra ℝ NativeOp:=NormedAlgebra.restrictScalars ℝ ℂ _

private theorem color_sample (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (l r : QuantumTest) (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius l) :
    nativeSample (Fin.castAdd 6 g) 0 gradient p l r (h,z)=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        noetherSample (gaugeField b.2 b.1) p l r (h,z) :=by
  by_cases inside : z∈tsupport l
  · have valid:=ambientRadius_valid l h z small.le inside
    change (pairRight z (l z))
        (quantizer (nativeNoether (Fin.castAdd 6 g) 0 gradient p (sourceState z) (ambientState (h,z))) (r z))=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • (pairRight z (l z))
        (quantizer (transportedRawSymbol (gaugeField b.2 b.1) (sourceState z) (ambientState (h,z)) p) (r z))
    rw [native_color_gradient_transport g gradient p (sourceState z) (ambientState (h,z)) valid,map_sum]
    simp only [sum_apply,smul_apply,map_sum,map_smul]
  · rw [nativeSample_zero (Fin.castAdd 6 g) 0 gradient p l r h z inside]
    simp only [noetherSample_zero _ p l r h z inside,smul_zero,Finset.sum_const_zero]

private theorem color_form (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (l r : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius l) :
    nativeForm (Fin.castAdd 6 g) 0 gradient p l r h=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        noetherForm (gaugeField b.2 b.1) p l r h :=by
  have integrable (b : Fin 12×Fin 4) : Integrable
      (fun z=>noetherSample (gaugeField b.2 b.1) p l r (h,z)) GaussHistoryHilbert.configurationMeasure :=
    parameter_slice_integrable _ (tsupport l) l.hasCompactSupport h
      (fun z=>noetherSample_near_smooth (gaugeField b.2 b.1) p l r h z small)
      (noetherSample_zero (gaugeField b.2 b.1) p l r)
  unfold PreparationVacuumNativeLocalWard.nativeForm noetherForm
  calc
    _=∫z,∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        noetherSample (gaugeField b.2 b.1) p l r (h,z) ∂GaussHistoryHilbert.configurationMeasure :=
      integral_congr_ae (Eventually.of_forall (fun z=>color_sample g gradient p l r h z small))
    _=_ :=by
      simpa only [Pi.smul_apply,integral_smul] using
        integral_finsetSum Finset.univ (fun b _=>(integrable b).smul ((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ))

private def rieszLinear (F : GaussUnitaryHistory.Index) :
    (FrameIndex F→FrameIndex F→ℂ)→ₗ[ℂ] NativeOp where
  toFun:=finiteRiesz F
  map_add' a b:=by simp only [finiteRiesz,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c a:=by
    simp only [finiteRiesz,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]

/-- The real source preparation and its own common compact chart neighbourhood pay the full four-current reader germ. -/
theorem native_color_gradient_reader_germ (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : nativeReader (Fin.castAdd 6 g) 0 gradient p F=ᶠ[𝓝 0]
      fun h=>∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • noetherReader (gaugeField b.2 b.1) p F h :=by
  have entries : ∀ᶠh : Field289 in 𝓝 0,∀i j : FrameIndex F,
      nativeForm (Fin.castAdd 6 g) 0 gradient p (frameTest F i) (frameTest F j) h=
        ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
          noetherForm (gaugeField b.2 b.1) p (frameTest F i) (frameTest F j) h :=by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have near : ∀ᶠh : Field289 in 𝓝 0,‖h‖<ambientRadius (frameTest F i):=
      (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using ambientRadius_positive (frameTest F i)))
    exact near.mono (fun h small=>color_form g gradient p (frameTest F i) (frameTest F j) h small)
  filter_upwards [entries] with h paid
  have same : (fun i j=>nativeForm (Fin.castAdd 6 g) 0 gradient p (frameTest F i) (frameTest F j) h)=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) •
        (fun i j=>noetherForm (gaugeField b.2 b.1) p (frameTest F i) (frameTest F j) h) :=by
    funext i j
    simpa only [Finset.sum_apply,Pi.smul_apply] using paid i j
  have source:=congrArg (rieszLinear F) same
  simpa only [map_sum,map_smul,rieszLinear,LinearMap.coe_mk,AddHom.coe_mk,nativeReader,noetherReader] using source

theorem native_color_gradient_reader (g : Fin 3) (gradient : Fin 4→ℝ) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : nativeReader (Fin.castAdd 6 g) 0 gradient p F 0=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • noetherReader (gaugeField b.2 b.1) p F 0 :=
  (native_color_gradient_reader_germ g gradient p F).self_of_nhds

/-- The same source germ is differentiated, retaining the actual Noether contact. -/
theorem native_color_gradient_contact (g : Fin 3) (gradient : Fin 4→ℝ) (force : Field289)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    nativeReaderContact (Fin.castAdd 6 g) 0 gradient force p F=
      ∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • noetherReaderContact (gaugeField b.2 b.1) force p F :=by
  have generated : HasDerivAt
      (fun r : ℝ=>∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • noetherReader (gaugeField b.2 b.1) p F (r • force))
      (∑b : Fin 12×Fin 4,((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ) • noetherReaderContact (gaugeField b.2 b.1) force p F) 0 :=
    HasDerivAt.fun_sum (fun b _=>(noetherReader_generated (gaugeField b.2 b.1) force p F).const_smul
      ((-gradient b.2*gaugeColorRaw g b.1 : ℝ):ℂ))
  have same:=(native_color_gradient_reader_germ g gradient p F).comp_tendsto
    (show Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 0) from by
      simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto)
  exact (nativeReader_generated (Fin.castAdd 6 g) 0 gradient force p F).unique
    (generated.congr_of_eventuallyEq same)

end LowEnergy.GaussComposite.ActualDressedNativeQuantumWard
