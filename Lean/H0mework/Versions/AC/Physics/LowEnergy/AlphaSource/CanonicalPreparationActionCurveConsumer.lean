import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationActionCoreDecomposition

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActionDecomposition
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeVariation
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

open GaussNativePotential GaussNativeMatter
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift

open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumNonlinearFieldCurve
open SU7ExteriorBreakingYukawa GaussNativeEnergy StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariationDensity

open PreparationVacuumCausalFieldResponse PreparationVacuumFieldPerturbation
open PreparationVacuumLocalizedYukawa GaussUnitaryHistory FullYSourceCutoffVolterra
open CanonicalGradedVariation
open scoped Interval

abbrev GaussOp := H →L[ℂ] H
local instance : NormedAlgebra ℝ GaussOp := NormedAlgebra.restrictScalars ℝ ℂ _

theorem rawCurve_zero_source (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (z : SourceCoordinateSlice) : rawCurve g psi p (0,z)=actualFiber p z := by
  simp only [rawCurve,statePath,zero_mul,zero_smul,add_zero,actualFiber]

theorem rawCurve_reconstruction (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (z : SourceCoordinateSlice) :
    rawCurve g psi p (r,z)=actualFiber p z+coefficientCurve g psi p r z := by
  rw [coefficientCurve,rawCurve_zero_source]
  abel

theorem variedFiber_smooth (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (small : |r|≤fieldRadius g psi) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w=>rawCurve g psi p (r,w)) z.val := by
  have same : (fun w=>rawCurve g psi p (r,w))=
      fun w=>actualFiber p w+coefficientCurve g psi p r w :=
    funext (rawCurve_reconstruction g psi p r)
  rw [same]
  exact (actualFiber_smooth p z).add (coefficientCurve_smooth g psi p r small).contDiffAt

def variedCore (g : Field289) (psi : Localizer) (p : PhysicalMomentum) (r : ℝ)
    (small : |r|≤fieldRadius g psi) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z=>rawCurve g psi p (r,z)) (variedFiber_smooth g psi p r small)

theorem variedCore_original (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (small : |r|≤fieldRadius g psi) (test : QuantumTest) (z : SourceCoordinateSlice) :
    variedCore g psi p r small test z=
      quantizer (fourierLinear p (stateHamiltonian
        (sourceState z+(r*psi z) • fieldDirection g))) (test z) := rfl

theorem variedCore_split (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (r : ℝ) (small : |r|≤fieldRadius g psi) :
    variedCore g psi p r small=actualCore p+curveCore g psi p r small := by
  apply LinearMap.ext
  intro test
  apply DFunLike.ext
  intro z
  change rawCurve g psi p (r,z) (test z)=
    actualFiber p z (test z)+coefficientCurve g psi p r z (test z)
  rw [rawCurve_reconstruction,add_apply]

-- The finite generator is read from its original compression, not defined by this decomposition.
theorem original_finite_core_decomposition (p : PhysicalMomentum) (cut : ℕ) (test : QuantumTest) :
    ∀ᶠ F in sourceFilter,
      (CanonicalPhysicalSpatial.compression p F+cutoff cut) (embed test)=
        embed ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
          actualCore p-retainedCore) test)-embed (remainderCore cut test) := by
  filter_upwards [CanonicalPhysicalSpatial.eventually_exact p (coreEquiv test)] with F hF
  change CanonicalPhysicalSpatial.compression p F (embed test)+cutoff cut (embed test)=_
  have hcore : CanonicalPhysicalSpatial.compression p F (embed test)=
      embed (CanonicalPhysicalSpatial.physicalAction p test) := hF.trans (by
    rw [CanonicalPhysicalSpatial.physical_core]
    exact (map_add embed _ _).symm)
  rw [hcore,←physical_action_decomposition,LinearMap.add_apply,map_add]
  have residual:=original_cutoff_core_residual cut test
  rw [←residual]
  abel

theorem original_nonlinear_core_decomposition (g : Field289) (psi : Localizer)
    (p : PhysicalMomentum) (cut : ℕ) (r : ℝ) (small : |r|≤fieldRadius g psi) (test : QuantumTest) :
    ∀ᶠ F in sourceFilter,
      (CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) (embed test)=
        embed ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
          variedCore g psi p r small-retainedCore) test)-embed (remainderCore cut test) := by
  filter_upwards [original_finite_core_decomposition p cut test] with F hF
  rw [add_apply,hF,matterIncrement_actual g psi p r small,curveGauss_core,variedCore_split]
  simp only [LinearMap.sub_apply,LinearMap.add_apply,map_add,map_sub]
  abel

theorem original_nonlinear_cutoff_bound (g : Field289) (psi : Localizer)
    (p : PhysicalMomentum) (cut : ℕ) (r : ℝ) (small : |r|≤fieldRadius g psi) (test : QuantumTest)
    (supported : tsupport test⊆PreparationScalarCoordinates.fullCoordinates ⁻¹'
      CanonicalPreparationCutoff.sourceClosedBox) :
    ∀ᶠ F in sourceFilter,
      ‖(CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) (embed test)-
        embed ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
          variedCore g psi p r small-retainedCore) test)‖≤
        sourceCutRate^(cut+1)*sourceRadiusBound*GaussYukawaCoefficient.bound*‖embed test‖ := by
  filter_upwards [original_nonlinear_core_decomposition g psi p cut r small test] with F hF
  rw [hF,sub_sub_cancel_left,norm_neg,←original_cutoff_core_residual]
  exact original_cutoff_source_core_bound cut test supported

section Time
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem time_differentiable_operator (C : E →L[ℂ] E) (t : ℝ) :
    DifferentiableAt ℝ (fun A : E →L[ℂ] E=>SourceFiniteUnitary.time A t) C := by
  apply (NormedSpace.exp_analytic (𝕂:=ℝ) _).differentiableAt.comp C
  fun_prop

theorem nonlinear_time_derivative (C B : E →L[ℂ] E) (curve : ℝ→E →L[ℂ] E)
    (zero : curve 0=0) (jet : HasDerivAt curve B 0) (t : ℝ) :
    HasDerivAt (fun r=>SourceFiniteUnitary.time (C+curve r) t) (variation C B t) 0 := by
  have ht:=time_differentiable_operator C t
  have hc:=(hasDerivAt_const (0:ℝ) C).add jet
  simp only [zero_add] at hc
  have nonlinear:=ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by change C=C+curve 0; rw [zero,add_zero])
  have affine : HasDerivAt (fun r : ℝ=>C+r • B) B 0 := by
    convert! (hasDerivAt_const (0:ℝ) C).add ((hasDerivAt_id (0:ℝ)).smul_const B) using 1
    simp only [zero_add,one_smul]
  have tangent:=ht.hasFDerivAt.comp_hasDerivAt_of_eq 0 affine (by simp only [zero_smul,add_zero])
  have same:=tangent.unique (parameter_derivative_full C B t)
  rw [same] at nonlinear
  exact nonlinear
end Time

theorem actual_source_time_derivative (g : Field289) (psi : Localizer) (p : PhysicalMomentum)
    (cut : ℕ) (F : Index) (t : ℝ) :
    HasDerivAt (fun r=>SourceFiniteUnitary.time
      (CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) t)
      (variation (CanonicalPhysicalSpatial.compression p F+cutoff cut) (forceGauss g p psi) t) 0 :=
  nonlinear_time_derivative _ _ _ (matterIncrement_zero g psi p) (matterIncrement_derivative g psi p) t

theorem actual_source_observable_derivative (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (cut : ℕ) (F : Index) (t : ℝ) :
    HasDerivAt (fun r=>
      SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) (-t)*
        actualReaderCurve f g phi psi p r*
      SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) t)
      ((variation (CanonicalPhysicalSpatial.compression p F+cutoff cut) (forceGauss g p psi) (-t)*
        localizedGauss f p phi+SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut) (-t)*
          contactGauss f g p (contactLocalizer phi psi))*
        SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut) t+
        SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut) (-t)*localizedGauss f p phi*
          variation (CanonicalPhysicalSpatial.compression p F+cutoff cut) (forceGauss g p psi) t) 0 := by
  have generated:=((actual_source_time_derivative g psi p cut F (-t)).mul
    (actualReaderCurve_derivative f g phi psi p)).mul (actual_source_time_derivative g psi p cut F t)
  simp only [matterIncrement_zero,actualReaderCurve_zero,add_zero,Pi.mul_apply] at generated
  convert! generated using 1

open GaussComposite GaussComposite.SourceGraph

-- The derivative is consumed by the original prepared reader, with its existing affine first-jet expression.
theorem prepared_source_observable_derivative (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (cut : ℕ) (F : Index) (t : ℝ)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    HasDerivAt (fun r=>SourceGraph.response (reader
      (SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) (-t)*
        actualReaderCurve f g phi psi p r*
       SourceFiniteUnitary.time (CanonicalPhysicalSpatial.compression p F+cutoff cut+matterIncrement g psi p r) t))
      left right lc ls rc rs u v)
      (SourceGraph.response (reader (deriv (fun r=>sourceFirstJet cut F f g phi psi p r t) 0))
        left right lc ls rc rs u v) 0 := by
  have generated:=actual_source_observable_derivative f g phi psi p cut F t
  have affine:=sourceFirstJet_derivative cut F f g phi psi p t
  rw [←affine.deriv] at generated
  have prepared:=(preparedGaussRead left right lc ls rc rs u v).hasFDerivAt.comp_hasDerivAt 0 generated
  simpa only [Function.comp_def,preparedGaussRead_eq] using prepared

end LowEnergy.PreparationVacuumActionDecomposition
