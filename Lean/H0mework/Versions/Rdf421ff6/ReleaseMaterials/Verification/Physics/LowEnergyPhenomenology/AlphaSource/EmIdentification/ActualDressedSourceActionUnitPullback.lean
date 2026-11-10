import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMCompleteSourceSpectrum
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholeNoetherPhysicalObserver
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceFieldCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMWholeUnitCovariance
open SaturationMonoid.PhysicsCore CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic SourcePropagationNativeActionHessian
open ActualEMAction GaussCoreHilbert GaussHistoryHilbert GaussCoreDifferential PreparationVacuumJointFieldResponse
open PreparationPhysicalActionUnits PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open ActualDressedFullCoulomb ActualDressedEMSourceSpectrum
open scoped BigOperators Topology Matrix ContDiff InnerProductSpace
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] emOriginalAction nativeJetDensity nativeHessian emOriginalHessian
  jointGenerator jointCurrent jointHessian Stage10.ActionNormalization.phaseMomentum
  actualC actualA physicalTime sourceDensityEnergyRead sourceActualUnitDefect

structure SourceUnits where
  energy : ℝ
  length : ℝ
  time : ℝ
  field : ℝ
  generator : ℝ
  energy_positive : 0<energy
  length_positive : 0<length
  time_positive : 0<time
  field_nonzero : field≠0
  generator_nonzero : generator≠0

def sourceDensityUnit (u : SourceUnits) : ℝ := u.length^3/u.energy

def sourceAxisUnit (u : SourceUnits) (mu : Fin 4) : ℝ := if mu=0 then u.time else u.length

/-- Values and all four derivative slots are re-expressed before evaluating the original action. -/
def sourceUnitJetLinear (u : SourceUnits) : NativeFirstJet→ₗ[ℝ]NativeFirstJet where
  toFun a := (u.field • a.1, fun mu => (u.field/sourceAxisUnit u mu) • a.2 mu)
  map_add' a b := by
    apply Prod.ext
    · exact smul_add _ _ _
    · funext mu
      exact smul_add _ _ _
  map_smul' r a := by
    apply Prod.ext
    · change u.field • (r • a.1)=r • (u.field • a.1)
      exact smul_comm _ _ _
    · funext mu
      change (u.field/sourceAxisUnit u mu) • (r • a.2 mu)=r • ((u.field/sourceAxisUnit u mu) • a.2 mu)
      exact smul_comm _ _ _

def sourceUnitJetMap (u : SourceUnits) : NativeFirstJet→L[ℝ]NativeFirstJet :=
  (sourceUnitJetLinear u).toContinuousLinearMap

def sourceUnitOriginalAction (u : SourceUnits) (a : NativeFirstJet) : ℝ :=
  sourceDensityUnit u • emOriginalAction (sourceUnitJetMap u a)

theorem source_unit_action_original (u : SourceUnits) (a : NativeFirstJet) :
    sourceUnitOriginalAction u a=sourceDensityUnit u * nativeJetDensity (sourceUnitJetMap u a) := by
  rw [sourceUnitOriginalAction,em_action_source,smul_eq_mul]

private theorem second_source_pullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E→F) (C : E→L[ℝ]E) (scale : ℝ)
    (smooth : ContDiffAt ℝ 2 f 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun x => scale • f (C x))) 0 a b=
      scale • fderiv ℝ (fderiv ℝ f) 0 (C a) (C b) := by
  have nearby : ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ f x :=
    (smooth.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have atC : ∀ᶠ x in 𝓝 (0:E), DifferentiableAt ℝ f (C x) := by
    have target : ∀ᶠ y in 𝓝 (C 0), DifferentiableAt ℝ f y := by simpa only [map_zero] using nearby
    exact C.continuous.continuousAt.eventually target
  have first : (fun x => fderiv ℝ (fun y => scale • f (C y)) x b)=ᶠ[𝓝 (0:E)]
      (fun x => scale • fderiv ℝ f (C x) (C b)) := by
    filter_upwards [atC] with x h
    have chain := (h.hasFDerivAt.comp x C.hasFDerivAt).const_smul scale
    change HasFDerivAt (fun y => scale • f (C y)) _ x at chain
    simpa only [smul_apply,ContinuousLinearMap.comp_apply] using
      congrArg (fun D : E→L[ℝ]F => D b) chain.fderiv
  have original := (smooth.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have originalAtC : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0) (C 0) := by
    simpa only [map_zero] using original
  have right := ((originalAtC.comp 0 C.hasFDerivAt).clm_apply (hasFDerivAt_const (C b) (0:E))).const_smul scale
  change HasFDerivAt (fun x => scale • fderiv ℝ f (C x) (C b)) _ 0 at right
  have transformed : ContDiffAt ℝ 2 (fun x => scale • f (C x)) 0 := by
    have smoothAtC : ContDiffAt ℝ 2 f (C 0) := by simpa only [map_zero] using smooth
    exact (smoothAtC.comp 0 (C.contDiff.contDiffAt)).const_smul scale
  have left := ((transformed.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt).clm_apply
    (hasFDerivAt_const b (0:E))
  have equation := congrArg (fun D : E→L[ℝ]F => D a) (first.fderiv_eq (𝕜:=ℝ))
  rw [left.fderiv,right.fderiv] at equation
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,smul_apply,
    add_apply,zero_apply,map_zero,add_zero,zero_add,zero_smul] using equation

def sourceUnitOriginalHessian (u : SourceUnits) : NativeFirstJet→L[ℝ]NativeFirstJet→L[ℝ]ℝ :=
  fderiv ℝ (fderiv ℝ (sourceUnitOriginalAction u)) 0

/-- Both endpoints are derivatives of the same literal source; no Hessian transformation is assumed. -/
theorem source_unit_action_hessian (u : SourceUnits) (a b : NativeFirstJet) :
    sourceUnitOriginalHessian u a b=sourceDensityUnit u * nativeHessian (sourceUnitJetMap u a) (sourceUnitJetMap u b) := by
  have smooth : ContDiffAt ℝ 2 emOriginalAction 0 := by
    have identity : emOriginalAction=nativeJetDensity := funext em_action_source
    rw [identity]
    exact nativeJetDensity_smooth.of_le (by
      change ((2:ℕ∞):ℕ∞ω)≤((⊤:ℕ∞):ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have generated := second_source_pullback emOriginalAction (sourceUnitJetMap u) (sourceDensityUnit u) smooth a b
  rw [←em_hessian_source]
  unfold sourceUnitOriginalHessian sourceUnitOriginalAction emOriginalHessian
  simpa only [smul_eq_mul] using generated

def sourceJetSlotUnit (u : SourceUnits) : Option (Fin 4)→ℝ
  | none => u.field
  | some mu => u.field/sourceAxisUnit u mu

theorem source_unit_jet_basis (u : SourceUnits) (o : Option (Fin 4)) (i : Fin 289) :
    sourceUnitJetMap u (nativeJetBasis (o,i))=sourceJetSlotUnit u o • nativeJetBasis (o,i) := by
  cases o with
  | none =>
    apply Prod.ext
    · rfl
    · funext mu
      simp [sourceUnitJetMap,sourceUnitJetLinear,nativeJetBasis,sourceJetSlotUnit]
  | some k =>
    apply Prod.ext
    · simp [sourceUnitJetMap,sourceUnitJetLinear,nativeJetBasis]
    · funext mu i
      by_cases same : mu=k
      · subst mu
        simp [sourceUnitJetMap,sourceUnitJetLinear,nativeJetBasis,sourceJetSlotUnit]
      · simp [sourceUnitJetMap,sourceUnitJetLinear,nativeJetBasis,sourceJetSlotUnit,same]

def sourceUnitFourierMomentum (u : SourceUnits) (p : Fin 4→ℂ) : Fin 4→ℂ :=
  fun mu => p mu/(sourceAxisUnit u mu : ℂ)

private theorem source_unit_jet_symbol (u : SourceUnits) (o : Option (Fin 4)) (p : Fin 4→ℂ) :
    (sourceJetSlotUnit u o : ℂ)*jetSymbol o p=
      (u.field : ℂ)*jetSymbol o (sourceUnitFourierMomentum u p) := by
  cases o
  all_goals simp only [sourceJetSlotUnit,jetSymbol,sourceUnitFourierMomentum,Complex.ofReal_div,mul_one]
  all_goals ring

def sourceUnitActionJacobi (u : SourceUnits) (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  nativeFourierHessian (sourceUnitOriginalHessian u) p

/-- The whole Fourier covariance is generated from the complete pulled-back action Hessian. -/
theorem source_unit_whole_action_jacobi (u : SourceUnits) (p : Fin 4→ℂ) :
    sourceUnitActionJacobi u p=((sourceDensityUnit u : ℂ)*(u.field : ℂ)^2) •
      emOriginalJacobi (sourceUnitFourierMomentum u p) := by
  have minus : sourceUnitFourierMomentum u (-p)= -sourceUnitFourierMomentum u p := by
    funext mu
    simp only [sourceUnitFourierMomentum,Pi.neg_apply,neg_div]
  funext i j
  simp only [sourceUnitActionJacobi,nativeFourierHessian,Matrix.smul_apply,smul_eq_mul,
    emOriginalJacobi,em_hessian_source,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  rw [source_unit_action_hessian,source_unit_jet_basis,source_unit_jet_basis]
  simp only [map_smul,smul_apply,smul_eq_mul,Complex.ofReal_mul]
  have l := source_unit_jet_symbol u left (-p)
  rw [minus] at l
  have r := source_unit_jet_symbol u right p
  linear_combination (sourceDensityUnit u : ℂ)*
    (nativeHessian (nativeJetBasis (left,i)) (nativeJetBasis (right,j)) : ℂ)*
      ((sourceJetSlotUnit u right : ℂ)*jetSymbol right p)*l+
    (sourceDensityUnit u : ℂ)*(u.field : ℂ)*
      (nativeHessian (nativeJetBasis (left,i)) (nativeJetBasis (right,j)) : ℂ)*
        jetSymbol left (-sourceUnitFourierMomentum u p)*r

/-- The source quantum generator is re-expressed in the same clock and field coordinates. -/
def sourceUnitGenerator (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (f : Field289) : H→L[ℂ]H :=
  u.time • jointGenerator (u.length⁻¹ • p) F (z/(u.time : ℂ)) (u.field • f)

def sourceUnitHamiltonian (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (f : Field289) : H→L[ℂ]H :=
  (Stage10.ActionNormalization.phaseMomentum/(u.energy*u.time)) • sourceUnitGenerator u p F 0 f

def sourceUnitCurrent (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) : Field289→L[ℝ](H→L[ℂ]H) :=
  fderiv ℝ (sourceUnitGenerator u p F z) 0

theorem source_unit_actual_current (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (force : Field289) :
    sourceUnitCurrent u p F z force=u.time •
      jointCurrent (u.length⁻¹ • p) F (z/(u.time : ℂ)) 0 (u.field • force) := by
  let C : Field289→L[ℝ]Field289 := u.field • ContinuousLinearMap.id ℝ Field289
  have d := ((jointGenerator_C2 (u.length⁻¹ • p) F (z/(u.time : ℂ))).differentiableAt (by norm_num)).hasFDerivAt
  have atC : HasFDerivAt (jointGenerator (u.length⁻¹ • p) F (z/(u.time : ℂ)))
      (fderiv ℝ (jointGenerator (u.length⁻¹ • p) F (z/(u.time : ℂ))) 0) (C 0) := by
    simpa only [map_zero] using d
  have generated := (atC.comp 0 C.hasFDerivAt).const_smul u.time
  change HasFDerivAt (sourceUnitGenerator u p F z) _ 0 at generated
  simpa only [sourceUnitCurrent,jointCurrent,smul_apply,ContinuousLinearMap.comp_apply,
    C,ContinuousLinearMap.id_apply] using
    congrArg (fun D : Field289→L[ℝ](H→L[ℂ]H) => D force) generated.fderiv

def sourceUnitQuantumHessian (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (reader force : Field289) : H→L[ℂ]H :=
  deriv (fun r : ℝ => u.time • jointCurrent (u.length⁻¹ • p) F (z/(u.time : ℂ))
    (r • (u.field • reader)) (u.field • force)) 0

theorem source_unit_actual_quantum_hessian (u : SourceUnits) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (reader force : Field289) :
    sourceUnitQuantumHessian u p F z reader force=u.time •
      jointHessian (u.length⁻¹ • p) F (z/(u.time : ℂ)) (u.field • reader) (u.field • force) := by
  exact ((current_direction (u.length⁻¹ • p) F (z/(u.time : ℂ))
    (u.field • reader) (u.field • force)).const_smul u.time).deriv

def sourceActionHamiltonian (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : H→L[ℂ]H :=
  (Stage10.ActionNormalization.phaseMomentum : ℂ) • jointGenerator p F 0 0

/-- The energy read is the original complete action read, with every source calibration retained. -/
theorem source_action_hamiltonian_energy (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (a b : QuantumTest) :
    sourceDensityEnergyRead p a b=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*inner ℂ (embed a) (jointGenerator p F 0 0 (embed b))+
        (Stage10.ActionNormalization.phaseMomentum : ℂ)*sourceActualUnitDefect p F a b := by
  have original := sourceDensityEnergyRead_actual_time p F a b
  have normalization : (Stage10.ActionNormalization.phaseMomentum : ℂ)*
      (Stage10.ActionNormalization.actionScale : ℂ)=1 := by
    rw [mul_comm]
    exact sourceActionScale_momentum
  have scaled : sourceDensityEnergyRead p a b=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*
        (inner ℂ (embed a) ((actualC p F+actualA p F) (embed b))+sourceActualUnitDefect p F a b) := by
    rw [←original,←mul_assoc,normalization,one_mul]
  rw [actualGenerator_source,scaled]
  ring

private theorem phase_energy_product (U G : H→L[ℂ]H) (h : ℂ) :
    (Complex.I*h) • (U*((-Complex.I) • G))=U*(h • G) := by
  apply ContinuousLinearMap.ext
  intro b
  change (Complex.I*h) • U ((-Complex.I) • G b)=U (h • G b)
  have scalar : (Complex.I*h)*(-Complex.I)=h := by
    calc
      _= -(Complex.I*Complex.I)*h := by ring
      _=_ := by rw [←pow_two,Complex.I_sq,neg_neg,one_mul]
  calc
    _=(Complex.I*h) • ((-Complex.I) • U (G b)) :=
      congrArg (fun v : H => (Complex.I*h) • v) (U.map_smul (-Complex.I) (G b))
    _=((Complex.I*h)*(-Complex.I)) • U (G b) := smul_smul _ _ _
    _=h • U (G b) := congrArg (fun c : ℂ => c • U (G b)) scalar
    _=U (h • G b) := (U.map_smul h (G b)).symm

/-- The action energy read, actual clock derivative and i*h conversion share the complete source generator. -/
theorem source_action_clock_energy (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) :
    HasDerivAt (fun t : ℝ => physicalTime p F t 0)
      (physicalTime p F age 0*((-Complex.I) • jointGenerator p F 0 0)) age ∧
    (Complex.I*(Stage10.ActionNormalization.phaseMomentum : ℂ)) •
      (physicalTime p F age 0*((-Complex.I) • jointGenerator p F 0 0))=
        physicalTime p F age 0*sourceActionHamiltonian p F ∧
    ∀a b : QuantumTest, sourceDensityEnergyRead p a b=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*inner ℂ (embed a) (jointGenerator p F 0 0 (embed b))+
        (Stage10.ActionNormalization.phaseMomentum : ℂ)*sourceActualUnitDefect p F a b := by
  refine ⟨?_,?_,source_action_hamiltonian_energy p F⟩
  · simpa only [actualGenerator_source] using sourceActualPhysicalTime_generated p F age
  · exact phase_energy_product (physicalTime p F age 0) (jointGenerator p F 0 0)
      (Stage10.ActionNormalization.phaseMomentum : ℂ)

end LowEnergy.GaussComposite.ActualDressedEMWholeUnitCovariance
