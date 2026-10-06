import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCausalFieldContacts
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailActualPreparation
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaPreparedDomain

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCausalFieldResponse
open GaussCoreHilbert GaussComposite GaussComposite.SourceGraph SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open CanonicalPhysicalSpatial CanonicalGradedSpatialSource CanonicalPhysicalLaplace
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open FullYSourceCutoffVolterra SourceFamilyOperator SourceFiniteUnitary
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader inclusion)
open scoped Topology InnerProductSpace BigOperators Interval
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op := NormedAlgebra.restrictScalars ℚ ℂ _

attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

section SourceForcing
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen Electromagnetic.CanonicalCoframe
open PreparationVacuumActualFieldQuantization
open scoped Matrix Matrix.Norms.L2Operator ContDiff
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

private theorem state_path (s d : ActionState) : HasDerivAt (fun r : ℝ=>s+r • d) d 0 := by
  convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
  simp

 def rawDensity (s : ActionState) (i : Fin 4) : SourceMatrix :=
  Fin.cases (stateDensityLower s) (fun j=>Complex.I • statePrincipal j.succ s) i

 theorem original_state_equation (s : ActionState) (unit : IsUnit (CoframeResponse.principalMatrix s.1)) (i : Fin 4) :
    Complex.I • (statePrincipal 0 s*stateHamiltonian s i)=rawDensity s i := by
  have cancel:=Ring.mul_inverse_cancel (CoframeResponse.principalMatrix s.1) unit
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [statePrincipal,stateHamiltonian,rawDensity,Fin.cases_zero,stateDensityLower,timeSymbol,
      ←principalMatrix_coefficient,smul_mul_assoc,mul_smul_comm,←mul_assoc,cancel,one_mul,smul_smul]
    congr 1
    ring_nf
    simp only [Complex.I_sq,neg_mul,neg_neg,one_mul]
  · simp only [statePrincipal,stateHamiltonian,rawDensity,Fin.cases_succ,
      ←principalMatrix_coefficient,smul_mul_assoc,←mul_assoc,cancel,one_mul]

private theorem phase_cancels (P M : SourceMatrix) (v : ℂ) (unit : IsUnit P) (nonzero : v≠0) :
    ((Complex.I*v⁻¹) • Ring.inverse P)*(Complex.I • ((v • P)*M))= -M := by
  have scalar : (Complex.I*v⁻¹)*(Complex.I*v)= -1 := by
    calc
      _ = (Complex.I*Complex.I)*(v⁻¹*v) := by ring
      _ = -1 := by rw [Complex.I_mul_I,inv_mul_cancel₀ nonzero,mul_one]
  calc
    _ = ((Complex.I*v⁻¹)*(Complex.I*v)) • ((Ring.inverse P*P)*M) := by
      simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_assoc]
      congr 1
      ring
    _ = -M := by rw [Ring.inverse_mul_cancel P unit,one_mul,scalar,neg_one_smul]

 theorem state_forcing_generated (f : Field289) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    HasDerivAt (fun r : ℝ=>stateHamiltonian (s+r • fieldDirection f) i)
      (-(statePhase s*densityVariation f s i)) 0 := by
  let D:=fderiv ℝ (fun w=>stateHamiltonian w i) s (fieldDirection f)
  have hH : HasDerivAt (fun r : ℝ=>stateHamiltonian (s+r • fieldDirection f) i) D 0 :=
    ((stateHamiltonian_smooth s nondegenerate regular i).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
      (state_path s (fieldDirection f)) (by simp)
  have hP:=principalVariation_generated f 0 s nondegenerate
  have product:=((hP.mul hH).const_smul Complex.I)
  have raw : HasDerivAt (fun r : ℝ=>rawDensity (s+r • fieldDirection f) i)
      (Fin.cases (lowerVariation f s) (fun j=>Complex.I • principalVariation f j.succ s) i) 0 := by
    refine Fin.cases (lowerVariation_generated f s nondegenerate) (fun j=>?_) i
    exact (principalVariation_generated f j.succ s nondegenerate).const_smul Complex.I
  have principal_cont : ContinuousAt (fun r : ℝ=>CoframeResponse.principalMatrix (s+r • fieldDirection f).1) 0 := by
    have smooth:=((principalMatrix_smooth s.1 nondegenerate).comp s contDiffAt_fst).continuousAt
    exact smooth.comp_of_eq (state_path s (fieldDirection f)).continuousAt (by simp)
  have units : ∀ᶠ r : ℝ in 𝓝 0,IsUnit (CoframeResponse.principalMatrix (s+r • fieldDirection f).1) :=
    principal_cont.eventually (Units.isOpen.mem_nhds (by simpa only [Set.mem_ofPred_eq,zero_smul,add_zero] using! principalMatrix_regular s.1 regular))
  have equations : (fun r : ℝ=>Complex.I • (statePrincipal 0 (s+r • fieldDirection f)*stateHamiltonian (s+r • fieldDirection f) i))=ᶠ[𝓝 0]
      (fun r=>rawDensity (s+r • fieldDirection f) i) := by
    filter_upwards [units] with r hr
    exact original_state_equation _ hr i
  have differentiated:=raw.unique (product.congr_of_eventuallyEq equations.symm)
  simp only [zero_smul,add_zero] at differentiated
  have density : densityVariation f s i=Complex.I • (statePrincipal 0 s*D) := by
    unfold densityVariation
    rw [differentiated,smul_add,add_sub_cancel_left]
  have vnonzero : stateVolume s≠0 := by
    unfold stateVolume
    exact_mod_cast (abs_ne_zero.mpr nondegenerate)
  have read : statePhase s*densityVariation f s i= -D := by
    rw [density]
    change ((Complex.I*(stateVolume s)⁻¹) • Ring.inverse (CoframeResponse.principalMatrix s.1))*
      (Complex.I • ((stateVolume s • coefficientMatrix 0 s.1)*D))= -D
    rw [←principalMatrix_coefficient]
    exact phase_cancels _ _ _ (principalMatrix_regular s.1 regular) vnonzero
  exact hH.congr_deriv (by rw [read,neg_neg])

 theorem actual_forcing_generated (f : Field289) (z : GaussHistoryHilbert.physicalChart) (i : Fin 4) :
    HasDerivAt (fun r : ℝ=>stateHamiltonian (sourceState z.val+r • fieldDirection f) i)
      (-familyReader f z.val i) 0 := by
  convert! state_forcing_generated f (sourceState z.val) (coframe_nondegenerate z)
    (CanonicalGradedSpatialSource.temporal_noncharacteristic z) i using 1

 theorem actual_quantized_forcing (f : Field289) (p : PhysicalMomentum) (z : GaussHistoryHilbert.physicalChart) :
    HasDerivAt (fun r : ℝ=>GaussQuantumMultiplier.quantizer (fourierLinear p
      (stateHamiltonian (sourceState z.val+r • fieldDirection f)))) (-fiberFamily f p z.val) 0 := by
  have native : HasDerivAt (fun r : ℝ=>stateHamiltonian (sourceState z.val+r • fieldDirection f))
      (fun i=> -familyReader f z.val i) 0 := hasDerivAt_pi.mpr (fun i=>actual_forcing_generated f z i)
  let Q : (Fin 4→SourceMatrix) →L[ℝ] FiberMap :=
    (GaussQuantumMultiplier.quantizer.toContinuousLinearMap.restrictScalars ℝ).comp (fourierLinear p).toContinuousLinearMap
  have generated:=Q.hasFDerivAt.comp_hasDerivAt 0 native
  convert! generated using 1
  change -GaussQuantumMultiplier.quantizer (fourierLinear p (familyReader f z.val))=
    GaussQuantumMultiplier.quantizer (fourierLinear p (-familyReader f z.val))
  rw [map_neg,map_neg]

end SourceForcing

open GaussCoreDifferential GaussQuantumMultiplier
open scoped ContDiff

def forceCoefficient (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) : FiberMap :=
  (phi z:ℂ) • deriv (fun r : ℝ=>GaussQuantumMultiplier.quantizer
    (PreparationVacuumActualFieldQuantization.fourierLinear p (stateHamiltonian (sourceState z+r • fieldDirection f)))) 0

theorem forceCoefficient_generated (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    forceCoefficient f p phi z= -localizedCoefficient f p phi z := by
  by_cases inside : z∈tsupport phi
  · have generated:=(actual_quantized_forcing f p ⟨z,phi.tsupport_subset inside⟩).deriv
    unfold forceCoefficient
    rw [generated]
    exact smul_neg _ _
  · unfold forceCoefficient localizedCoefficient
    rw [image_eq_zero_of_notMem_tsupport inside,Complex.ofReal_zero]
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,neg_apply,zero_smul,neg_zero]

theorem force_smooth (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    ContDiff ℝ ∞ (forceCoefficient f p phi) := by
  have generated : forceCoefficient f p phi=(fun z=> -localizedCoefficient f p phi z) :=
    funext (forceCoefficient_generated f p phi)
  rw [generated]
  exact (localized_smooth f p phi).neg

theorem force_weights (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (GaussFockWeights.weight w) (forceCoefficient f p phi z) := by
  rw [forceCoefficient_generated]
  exact (localized_weights f p phi z w).neg_right

theorem force_bound (f : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) (v : FockFiber) :
    ‖forceCoefficient f p phi z v‖ ≤ localBound f p phi*‖v‖ := by
  rw [forceCoefficient_generated,neg_apply,norm_neg]
  exact local_bound f p phi z v

def forceCore (f : Field289) (p : PhysicalMomentum) (phi : Localizer) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (forceCoefficient f p phi) (fun _=>(force_smooth f p phi).contDiffAt)

def forceGauss (f : Field289) (p : PhysicalMomentum) (phi : Localizer) : Op :=
  GaussBoundedMultiplier.extension (forceCoefficient f p phi) (fun _=>(force_smooth f p phi).contDiffAt)
    (fun z w=>force_weights f p phi z w) (localBound f p phi) (localBound_nonnegative f p phi)
    (fun z=>force_bound f p phi z)

theorem forceGauss_core (f : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest) :
    forceGauss f p phi (embed test)=embed (forceCore f p phi test) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ test

theorem forceCore_generated (f : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest) :
    forceCore f p phi test= -(localizedCore f p phi test) := by
  apply DFunLike.ext
  intro z
  change forceCoefficient f p phi z (test z)= -localizedCoefficient f p phi z (test z)
  rw [forceCoefficient_generated]
  rfl

theorem forceGauss_generated (f : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    forceGauss f p phi= -localizedGauss f p phi := by
  apply GaussYukawaGrade.core_ext
  intro test
  change forceGauss f p phi (embed test)=(-localizedGauss f p phi) (embed test)
  rw [forceGauss_core,forceCore_generated,map_neg,neg_apply,localizedGauss_core]


abbrev FourierSection := PhysicalMomentum → H

def fullTime (cut : ℕ) (F : Index) (t : ℝ) (v : FourierSection) : FourierSection :=
  fun q=>time (compression q F+cutoff cut) t (v q)

def fieldCurrent (f : Field289) (phi : Localizer) (k : PhysicalMomentum)
    (v : FourierSection) : FourierSection := fun q=>localizedGauss f (q-k) phi (v (q-k))

def fieldWord (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (k ell : PhysicalMomentum) (t s : ℝ) (v : FourierSection) : FourierSection :=
  fullTime cut F (-t) (fieldCurrent f phi k (fullTime cut F (t-s)
    (fieldCurrent g psi ell (fullTime cut F s v))))

def orderedField (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : Op :=
  time (compression (p+k+ell) F+cutoff cut) (-t)*localizedGauss f (p+ell) phi*
    time (compression (p+ell) F+cutoff cut) (t-s)*localizedGauss g p psi*
      time (compression p F+cutoff cut) s

 theorem fieldWord_read (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) (v : FourierSection) :
    fieldWord cut F f g phi psi k ell t s v (p+k+ell)=orderedField cut F f g phi psi p k ell t s (v p) := by
  have route : p+k+ell-k=p+ell := by abel
  simp only [fieldWord,fullTime,fieldCurrent,route,add_sub_cancel_right,orderedField,mul_apply_eq_comp]

 def finiteKernel (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : Op :=
  (-Complex.I) • (orderedField cut F g f psi phi p ell k s t-orderedField cut F f g phi psi p k ell t s)

 def actualKernel (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : Op :=
  Complex.I •
    (CanonicalGradedBilocal.ordered (compression (p+k+ell) F+cutoff cut) (compression p F+cutoff cut)
      (compression (p+k) F+cutoff cut) (forceGauss g (p+k) psi) (localizedGauss f p phi) s t-
    CanonicalGradedBilocal.ordered (compression (p+k+ell) F+cutoff cut) (compression p F+cutoff cut)
      (compression (p+ell) F+cutoff cut) (localizedGauss f (p+ell) phi) (forceGauss g p psi) t s)

 theorem actualKernel_generated (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    actualKernel cut F f g phi psi p k ell t s=finiteKernel cut F f g phi psi p k ell t s := by
  have exchange : p+ell+k=p+k+ell := by abel
  simp only [actualKernel,CanonicalGradedBilocal.ordered,forceGauss_generated,finiteKernel,orderedField,exchange,mul_neg,neg_mul,
    neg_smul,smul_neg,smul_sub]

 theorem finiteKernel_fourier (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) (v : FourierSection) :
    finiteKernel cut F f g phi psi p k ell t s (v p)=(-Complex.I) •
      (fieldWord cut F g f psi phi ell k s t v (p+k+ell)-fieldWord cut F f g phi psi k ell t s v (p+k+ell)) := by
  have exchange : p+ell+k=p+k+ell := by abel
  have reverse:=fieldWord_read cut F g f psi phi p ell k s t v
  rw [exchange] at reverse
  rw [reverse,fieldWord_read]
  rfl

 theorem timeBound_neg (cut : ℕ) (t : ℝ) : timeBound cut (-t)=timeBound cut t := by
  simp only [timeBound,abs_neg]

 def wordBound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p ell : PhysicalMomentum) (t s : ℝ) : ℝ :=
  timeBound cut t*localBound f (p+ell) phi*timeBound cut (t-s)*localBound g p psi*timeBound cut s

 theorem wordBound_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p ell : PhysicalMomentum) (t s : ℝ) : 0 ≤ wordBound cut f g phi psi p ell t s := by
  unfold wordBound
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (timeBound_nonneg cut t)
    (localBound_nonnegative f (p+ell) phi)) (timeBound_nonneg cut (t-s))) (localBound_nonnegative g p psi))
      (timeBound_nonneg cut s)

 theorem orderedField_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    ‖orderedField cut F f g phi psi p k ell t s‖ ≤ wordBound cut f g phi psi p ell t s := by
  have out := full_time_bound (p+k+ell) F cut (-t)
  rw [timeBound_neg] at out
  have := timeBound_nonneg cut t
  have := timeBound_nonneg cut (t-s)
  have := localBound_nonnegative f (p+ell) phi
  have := localBound_nonnegative g p psi
  unfold orderedField wordBound
  apply (norm_mul_le _ _).trans
  apply mul_le_mul _ (full_time_bound p F cut s) (norm_nonneg _) (by positivity)
  apply (norm_mul_le _ _).trans
  apply mul_le_mul _ (localizedGauss_norm g p psi) (norm_nonneg _) (by positivity)
  apply (norm_mul_le _ _).trans
  apply mul_le_mul _ (full_time_bound (p+ell) F cut (t-s)) (norm_nonneg _) (by positivity)
  exact (norm_mul_le _ _).trans (mul_le_mul out (localizedGauss_norm f (p+ell) phi) (norm_nonneg _) (timeBound_nonneg cut t))

 def kernelBound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : ℝ :=
  wordBound cut g f psi phi p k s t+wordBound cut f g phi psi p ell t s

 theorem kernelBound_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : 0 ≤ kernelBound cut f g phi psi p k ell t s :=
  add_nonneg (wordBound_nonneg cut g f psi phi p k s t) (wordBound_nonneg cut f g phi psi p ell t s)

 theorem finiteKernel_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    ‖finiteKernel cut F f g phi psi p k ell t s‖ ≤ kernelBound cut f g phi psi p k ell t s := by
  rw [finiteKernel,norm_smul,norm_neg,Complex.norm_I,one_mul]
  exact (norm_sub_le _ _).trans (add_le_add (orderedField_bound cut F g f psi phi p ell k s t)
    (orderedField_bound cut F f g phi psi p k ell t s))

 theorem actualKernel_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    ‖actualKernel cut F f g phi psi p k ell t s‖ ≤ kernelBound cut f g phi psi p k ell t s := by
  rw [actualKernel_generated]
  exact finiteKernel_bound cut F f g phi psi p k ell t s

 def kernelFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : Operator Index H where
  component F:=actualKernel cut F f g phi psi p k ell t s
  bounded:=⟨kernelBound cut f g phi psi p k ell t s,kernelBound_nonneg cut f g phi psi p k ell t s,
    fun F v=>((actualKernel cut F f g phi psi p k ell t s).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (actualKernel_bound cut F f g phi psi p k ell t s) (norm_nonneg v))⟩

 def twoTime (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (kernelFamily cut f g phi psi p k ell t s)

 theorem twoTime_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    ‖twoTime cut f g phi psi p k ell t s‖ ≤ kernelBound cut f g phi psi p k ell t s :=
  CanonicalGradedVariation.lift_bound sourceFilter _ _ (kernelBound_nonneg cut f g phi psi p k ell t s)
    (fun F=>actualKernel_bound cut F f g phi psi p k ell t s)

 def causalTwoTime (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  if s≤t then twoTime cut f g phi psi p k ell t s else 0

 theorem causal_past_zero (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) (past : t<s) :
    causalTwoTime cut f g phi psi p k ell t s=0 := if_neg (not_le.mpr past)

 theorem causalTwoTime_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    ‖causalTwoTime cut f g phi psi p k ell t s‖ ≤ kernelBound cut f g phi psi p k ell t s := by
  unfold causalTwoTime
  split_ifs
  · exact twoTime_bound cut f g phi psi p k ell t s
  · simpa only [norm_zero] using kernelBound_nonneg cut f g phi psi p k ell t s

 def preparedCausal (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) : ℂ :=
  SourceGraph.response (causalTwoTime cut f g phi psi p k ell t s) left right lc ls rc rs u v

 theorem preparedCausal_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖preparedCausal cut f g phi psi p k ell t s left right lc ls rc rs u v‖ ≤
      legBound^2*kernelBound cut f g phi psi p k ell t s*‖u‖*‖v‖ := by
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (causalTwoTime_bound cut f g phi psi p k ell t s) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

 theorem finite_equal_time (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) :
    finiteKernel cut F f g phi psi p k ell t t=
      (-Complex.I) • (time (compression (p+k+ell) F+cutoff cut) (-t)*
        (localizedGauss g (p+k) psi*localizedGauss f p phi-
         localizedGauss f (p+ell) phi*localizedGauss g p psi)*time (compression p F+cutoff cut) t) := by
  have exchange : p+ell+k=p+k+ell := by abel
  simp only [finiteKernel,orderedField,exchange,sub_self,SourceFiniteUnitary.time_zero,mul_one,mul_sub,sub_mul,mul_assoc]

 def finiteContact (cut : ℕ) (F : Index) (f g : Field289) (phi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : Op :=
  time (compression (p+k+ell) F+cutoff cut) (-t)*contactGauss f g p phi*time (compression p F+cutoff cut) t

 def contactTimeBound (cut : ℕ) (f g : Field289) (phi : Localizer)
    (p : PhysicalMomentum) (t : ℝ) : ℝ :=timeBound cut t*contactBound f g p phi*timeBound cut t

 theorem contactTimeBound_nonneg (cut : ℕ) (f g : Field289) (phi : Localizer)
    (p : PhysicalMomentum) (t : ℝ) : 0 ≤ contactTimeBound cut f g phi p t :=
  mul_nonneg (mul_nonneg (timeBound_nonneg cut t) (contactBound_nonneg f g p phi)) (timeBound_nonneg cut t)

 theorem finiteContact_bound (cut : ℕ) (F : Index) (f g : Field289) (phi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) :
    ‖finiteContact cut F f g phi p k ell t‖ ≤ contactTimeBound cut f g phi p t := by
  have out:=full_time_bound (p+k+ell) F cut (-t)
  rw [timeBound_neg] at out
  exact (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
    (mul_le_mul out (contactGauss_norm f g p phi) (norm_nonneg _) (timeBound_nonneg cut t)))
      (full_time_bound p F cut t) (norm_nonneg _)
        (mul_nonneg (timeBound_nonneg cut t) (contactBound_nonneg f g p phi)))

 def contactFamily (cut : ℕ) (f g : Field289) (phi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : Operator Index H where
  component F:=finiteContact cut F f g phi p k ell t
  bounded:=⟨contactTimeBound cut f g phi p t,contactTimeBound_nonneg cut f g phi p t,
    fun F v=>((finiteContact cut F f g phi p k ell t).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (finiteContact_bound cut F f g phi p k ell t) (norm_nonneg v))⟩

 def directContact (cut : ℕ) (f g : Field289) (phi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (contactFamily cut f g phi p k ell t)

 theorem directContact_bound (cut : ℕ) (f g : Field289) (phi : Localizer)
    (p k ell : PhysicalMomentum) (t : ℝ) :
    ‖directContact cut f g phi p k ell t‖ ≤ contactTimeBound cut f g phi p t :=
  CanonicalGradedVariation.lift_bound sourceFilter _ _ (contactTimeBound_nonneg cut f g phi p t)
    (fun F=>finiteContact_bound cut F f g phi p k ell t)

/- The first jet is generated by the original density/phase/shell variation; it is
kept inside both original finite time legs before the common source completion. -/


 def contactLocalizer (phi psi : Localizer) : Localizer where
  toFun z:=phi z*psi z
  contDiff':=phi.contDiff.mul psi.contDiff
  hasCompactSupport':=phi.hasCompactSupport.mul_right
  tsupport_subset':=tsupport_mul_subset_left.trans phi.tsupport_subset

 theorem actual_core_contact_derivative (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (test : GaussCoreDifferential.QuantumTest) (z : GaussHistoryHilbert.physicalChart) :
    HasDerivAt (fun r : ℝ=>(phi z.val:ℂ) • stateFiber f p (sourceState z.val+r • fieldDirection g) (test z.val))
      (contactCoefficient f g p phi z.val (test z.val)) 0 := by
  have applied := ((ContinuousLinearMap.apply ℂ FockFiber (test z.val)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (contactFiber_derivative f g p z)
  have generated := applied.const_smul (phi z.val:ℂ)
  convert! generated using 1

private theorem parameter_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ→E) (D : E) (h : HasDerivAt F D 0) (a : ℝ) :
    HasDerivAt (fun r : ℝ=>F (r*a)) (a • D) 0 := by
  have generated:=h.scomp_of_eq 0 ((hasDerivAt_id (0:ℝ)).mul_const a) (by simp only [id_eq,zero_mul])
  simpa only [Function.comp_def,id_eq,one_mul] using generated

private theorem joint_scalar {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] (a b : ℝ) (v : E) :
    b • ((a:ℂ) • v)=((a*b:ℝ):ℂ) • v := by
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul,Complex.ofReal_mul,mul_comm]
  rfl

 theorem actual_joint_contact_derivative (f g : Field289) (p : PhysicalMomentum) (phi psi : Localizer)
    (test : GaussCoreDifferential.QuantumTest) (z : GaussHistoryHilbert.physicalChart) :
    HasDerivAt (fun r : ℝ=>(phi z.val:ℂ) • stateFiber f p
      (sourceState z.val+(r*psi z.val) • fieldDirection g) (test z.val))
      (contactCoefficient f g p (contactLocalizer phi psi) z.val (test z.val)) 0 := by
  have generated:=parameter_scale _ _ (actual_core_contact_derivative f g p phi test z) (psi z.val)
  apply generated.congr_deriv
  exact joint_scalar (phi z.val) (psi z.val) (contactFiber f g p z.val (test z.val))

 def sourceFirstJet (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (r t : ℝ) : Op :=
  time (compression p F+cutoff cut+r • forceGauss g p psi) (-t)*
    (localizedGauss f p phi+r • contactGauss f g p (contactLocalizer phi psi))*
      time (compression p F+cutoff cut+r • forceGauss g p psi) t

 theorem observable_firstjet_derivative (C A B D : Op) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>time (C+r • B) (-t)*(A+r • D)*time (C+r • B) t)
      ((CanonicalGradedVariation.variation C B (-t)*A+time C (-t)*D)*time C t+
        time C (-t)*A*CanonicalGradedVariation.variation C B t) 0 := by
  have observed : HasDerivAt (fun r : ℝ=>A+r • D) D 0 := by
    convert! (hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).smul_const D) using 1
    simp only [zero_add,one_smul]
  have generated:=((parameter_derivative_full C B (-t)).mul observed).mul (parameter_derivative_full C B t)
  simp only [Pi.mul_apply] at generated
  have zB : (0 : ℝ) • B=0 := zero_smul ℝ B
  have zD : (0 : ℝ) • D=0 := zero_smul ℝ D
  simp only [zB,zD,add_zero] at generated
  exact generated

 theorem sourceFirstJet_derivative (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p : PhysicalMomentum) (t : ℝ) :
    HasDerivAt (fun r : ℝ=>sourceFirstJet cut F f g phi psi p r t)
      ((CanonicalGradedVariation.variation (compression p F+cutoff cut) (forceGauss g p psi) (-t)*
        localizedGauss f p phi+time (compression p F+cutoff cut) (-t)*contactGauss f g p (contactLocalizer phi psi))*
          time (compression p F+cutoff cut) t+
        time (compression p F+cutoff cut) (-t)*localizedGauss f p phi*
          CanonicalGradedVariation.variation (compression p F+cutoff cut) (forceGauss g p psi) t) 0 :=
  observable_firstjet_derivative _ _ _ _ t

open MeasureTheory Set Filter
open SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
local instance : SecondCountableTopologyEither ℝ Op := ⟨Or.inl inferInstance⟩

 theorem timeBound_polynomial (cut : ℕ) (t Q : ℝ) (one : 1 ≤ Q)
    (dominates : |t| *‖cutoff cut‖ ≤ Q) : timeBound cut t ≤ 57*Q^56 := by
  unfold timeBound
  calc
    _ ≤ ∑ n∈Finset.range 57,Q^56 := by
      apply Finset.sum_le_sum
      intro n hn
      exact (pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) (norm_nonneg _)) dominates n).trans
        (pow_le_pow_right₀ one (by have := Finset.mem_range.mp hn;omega))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_ofNat]

 def fieldScale (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age : ℝ) : ℝ :=
  57^3*((1+|age|)*(1+‖cutoff cut‖))^168*
    (localBound g (p+k) psi*localBound f p phi+localBound f (p+ell) phi*localBound g p psi)

 theorem fieldScale_nonneg (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age : ℝ) : 0 ≤ fieldScale cut f g phi psi p k ell age := by
  exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 57^3)
    (pow_nonneg (mul_nonneg (add_nonneg zero_le_one (abs_nonneg age))
      (add_nonneg zero_le_one (norm_nonneg _))) 168))
    (add_nonneg (mul_nonneg (localBound_nonnegative g (p+k) psi) (localBound_nonnegative f p phi))
      (mul_nonneg (localBound_nonnegative f (p+ell) phi) (localBound_nonnegative g p psi)))

private theorem triple_bound (x y z a b Q : ℝ) (hx : x ≤ Q) (hy : y ≤ Q) (hz : z ≤ Q)
    (_nx : 0 ≤ x) (_ny : 0 ≤ y) (_nz : 0 ≤ z) (_na : 0 ≤ a) (_nb : 0 ≤ b) (_nQ : 0 ≤ Q) :
    x*a*y*b*z ≤ Q*a*Q*b*Q := by
  gcongr

 theorem kernel_polynomial (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age lag : ℝ) (future : 0 ≤ lag) :
    ‖finiteKernel cut F f g phi psi p k ell (age+lag) age‖ ≤
      fieldScale cut f g phi psi p k ell age*(1+lag)^168 := by
  let Q := ((1+|age|)*(1+‖cutoff cut‖))*(1+lag)
  have aa : 0 ≤ |age| := abs_nonneg age
  have yy : 0 ≤ ‖cutoff cut‖ := norm_nonneg _
  have one : 1 ≤ Q :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) (by linarith)
  have pos : 0 ≤ Q := zero_le_one.trans one
  have qage : |age| *‖cutoff cut‖ ≤ Q := by
    apply (mul_le_mul (show |age| ≤ 1+|age| by linarith)
      (show ‖cutoff cut‖ ≤ 1+‖cutoff cut‖ by linarith) yy (by positivity)).trans
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have qlag : |lag| *‖cutoff cut‖ ≤ Q := by
    rw [abs_of_nonneg future]
    calc
      _ ≤ (1+lag)*(1+‖cutoff cut‖) := mul_le_mul (by linarith) (by linarith) yy (by positivity)
      _ ≤ (1+|age|)*((1+lag)*(1+‖cutoff cut‖)) := le_mul_of_one_le_left (by positivity) (by linarith)
      _ = Q := by unfold Q;ring
  have qsum : |age+lag| *‖cutoff cut‖ ≤ Q := by
    have triangle := abs_add_le age lag
    rw [abs_of_nonneg future] at triangle
    have sum : |age|+lag ≤ (1+|age|)*(1+lag) := by nlinarith [mul_nonneg aa future]
    calc
      _ ≤ ((1+|age|)*(1+lag))*(1+‖cutoff cut‖) :=
        mul_le_mul (triangle.trans sum) (by linarith) yy (by positivity)
      _ = Q := by unfold Q;ring
  have ha:=timeBound_polynomial cut age Q one qage
  have hl:=timeBound_polynomial cut lag Q one qlag
  have ht:=timeBound_polynomial cut (age+lag) Q one qsum
  have neg : timeBound cut (age-(age+lag))=timeBound cut lag := by
    rw [show age-(age+lag)=-lag by ring,timeBound_neg]
  have forward := wordBound_nonneg cut f g phi psi p ell (age+lag) age
  have reverse := wordBound_nonneg cut g f psi phi p k age (age+lag)
  have fa := localBound_nonnegative f (p+ell) phi
  have fb := localBound_nonnegative g p psi
  have ga := localBound_nonnegative g (p+k) psi
  have gb := localBound_nonnegative f p phi
  apply (finiteKernel_bound cut F f g phi psi p k ell (age+lag) age).trans
  unfold kernelBound wordBound
  rw [neg,add_sub_cancel_left]
  calc
    _ ≤ (57*Q^56)*localBound g (p+k) psi*(57*Q^56)*localBound f p phi*(57*Q^56)+
      (57*Q^56)*localBound f (p+ell) phi*(57*Q^56)*localBound g p psi*(57*Q^56) := by
      have nQ : 0 ≤ 57*Q^56 := mul_nonneg (by norm_num) (pow_nonneg pos 56)
      exact add_le_add
        (triple_bound _ _ _ _ _ _ ha hl ht (timeBound_nonneg cut age) (timeBound_nonneg cut lag)
          (timeBound_nonneg cut (age+lag)) ga gb nQ)
        (triple_bound _ _ _ _ _ _ ht hl ha (timeBound_nonneg cut (age+lag)) (timeBound_nonneg cut lag)
          (timeBound_nonneg cut age) fa fb nQ)
    _ = _ := by
      have algebra (x y a b c d : ℝ) :
          (57*(x*y)^56)*a*(57*(x*y)^56)*b*(57*(x*y)^56)+
            (57*(x*y)^56)*c*(57*(x*y)^56)*d*(57*(x*y)^56)=
              57^3*x^168*(a*b+c*d)*y^168 := by ring
      exact algebra ((1+|age|)*(1+‖cutoff cut‖)) (1+lag) _ _ _ _

 def dampedPolynomial (damping : ℝ) (n : ℕ) (t : ℝ) : ℝ :=Real.exp (-damping*t)*(t+1)^n

 theorem dampedPolynomial_integrable (damping : ℝ) (positive : 0<damping) (n : ℕ) :
    IntegrableOn (dampedPolynomial damping n) (Ioi 0) := by
  have same : dampedPolynomial damping n=(fun t=>∑ j∈Finset.range (n+1),
      (Real.exp (-damping*t)*t^j)*(n.choose j : ℝ)) := by
    funext t
    simp only [dampedPolynomial,add_pow,one_pow,mul_one,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [same]
  exact integrable_finsetSum _ (fun j _=>(damping_moment_integrable j damping positive).mul_const _)

 def dampingTail (damping T : ℝ) : ℝ :=∫ lag in Ioi T,dampedPolynomial damping 168 lag

 theorem dampingTail_zero (damping : ℝ) : Tendsto (dampingTail damping) atTop (𝓝 0) :=
  MeasureTheory.tendsto_integral_Ioi_zero (f:=dampedPolynomial damping 168) tendsto_id

 def dampedKernel (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping lag : ℝ) : Op :=
  CanonicalGradedFrequency.weight frequency damping lag • actualKernel cut F f g phi psi p k ell (age+lag) age

 theorem dampedKernel_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping lag : ℝ) (future : 0 ≤ lag) :
    ‖dampedKernel cut F f g phi psi p k ell age frequency damping lag‖ ≤
      dampedPolynomial damping 168 lag*fieldScale cut f g phi psi p k ell age := by
  rw [dampedKernel,norm_smul,CanonicalGradedFrequency.weight_norm,actualKernel_generated]
  exact (mul_le_mul_of_nonneg_left (kernel_polynomial cut F f g phi psi p k ell age lag future)
    (Real.exp_pos _).le).trans_eq (by unfold dampedPolynomial;rw [add_comm lag 1];ring)

 theorem dampedKernel_integrable (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) :
    IntegrableOn (dampedKernel cut F f g phi psi p k ell age frequency damping) (Ioi 0) := by
  have continuous : Continuous (dampedKernel cut F f g phi psi p k ell age frequency damping) := by
    change Continuous (fun lag : ℝ=>CanonicalGradedFrequency.weight frequency damping lag •
      actualKernel cut F f g phi psi p k ell (age+lag) age)
    simp only [actualKernel_generated]
    unfold finiteKernel orderedField CanonicalGradedFrequency.weight SourceFiniteUnitary.time
    fun_prop
  apply ((dampedPolynomial_integrable damping positive 168).mul_const
    (fieldScale cut f g phi psi p k ell age)).mono' continuous.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
  exact dampedKernel_bound cut F f g phi psi p k ell age frequency damping lag hlag.le

 def finiteResponse (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) : Op :=
  ∫ lag in Ioi 0,dampedKernel cut F f g phi psi p k ell age frequency damping lag

 def finiteTruncation (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) : Op :=
  ∫ lag in (0:ℝ)..T,dampedKernel cut F f g phi psi p k ell age frequency damping lag

 theorem finiteResponse_tail (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    ‖finiteResponse cut F f g phi psi p k ell age frequency damping-
      finiteTruncation cut F f g phi psi p k ell age frequency damping T‖ ≤
      dampingTail damping T*fieldScale cut f g phi psi p k ell age := by
  have integrable:=dampedKernel_integrable cut F f g phi psi p k ell age frequency damping positive
  have split:=intervalIntegral.integral_interval_add_Ioi integrable (integrable.mono_set (Ioi_subset_Ioi future))
  unfold finiteResponse finiteTruncation
  rw [←split,add_sub_cancel_left]
  have h:=norm_integral_le_of_norm_le
    (((dampedPolynomial_integrable damping positive 168).mono_set (Ioi_subset_Ioi future)).mul_const
      (fieldScale cut f g phi psi p k ell age))
    (show ∀ᵐ lag ∂volume.restrict (Ioi T),‖dampedKernel cut F f g phi psi p k ell age frequency damping lag‖ ≤
      dampedPolynomial damping 168 lag*fieldScale cut f g phi psi p k ell age from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
        exact dampedKernel_bound cut F f g phi psi p k ell age frequency damping lag (future.trans hlag.le))
  rw [integral_mul_const] at h
  exact h

 theorem dampingTail_nonneg (damping T : ℝ) (future : 0 ≤ T) : 0 ≤ dampingTail damping T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
  unfold dampedPolynomial
  have : 0 ≤ lag := future.trans hlag.le
  positivity

 theorem finiteResponse_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) :
    ‖finiteResponse cut F f g phi psi p k ell age frequency damping‖ ≤
      dampingTail damping 0*fieldScale cut f g phi psi p k ell age := by
  simpa only [finiteTruncation,intervalIntegral.integral_same,sub_zero] using
    finiteResponse_tail cut F f g phi psi p k ell age frequency damping 0 positive le_rfl

 def responseFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) : Operator Index H where
  component F:=finiteResponse cut F f g phi psi p k ell age frequency damping
  bounded:=⟨dampingTail damping 0*fieldScale cut f g phi psi p k ell age,
    mul_nonneg (dampingTail_nonneg damping 0 le_rfl) (fieldScale_nonneg cut f g phi psi p k ell age),
    fun F v=>((finiteResponse cut F f g phi psi p k ell age frequency damping).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (finiteResponse_bound cut F f g phi psi p k ell age frequency damping positive) (norm_nonneg v))⟩

 def response (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily cut f g phi psi p k ell age frequency damping positive)

 theorem response_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) :
    ‖response cut f g phi psi p k ell age frequency damping positive‖ ≤
      dampingTail damping 0*fieldScale cut f g phi psi p k ell age :=
  CanonicalGradedVariation.lift_bound sourceFilter _ _
    (mul_nonneg (dampingTail_nonneg damping 0 le_rfl) (fieldScale_nonneg cut f g phi psi p k ell age))
    (fun F=>finiteResponse_bound cut F f g phi psi p k ell age frequency damping positive)

 def tailFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) : Operator Index H where
  component F:=finiteResponse cut F f g phi psi p k ell age frequency damping-
    finiteTruncation cut F f g phi psi p k ell age frequency damping T
  bounded:=⟨dampingTail damping T*fieldScale cut f g phi psi p k ell age,
    mul_nonneg (dampingTail_nonneg damping T future) (fieldScale_nonneg cut f g phi psi p k ell age),
    fun F v=>((finiteResponse cut F f g phi psi p k ell age frequency damping-
      finiteTruncation cut F f g phi psi p k ell age frequency damping T).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (finiteResponse_tail cut F f g phi psi p k ell age frequency damping T positive future) (norm_nonneg v))⟩

 def responseTail (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (tailFamily cut f g phi psi p k ell age frequency damping T positive future)

 theorem responseTail_bound (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    ‖responseTail cut f g phi psi p k ell age frequency damping T positive future‖ ≤
      dampingTail damping T*fieldScale cut f g phi psi p k ell age :=
  CanonicalGradedVariation.lift_bound sourceFilter _ _
    (mul_nonneg (dampingTail_nonneg damping T future) (fieldScale_nonneg cut f g phi psi p k ell age))
    (fun F=>finiteResponse_tail cut F f g phi psi p k ell age frequency damping T positive future)

 theorem prepared_response_tail (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T)
    (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖SourceGraph.response (responseTail cut f g phi psi p k ell age frequency damping T positive future)
      left right lc ls rc rs u v‖ ≤
      legBound^2*(dampingTail damping T*fieldScale cut f g phi psi p k ell age)*‖u‖*‖v‖ := by
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (responseTail_bound cut f g phi psi p k ell age frequency damping T positive future) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

 def truncationFamily (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) : Operator Index H where
  component F:=finiteTruncation cut F f g phi psi p k ell age frequency damping T
  bounded:=⟨(dampingTail damping 0+dampingTail damping T)*fieldScale cut f g phi psi p k ell age,
    mul_nonneg (add_nonneg (dampingTail_nonneg damping 0 le_rfl) (dampingTail_nonneg damping T future))
      (fieldScale_nonneg cut f g phi psi p k ell age),fun F v=>by
    have bound : ‖finiteTruncation cut F f g phi psi p k ell age frequency damping T‖ ≤
        (dampingTail damping 0+dampingTail damping T)*fieldScale cut f g phi psi p k ell age := by
      have triangle:=norm_sub_le (finiteResponse cut F f g phi psi p k ell age frequency damping)
        (finiteResponse cut F f g phi psi p k ell age frequency damping-
          finiteTruncation cut F f g phi psi p k ell age frequency damping T)
      rw [sub_sub_cancel] at triangle
      exact triangle.trans ((add_le_add (finiteResponse_bound cut F f g phi psi p k ell age frequency damping positive)
        (finiteResponse_tail cut F f g phi psi p k ell age frequency damping T positive future)).trans_eq (by ring))
    exact ((finiteTruncation cut F f g phi psi p k ell age frequency damping T).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg v))⟩

 def truncation (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (truncationFamily cut f g phi psi p k ell age frequency damping T positive future)

 theorem response_sub_truncation (cut : ℕ) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    response cut f g phi psi p k ell age frequency damping positive-
      truncation cut f g phi psi p k ell age frequency damping T positive future=
        responseTail cut f g phi psi p k ell age frequency damping T positive future := by
  have same:=lift_congr sourceFilter
    (add (tailFamily cut f g phi psi p k ell age frequency damping T positive future)
      (truncationFamily cut f g phi psi p k ell age frequency damping T positive future))
    (responseFamily cut f g phi psi p k ell age frequency damping positive)
    (fun F=>by simp only [add,tailFamily,truncationFamily,responseFamily,sub_add_cancel])
  rw [lift_add] at same
  change responseTail cut f g phi psi p k ell age frequency damping T positive future+
    truncation cut f g phi psi p k ell age frequency damping T positive future=
      response cut f g phi psi p k ell age frequency damping positive at same
  exact sub_eq_iff_eq_add.mpr same.symm

 def preparedContact (cut : ℕ) (f g : Field289) (phi : Localizer) (p k ell : PhysicalMomentum)
    (t : ℝ) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) : ℂ :=
  SourceGraph.response (directContact cut f g phi p k ell t) left right lc ls rc rs u v

 theorem preparedContact_bound (cut : ℕ) (f g : Field289) (phi : Localizer) (p k ell : PhysicalMomentum)
    (t : ℝ) (left right : Bool) (lc ls rc rs : Fin 2) (u v : Profile) :
    ‖preparedContact cut f g phi p k ell t left right lc ls rc rs u v‖ ≤
      legBound^2*contactTimeBound cut f g phi p t*‖u‖*‖v‖ := by
  apply (SourceGraph.response_bound _ left right lc ls rc rs u v).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (directContact_bound cut f g phi p k ell t) (sq_nonneg _)) (norm_nonneg u)) (norm_nonneg v)

 theorem sharp_orderedField (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    star (orderedField cut F f g phi psi p k ell t s)=
      star (time (compression p F+cutoff cut) s)*star (localizedGauss g p psi)*
        star (time (compression (p+ell) F+cutoff cut) (t-s))*star (localizedGauss f (p+ell) phi)*
          star (time (compression (p+k+ell) F+cutoff cut) (-t)) := by
  simp only [orderedField,star_mul,mul_assoc]

 theorem sharp_kernel_bound (cut : ℕ) (F : Index) (f g : Field289) (phi psi : Localizer)
    (p k ell : PhysicalMomentum) (t s : ℝ) :
    ‖star (finiteKernel cut F f g phi psi p k ell t s)‖ ≤ kernelBound cut f g phi psi p k ell t s := by
  have sharpNorm (A : Op) : ‖star A‖=‖A‖ := ContinuousLinearMap.adjoint.norm_map A
  exact (sharpNorm _).le.trans (finiteKernel_bound cut F f g phi psi p k ell t s)

 open PreparationVacuumPreparedTail PreparationVacuumTailOperator PreparationVacuumNativeClosure
 open CanonicalPreparationCore.Completed CanonicalPreparationCreation
 open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation
 open SaturationMonoid.Quantum.Forms

set_option maxHeartbeats 1500000 in
 theorem actual_prepared_field_response (B0 : ℕ→Fin 5→(ℕ→ℝ))
    (nonnegative : ∀ k i n,0 ≤ B0 k i n) (inputs : PreparationVacuumTailSupport.UnitEnergyInputs B0 102)
    (epsilon : ℝ) (precision : 0<epsilon) :
    ∃ x : (BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
      (completeNativeRemainder B0 nonnegative inputs)).domain,
      let u:=zeroLocalizedProfile actualNativeLocalizer x.val
      ‖prepared u‖=1 ∧
      prepared u=sourceCreated (GaussHalfDensity.halfDensityEquiv 0 x.val.val) ∧
      ‖BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
          (completeNativeRemainder B0 nonnegative inputs) x-
        (BoundedRemainder.energy sourceClosedFactor sourceClosedFactor_closed
          (completeNativeRemainder B0 nonnegative inputs):ℂ) • x.val‖<epsilon ∧
      (∃ h : prepared u∈GaussRadialDomain.closedY.domain,
        ∀ n : ℕ,‖GaussRadialDomain.closedY ⟨prepared u,h⟩-cutoff n (prepared u)‖ ≤
          (915/916:ℝ)^(n+1)*916*GaussYukawaCoefficient.bound) ∧
      ∀ (cut : ℕ) (f g : Field289) (phi psi : Localizer) (p k ell : PhysicalMomentum) (t s : ℝ)
        (left right : Bool) (lc ls rc rs : Fin 2),
        ‖preparedCausal cut f g phi psi p k ell t s left right lc ls rc rs u u‖ ≤
          legBound^2*kernelBound cut f g phi psi p k ell t s*‖u‖*‖u‖ ∧
        ‖preparedContact cut f g (contactLocalizer phi psi) p k ell t left right lc ls rc rs u u‖ ≤
          legBound^2*contactTimeBound cut f g (contactLocalizer phi psi) p t*‖u‖*‖u‖ ∧
        ∀ (frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T),
          ‖SourceGraph.response (responseTail cut f g phi psi p k ell s frequency damping T positive future)
            left right lc ls rc rs u u‖ ≤
            legBound^2*(dampingTail damping T*fieldScale cut f g phi psi p k ell s)*‖u‖*‖u‖ := by
  obtain ⟨x,unit,near,created,domain⟩:=PreparationVacuumLocalizedYukawa.actual_full_tail_preparation_Y B0 nonnegative inputs epsilon precision
  exact ⟨x,unit,created,near,domain,fun cut f g phi psi p k ell t s left right lc ls rc rs=>
    ⟨preparedCausal_bound cut f g phi psi p k ell t s left right lc ls rc rs _ _,
      preparedContact_bound cut f g (contactLocalizer phi psi) p k ell t left right lc ls rc rs _ _,
      fun frequency damping T positive future=>prepared_response_tail cut f g phi psi p k ell s frequency damping T
        positive future left right lc ls rc rs _ _⟩⟩

end LowEnergy.PreparationVacuumCausalFieldResponse
