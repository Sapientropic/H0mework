import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceExactSchurScale

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedControl
open PreparationVacuumFullOriginResponse PreparationVacuumPhysicalCharacteristic CanonicalGradedSpatialSource
open Filter Set
open scoped Matrix BigOperators Topology Matrix.Norms.Operator ContDiff

@[fun_prop] private theorem ofReal_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(x:ℂ)):=Complex.ofRealCLM.contDiff

private theorem sourceMatrix_smooth (terms : List SourceTerm) : ContDiff ℝ ∞ (sourceMatrix terms):=by
  induction terms with
  | nil=>exact contDiff_const
  | cons a rest ih=>
    have scalar : ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>coefficientValue a.coefficient*a.powers.value p):=by
      unfold Powers.value
      fun_prop
    have term : ContDiff ℝ ∞ a.matrix:=by
      have result:=scalar.smul (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 4→ℂ=>Matrix.single a.row a.column (1:ℂ)))
      change ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>(coefficientValue a.coefficient*a.powers.value p) • Matrix.single a.row a.column (1:ℂ)) at result
      change ContDiff ℝ ∞ (fun p : Fin 4→ℂ=>Matrix.single a.row a.column (coefficientValue a.coefficient*a.powers.value p))
      simpa only [Matrix.smul_single,smul_eq_mul,mul_one] using result
    exact term.add ih

private theorem complementKernel_smooth : ContDiff ℝ ∞ complementKernel:=by
  unfold complementKernel activeKernel
  exact ((contDiff_const.mul (sourceMatrix_smooth activeTerms)).mul contDiff_const).add contDiff_const

/-- The source origin inverse makes the complete complement Green smooth there. -/
theorem unrestrictedGreen_smooth_origin : ContDiffAt ℝ ∞ unrestrictedGreen (0:Fin 4→ℂ):=by
  have unit : IsUnit (complementKernel 0):=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr origin_determinant)
  obtain ⟨u,hu⟩:=unit
  have inverse : ContDiffAt ℝ ∞ (fun p : Fin 4→ℂ=>(complementKernel p)⁻¹) 0:=by
    have smooth:=contDiffAt_ringInverse ℝ u (n:=∞)
    rw [hu] at smooth
    simpa only [Function.comp_def,Matrix.nonsing_inv_eq_ringInverse] using
      smooth.comp (0:Fin 4→ℂ) complementKernel_smooth.contDiffAt
  exact (contDiffAt_const.mul inverse).mul contDiffAt_const

private theorem matrix_smooth {d : ℕ} (f : ℝ×ℝ→Matrix (Fin d) (Fin d) ℂ)
    (entries : ∀i j,ContDiff ℝ ∞ (fun x=>f x i j)) : ContDiff ℝ ∞ f:=by
  have representation : f=(fun x=>∑i : Fin d,∑j : Fin d,f x i j • Matrix.single i j (1:ℂ)):=by
    funext x
    simp only [Matrix.smul_single,smul_eq_mul,mul_one]
    exact Matrix.matrix_eq_sum_single _
  rw [representation]
  exact ContDiff.sum (fun i _=>ContDiff.sum (fun j _=>(entries i j).smul contDiff_const))

private theorem physicalMomentum_smooth (n : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun x : ℝ×ℝ=>physicalFrequencyMomentum x.2 n):=by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change ContDiff ℝ ∞ (fun x : ℝ×ℝ=> -Complex.I*(x.2:ℂ))
    fun_prop
  · exact contDiff_const

private theorem frequencyRay_smooth (n : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun x : ℝ×ℝ=>frequencyRay x.1 x.2 n):=by
  simp_rw [frequencyRay_scaled]
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : ℝ×ℝ=>(x.1:ℂ)^2)).smul (physicalMomentum_smooth n)

private theorem characteristic_smooth (n : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun x : ℝ×ℝ=>characteristicTensor x.2 n):=by
  apply matrix_smooth
  intro i j
  fin_cases i <;> fin_cases j <;> simp [characteristicTensor,Fin.ext_iff] <;> fun_prop

private theorem mix_smooth (n : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun x : ℝ×ℝ=>characteristicMix x.2 n):=by
  apply matrix_smooth
  intro i j
  simp only [characteristicMix,Matrix.add_apply,Matrix.single_apply]
  split_ifs <;> fun_prop

private theorem fast_smooth (n : PhysicalMomentum) :
    ContDiff ℝ ∞ (fun x : ℝ×ℝ=>characteristicFast x.2 n):=by
  apply matrix_smooth
  intro i j
  simp only [characteristicFast,Matrix.add_apply,Matrix.single_apply]
  split_ifs <;> fun_prop

private theorem regularScaling_smooth : ContDiff ℝ ∞ (fun x : ℝ×ℝ=>regularScaling x.1):=by
  apply matrix_smooth
  intro i j
  simp only [regularScaling,Matrix.diagonal_apply]
  split_ifs <;> fun_prop

private def fiveRead : Matrix (Fin 289) (Fin 289) ℂ→L[ℝ] Matrix (Fin 5) (Fin 5) ℂ:=
  LinearMap.toContinuousLinearMap
    { toFun:=fun M=>M.submatrix fiveIndex fiveIndex
      map_add':=fun _ _=>rfl
      map_smul':=fun _ _=>rfl }

private theorem rayRemainder_smooth (s : ℝ) (n : PhysicalMomentum) :
    ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>rayRemainder x.1 x.2 n) (0,s):=by
  have p:=physicalMomentum_smooth n
  have z : ContDiff ℝ ∞ (fun x : ℝ×ℝ=>(x.1:ℂ)^2):=by fun_prop
  have variation : ContDiff ℝ ∞ (fun x : ℝ×ℝ=>nativeVariation ((x.1:ℂ)^2) (physicalFrequencyMomentum x.2 n)):=
    ((sourceMatrix_smooth (degreeTerms (positiveTerms activeTerms) 1)).comp p).add
      (z.smul ((sourceMatrix_smooth (degreeTerms (positiveTerms activeTerms) 2)).comp p))
  have higher : ContDiff ℝ ∞ (fun x : ℝ×ℝ=>nativeHigher ((x.1:ℂ)^2) (physicalFrequencyMomentum x.2 n)):=
    ((sourceMatrix_smooth (degreeTerms fullHigherTerms 3)).comp p).add
      (z.smul ((sourceMatrix_smooth (degreeTerms fullHigherTerms 4)).comp p))
  have origin : frequencyRay 0 s n=0:=by rw [frequencyRay_scaled];simp
  have green : ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>unrestrictedGreen (frequencyRay x.1 x.2 n)) (0,s):=by
    have smooth : ContDiffAt ℝ ∞ unrestrictedGreen (frequencyRay 0 s n):=by
      rw [origin];exact unrestrictedGreen_smooth_origin
    exact smooth.comp (0,s) (frequencyRay_smooth n).contDiffAt
  exact higher.contDiffAt.add ((((((contDiffAt_const.mul variation.contDiffAt).mul green).mul
    variation.contDiffAt).mul contDiffAt_const).mul variation.contDiffAt).mul contDiffAt_const)

/-- Full source Schur continuation is jointly smooth in source scale and physical frequency. -/
theorem extendedTensor_smooth (s : ℝ) (n : PhysicalMomentum) :
    ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>extendedTensor x.1 x.2 n) (0,s):=by
  have remainder : ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>(slowFastFrame.transpose*rayRemainder x.1 x.2 n*slowFastFrame).submatrix fiveIndex fiveIndex) (0,s):=fiveRead.contDiff.contDiffAt.comp (0,s)
    ((contDiffAt_const.mul (rayRemainder_smooth s n)).mul contDiffAt_const)
  have scaled : ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>scaledRemainder x.1 x.2 n) (0,s):=
    ((regularScaling_smooth.contDiffAt).mul remainder).mul regularScaling_smooth.contDiffAt
  have e : ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>(x.1:ℂ)) (0,s):=by fun_prop
  exact (((characteristic_smooth n).contDiffAt.add (e.smul (mix_smooth n).contDiffAt)).add
    ((e.pow 2).smul (fast_smooth n).contDiffAt)).add ((e.pow 2).smul scaled)

private theorem determinant_smooth : ContDiff ℝ ∞ (fun M : Matrix (Fin 5) (Fin 5) ℂ=>M.det):=by
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro sigma _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (Matrix.entryLinearMap ℝ ℂ (sigma i) i).toContinuousLinearMap.contDiff

def physicalDeterminant (epsilon s : ℝ) (n : PhysicalMomentum) : ℝ:=(extendedTensor epsilon s n).det.re

theorem physicalDeterminant_origin (s : ℝ) (n : PhysicalMomentum) :
    physicalDeterminant 0 s n=characteristicDeterminant s n:=by
  rw [physicalDeterminant,extendedTensor_origin,characteristic_det_real,Complex.ofReal_re]

theorem physicalDeterminant_smooth (s : ℝ) (n : PhysicalMomentum) :
    ContDiffAt ℝ ∞ (fun x : ℝ×ℝ=>physicalDeterminant x.1 x.2 n) (0,s):=
  Complex.reCLM.contDiff.contDiffAt.comp (0,s)
    (determinant_smooth.contDiffAt.comp (0,s) (extendedTensor_smooth s n))

/-- Frequency derivative of the complete five-channel source determinant. -/
def physicalSlope (epsilon s : ℝ) (n : PhysicalMomentum) : ℝ:=
  fderiv ℝ (fun x : ℝ×ℝ=>physicalDeterminant x.1 x.2 n) (epsilon,s) (0,1)

theorem physicalSlope_continuous_origin (s : ℝ) (n : PhysicalMomentum) :
    ContinuousAt (fun x : ℝ×ℝ=>physicalSlope x.1 x.2 n) (0,s):=
  ((physicalDeterminant_smooth s n).continuousAt_fderiv (by simp)).clm_apply continuousAt_const

theorem physicalDeterminant_derivative_near (s : ℝ) (n : PhysicalMomentum) :
    ∀ᶠ x : ℝ×ℝ in 𝓝 (0,s),HasDerivAt (fun t=>physicalDeterminant x.1 t n)
      (physicalSlope x.1 x.2 n) x.2:=by
  have smooth : ContDiffAt ℝ 1 (fun x : ℝ×ℝ=>physicalDeterminant x.1 x.2 n) (0,s):=
    (physicalDeterminant_smooth s n).of_le (by simp)
  filter_upwards [smooth.eventually (by simp)] with x hx
  exact hx.differentiableAt_one.hasFDerivAt.comp_hasDerivAt x.2
    ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))

theorem physicalSlope_origin (s : ℝ) (n : PhysicalMomentum) :
    physicalSlope 0 s n=deriv (fun t=>characteristicDeterminant t n) s:=by
  have derivative : HasDerivAt (fun t=>physicalDeterminant 0 t n) (physicalSlope 0 s n) s:=
    ((physicalDeterminant_smooth s n).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s (0:ℝ)).prodMk (hasDerivAt_id s))
  simpa only [physicalDeterminant_origin] using derivative.deriv.symm

end LowEnergy.PreparationVacuumPhysicalPoleSheet
