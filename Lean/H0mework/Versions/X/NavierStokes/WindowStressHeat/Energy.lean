import H0mework.NavierStokes.WindowStressHeat.Gram
import H0mework.Versions.X.NavierStokes.PhysicalTranslation.Field
import H0mework.Versions.X.NavierStokes.WindowSource.PairActionRows

set_option autoImplicit false
open scoped BigOperators ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStressHeatEnergy
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativePhysicalFourier NativePhysicalGradient
noncomputable section

theorem multiplier_star (wave : IntegerWavevector) (direction : Coordinate) :
    star (multiplier wave direction) = -multiplier wave direction := by
  simp [multiplier,complexWavevector]

theorem spectral_skew (direction : Coordinate) (first last firstJet lastJet : ScalarSequence)
    (firstActual : ∀ wave, firstJet wave = multiplier wave direction * first wave)
    (lastActual : ∀ wave, lastJet wave = multiplier wave direction * last wave) :
    inner ℂ first lastJet = -inner ℂ firstJet last := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,← tsum_neg]
  apply tsum_congr
  intro wave
  simp only [firstActual,lastActual,RCLike.inner_apply,starRingEnd_apply,star_mul,multiplier_star]
  ring

theorem spectral_green (direction : Coordinate) (value first second : ScalarSequence)
    (firstActual : ∀ wave, first wave = multiplier wave direction * value wave)
    (secondActual : ∀ wave, second wave = multiplier wave direction * first wave) :
    inner ℂ value second = -(‖first‖^2 : ℂ) := by
  rw [spectral_skew direction value first first second firstActual secondActual]
  rw [inner_self_eq_norm_sq_to_K]
  rfl

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def field (value : ScalarSequence) : ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm value

theorem field_fourier (value : ScalarSequence) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (field value) wave = value wave := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact congrArg (fun sequence : ScalarSequence => sequence wave)
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.apply_symm_apply value)

theorem field_hasDerivAt (direction : Coordinate) (value derivative : ScalarSequence)
    (actual : ∀ wave, derivative wave = multiplier wave direction * value wave) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate
      (NativePhysicalTranslation.displacement direction displacement) (field value)) (field derivative) 0 := by
  let inverse : ScalarSequence →L[ℝ] ScalarField :=
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have generated := inverse.hasFDerivAt.comp_hasDerivAt 0
    (NativeSpatialTranslation.translate_hasDerivAt_zero direction value derivative actual)
  simp only [NativePhysicalTranslation.translate_eq_fourier,field,LinearIsometryEquiv.apply_symm_apply]
  convert! generated using 1

theorem physical_green (direction : Coordinate) (value first second : ScalarSequence)
    (firstActual : ∀ wave, first wave = multiplier wave direction * value wave)
    (secondActual : ∀ wave, second wave = multiplier wave direction * first wave) :
    inner ℝ (field value) (field second) = -‖field first‖^2 := by
  have physical : inner ℂ (field value) (field second) = -(‖field first‖^2 : ℂ) := by
    rw [field,field,field,LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.norm_map]
    exact spectral_green direction value first second firstActual secondActual
  have realPart : inner ℝ (field value) (field second) = (inner ℂ (field value) (field second)).re := by
    rw [L2.inner_def,L2.inner_def]
    change (∫ point : Torus, RCLike.re (inner ℂ (field value point) (field second point))) =
      RCLike.re (∫ point : Torus, inner ℂ (field value point) (field second point))
    exact integral_re (L2.integrable_inner (field value) (field second))
  rw [realPart,physical,← Complex.ofReal_pow,Complex.neg_re,Complex.ofReal_re]

def finiteSequence (frequencies : Finset IntegerWavevector) (coefficients : IntegerWavevector → ℂ) : ScalarSequence :=
  ∑ wave ∈ frequencies, lp.single 2 wave (coefficients wave)

theorem finiteSequence_apply (frequencies : Finset IntegerWavevector) (coefficients : IntegerWavevector → ℂ)
    (wave : IntegerWavevector) :
    finiteSequence frequencies coefficients wave = if wave ∈ frequencies then coefficients wave else 0 := by
  change (lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave) (finiteSequence frequencies coefficients) = _
  rw [finiteSequence,map_sum]
  change (∑ other ∈ frequencies, lp.single 2 other (coefficients other) wave) = _
  simp [lp.single_apply]

def finiteJet (frequencies : Finset IntegerWavevector) (coefficients : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) : ScalarSequence :=
  finiteSequence frequencies (fun wave => multiplier wave direction^order * coefficients wave)

theorem finiteJet_successor (frequencies : Finset IntegerWavevector) (coefficients : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) (wave : IntegerWavevector) :
    finiteJet frequencies coefficients direction (order+1) wave =
      multiplier wave direction * finiteJet frequencies coefficients direction order wave := by
  simp only [finiteJet,finiteSequence_apply,pow_succ]
  split_ifs <;> ring

theorem finiteJet_hasDerivAt (frequencies : Finset IntegerWavevector) (coefficients : IntegerWavevector → ℂ)
    (direction : Coordinate) (order : ℕ) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate
      (NativePhysicalTranslation.displacement direction displacement)
        (field (finiteJet frequencies coefficients direction order)))
      (field (finiteJet frequencies coefficients direction (order+1))) 0 :=
  field_hasDerivAt direction _ _ (finiteJet_successor frequencies coefficients direction order)

theorem finite_green (frequencies : Finset IntegerWavevector) (coefficients : IntegerWavevector → ℂ)
    (direction : Coordinate) :
    inner ℝ (field (finiteJet frequencies coefficients direction 0))
      (field (finiteJet frequencies coefficients direction 2)) =
        -‖field (finiteJet frequencies coefficients direction 1)‖^2 :=
  physical_green direction _ _ _ (finiteJet_successor frequencies coefficients direction 0)
    (finiteJet_successor frequencies coefficients direction 1)

theorem pair_heat (viscosity : ℝ) (first last : IntegerWavevector) (left right : ℂ) :
    (-(viscosity*(2*Real.pi)^2*(integerWaveNormSq first+integerWaveNormSq last)) : ℂ)*(-left*right) =
      (-(viscosity*(2*Real.pi)^2*integerWaveNormSq (first+last)) : ℂ)*(-left*right)+
        2*(viscosity : ℂ)*∑ direction : Coordinate,
          (multiplier first direction*left)*(multiplier last direction*right) := by
  simp only [integerWaveNormSq,Fin.sum_univ_three,Pi.add_apply,Int.cast_add,multiplier,complexWavevector]
  push_cast
  simp only [mul_add]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem tensor_green (frequencies : Finset IntegerWavevector)
    (coefficients : IntegerWavevector → Coordinate → Coordinate → ℂ) :
    (∑ output : Coordinate, ∑ input : Coordinate, inner ℝ
      (field (finiteSequence frequencies (fun wave => coefficients wave output input)))
      (∑ direction : Coordinate, field (finiteJet frequencies (fun wave => coefficients wave output input) direction 2))) =
      -(∑ direction : Coordinate, ∑ output : Coordinate, ∑ input : Coordinate,
        ‖field (finiteJet frequencies (fun wave => coefficients wave output input) direction 1)‖^2) := by
  have base (output input direction : Coordinate) : finiteSequence frequencies (fun wave => coefficients wave output input) =
      finiteJet frequencies (fun wave => coefficients wave output input) direction 0 := by
    simp only [finiteJet,pow_zero,one_mul]
  have paired (output input direction : Coordinate) : inner ℝ
      (field (finiteSequence frequencies (fun wave => coefficients wave output input)))
      (field (finiteJet frequencies (fun wave => coefficients wave output input) direction 2)) =
        -‖field (finiteJet frequencies (fun wave => coefficients wave output input) direction 1)‖^2 := by
    rw [base output input direction]
    exact finite_green frequencies (fun wave => coefficients wave output input) direction
  simp only [inner_sum]
  simp_rw [paired]
  simp only [Finset.sum_neg_distrib]
  apply congrArg (fun value : ℝ => -value)
  calc
    _ = ∑ output : Coordinate, ∑ direction : Coordinate, ∑ input : Coordinate,
        ‖field (finiteJet frequencies (fun wave => coefficients wave output input) direction 1)‖^2 :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem tensor_heat_pairing (viscosity : ℝ) (frequencies : Finset IntegerWavevector)
    (coefficients : IntegerWavevector → Coordinate → Coordinate → ℂ)
    (diffusion : Coordinate → Coordinate → ScalarField) :
    (∑ output : Coordinate, ∑ input : Coordinate, inner ℝ
      (-field (finiteSequence frequencies (fun wave => coefficients wave output input)))
      (-viscosity • (∑ direction : Coordinate,
        field (finiteJet frequencies (fun wave => coefficients wave output input) direction 2))+
          (2*viscosity) • diffusion output input)) =
      -viscosity*(∑ direction : Coordinate, ∑ output : Coordinate, ∑ input : Coordinate,
        ‖field (finiteJet frequencies (fun wave => coefficients wave output input) direction 1)‖^2)-
      2*viscosity*(∑ output : Coordinate, ∑ input : Coordinate,
        inner ℝ (field (finiteSequence frequencies (fun wave => coefficients wave output input))) (diffusion output input)) := by
  simp only [inner_add_right,real_inner_smul_right,inner_neg_left,neg_mul,neg_neg,Finset.sum_add_distrib,
    Finset.mul_sum]
  have green := congrArg (fun value : ℝ => viscosity*value) (tensor_green frequencies coefficients)
  simp only [Finset.mul_sum,mul_neg] at green
  rw [green]
  simp only [Finset.sum_neg_distrib,sub_eq_add_neg]

open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTriadRows NativeWindowPairActionRows
variable {nu : Viscosity}

def diffusionPair (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : ℂ :=
  ∑ direction : Coordinate, (multiplier first direction*velocity seed time first input)*
    (multiplier last direction*velocity seed time last output)

theorem driver_diffusion (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) :
    driver seed first last output input time =
      -(action seed time first input*velocity seed time last output+
        velocity seed time first input*action seed time last output)-
      (nu.coeff*(2*Real.pi)^2*integerWaveNormSq (first+last)) • row seed first last output input time+
        (2*nu.coeff) • diffusionPair seed first last output input time := by
  rw [driver_original]
  have original := pair_heat nu.coeff first last (velocity seed time first input) (velocity seed time last output)
  rw [row_original]
  simp only [NativeUnheatedStressPairEvolution.decay,integerWaveViscousMultiplier,Complex.real_smul,
    Complex.ofReal_mul,Complex.ofReal_ofNat,sub_eq_add_neg,neg_mul,mul_neg,← mul_assoc,diffusionPair] at original ⊢
  push_cast at original ⊢
  linear_combination original

end
end SaturationMonoid.NavierStokes.NativeWindowStressHeatEnergy
