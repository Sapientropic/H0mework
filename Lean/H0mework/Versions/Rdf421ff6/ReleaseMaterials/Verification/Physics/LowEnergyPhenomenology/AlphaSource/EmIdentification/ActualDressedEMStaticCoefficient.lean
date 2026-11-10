import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMTensorSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTensorClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients LowEnergy.GaussComposite.ActualDressedVisiblePole
open LowEnergy.ActualDressedVisiblePole ActualDressedPhysicalRayNumerator
open Filter Set
open scoped Matrix Topology
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

def staticScaleSlice (sigma : ℝ) : Parameters →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 3 => if i=0 then Polynomial.X else if i=1 then Polynomial.C (sigma : ℂ) else 0)

theorem static_scale_eval (sigma eps : ℝ) (P : Parameters) :
    (staticScaleSlice sigma P).eval (eps : ℂ)=MvPolynomial.eval (irValues eps sigma 0) P := by
  have hom : (Polynomial.evalRingHom (eps : ℂ)).comp (staticScaleSlice sigma)=
      MvPolynomial.eval (irValues eps sigma 0) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [staticScaleSlice]
    · intro i
      simp [staticScaleSlice, irValues]
      split_ifs <;> simp_all
  exact congrArg (fun f : Parameters →+* ℂ => f P) hom

def staticEMDeterminant (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  staticScaleSlice sigma (commonDeterminant event n)

def staticEMNumerator (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] := (commonEMTensorNumerator event n).map (staticScaleSlice sigma)

def staticEMFraction (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) (RatFunc ℂ) :=
  fun mu nu => readFraction (staticEMNumerator event sigma n mu nu) (staticEMDeterminant event sigma n)

def staticEntryCoefficient (R : RatFunc ℂ) : ℂ :=
  if poleOrder R 0=4 then leadingPoleCoefficient R 0 else 0

def sourceStaticEMCoefficient (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ := fun mu nu => staticEntryCoefficient (staticEMFraction event sigma n mu nu)

/-- Both clearings act on the identical original pencil; its physical denominator is generated nonzero. -/
theorem actual_common_chart_original (event : DressedEvent) (eps sigma s : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma)
    (commonRegular : MvPolynomial.eval (irValues eps sigma s) (commonDeterminant event n)≠0) :
    correctedDet event eps s sigma n≠0 := by
  have relation := actual_common_signed_determinant_relation event eps sigma s n positive
  have denominator := physical_ray_denominator_nonzero event eps s sigma n positive
  intro zero
  rw [zero, mul_zero] at relation
  exact mul_ne_zero (pow_ne_zero 289 denominator) commonRegular relation.symm

private theorem real_punctured_complex :
    Tendsto (fun eps : ℝ => (eps : ℂ)) (nhdsWithin 0 ({0}ᶜ)) (nhdsWithin 0 ({0}ᶜ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with eps different
  simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero] using different

/-- A nonzero original scale polynomial generates its own punctured chart, even when its zero-scale value vanishes. -/
theorem source_static_punctured_chart (D : ℂ[X]) (nonzero : D≠0) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ), D.eval (eps : ℂ)≠0 := by
  let Q := D /ₘ (X-C 0)^D.rootMultiplicity 0
  have remainder : Q.eval 0≠0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 0 nonzero
  have continuous : Continuous (fun eps : ℝ => Q.eval (eps : ℂ)) := by fun_prop
  have near : ∀ᶠ eps : ℝ in 𝓝 0, Q.eval (eps : ℂ)≠0 := continuous.continuousAt.eventually_ne remainder
  filter_upwards [near.filter_mono inf_le_left, self_mem_nhdsWithin] with eps regular different
  have ep : (eps : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by
    simpa only [mem_compl_iff, mem_singleton_iff] using different)
  have factor := congrArg (Polynomial.eval (eps : ℂ)) (pow_mul_divByMonic_rootMultiplicity_eq D 0)
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero] at factor
  rw [← factor]
  exact mul_ne_zero (pow_ne_zero _ ep) regular

private theorem weighted_static_limit (R : RatFunc ℂ) (bounded : poleOrder R 0≤4) :
    Tendsto (fun eps : ℝ => (eps : ℂ)^4*(R.num.eval (eps : ℂ)/R.denom.eval (eps : ℂ)))
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (staticEntryCoefficient R)) := by
  have base := (pole_order_limit R 0).comp real_punctured_complex
  simp only [Function.comp_def, sub_zero] at base
  by_cases exactOrder : poleOrder R 0=4
  · simpa only [staticEntryCoefficient, exactOrder, if_true] using base
  · have lower : poleOrder R 0<4 := lt_of_le_of_ne bounded exactOrder
    have positive : 0<4-poleOrder R 0 := Nat.sub_pos_of_lt lower
    have extra := (Complex.continuous_ofReal.continuousAt.tendsto.pow (4-poleOrder R 0)).mono_left
      (show nhdsWithin (0 : ℝ) ({0}ᶜ)≤𝓝 0 from inf_le_left)
    have zeroLimit : Tendsto (fun eps : ℝ => (eps : ℂ)^(4-poleOrder R 0))
        (nhdsWithin 0 ({0}ᶜ)) (𝓝 0) := by
      simpa only [Complex.ofReal_zero, zero_pow positive.ne'] using extra
    have combined := zeroLimit.mul base
    simp only [zero_mul] at combined
    rw [staticEntryCoefficient, if_neg exactOrder]
    convert combined using 1
    funext eps
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel bounded]

private theorem actual_static_fraction (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (chart : (staticEMDeterminant event sigma n).eval (eps : ℂ)≠0)
    (mu nu : Fin 4) :
    correctedEMTensor event eps 0 sigma n mu nu=
      (staticEMFraction event sigma n mu nu).num.eval (eps : ℂ)/
        (staticEMFraction event sigma n mu nu).denom.eval (eps : ℂ) := by
  have commonRegular : MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n)≠0 := by
    rw [← static_scale_eval]
    exact chart
  have regular := actual_common_chart_original event eps sigma 0 n positive commonRegular
  have read := congrFun (congrFun (actual_corrected_em_tensor_clear event eps sigma 0 n positive regular) mu) nu
  have raw : correctedEMTensor event eps 0 sigma n mu nu=
      MvPolynomial.eval (irValues eps sigma 0) (commonEMTensorNumerator event n mu nu)/
        MvPolynomial.eval (irValues eps sigma 0) (commonDeterminant event n) := by
    apply (eq_div_iff commonRegular).mpr
    exact (mul_comm _ _).trans read
  refine raw.trans ?_
  rw [← static_scale_eval, ← static_scale_eval]
  exact (reduced_read_at_regular _ _ (eps : ℂ) chart).symm

/-- The generated scale chart is directly consumed by the unchanged actual corrected full response. -/
theorem actual_static_em_coefficient (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum)
    (positive : 0<sigma) (nonzero : staticEMDeterminant event sigma n≠0)
    (bounded : ∀mu nu, poleOrder (staticEMFraction event sigma n mu nu) 0≤4) :
    Tendsto (fun eps : ℝ => (eps : ℂ)^4 • correctedEMTensor event eps 0 sigma n)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceStaticEMCoefficient event sigma n)) := by
  apply tendsto_pi_nhds.2
  intro mu
  apply tendsto_pi_nhds.2
  intro nu
  apply Tendsto.congr' _ (weighted_static_limit _ (bounded mu nu))
  filter_upwards [source_static_punctured_chart _ nonzero] with eps chart
  exact congrArg (fun z : ℂ => (eps : ℂ)^4*z) (actual_static_fraction event eps sigma n positive chart mu nu).symm

/-- Every source object returns its own static branch. A higher pole is preserved as a higher pole, never reported as a finite coefficient. -/
inductive StaticEMReturn (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum) : Type
  | singular (determinant_zero : staticEMDeterminant event sigma n=0)
  | higher (determinant_nonzero : staticEMDeterminant event sigma n≠0)
      (higher_order : ∃mu nu, 4<poleOrder (staticEMFraction event sigma n mu nu) 0)
  | finite (determinant_nonzero : staticEMDeterminant event sigma n≠0)
      (orders : ∀mu nu, poleOrder (staticEMFraction event sigma n mu nu) 0≤4)
      (actual_return : Tendsto (fun eps : ℝ => (eps : ℂ)^4 • correctedEMTensor event eps 0 sigma n)
        (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceStaticEMCoefficient event sigma n)))

def sourceStaticEMReturn (event : DressedEvent) (sigma : ℝ) (n : PhysicalMomentum) (positive : 0<sigma) :
    StaticEMReturn event sigma n := by
  classical
  by_cases zero : staticEMDeterminant event sigma n=0
  · exact .singular zero
  · by_cases bounded : ∀mu nu, poleOrder (staticEMFraction event sigma n mu nu) 0≤4
    · exact .finite zero bounded (actual_static_em_coefficient event sigma n positive zero bounded)
    · push Not at bounded
      exact .higher zero bounded

end LowEnergy.GaussComposite.ActualDressedEMTensorClock
