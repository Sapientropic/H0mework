import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedZeroClockFrequencyOwn.ActualDressedZeroClockFrequencyReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroClockFrequency
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedZeroDamping ActualDressedOrderedStatic
open ActualCompositeFieldCurrent Filter Set
open scoped Topology BigOperators
open scoped Matrix
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

private theorem specialized_clock_pole (N D : (ℂ[X])[X]) (m j : ℕ) (less : j < m)
    (dFactor : X^m∣D) (eps : ℝ) (dRegular : (D.coeff m).eval (eps : ℂ)≠0)
    (nRegular : (N.coeff j).eval (eps : ℂ)≠0) :
    0<poleOrder (readFraction (clockSpecialize eps N) (clockSpecialize eps D)) 0 := by
  let Ne := clockSpecialize eps N
  let De := clockSpecialize eps D
  let R := readFraction Ne De
  have nCoefficient : Ne.coeff j≠0 := by simpa only [Ne,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using nRegular
  have dCoefficient : De.coeff m≠0 := by simpa only [De,clockSpecialize,coe_mapRingHom,coeff_map,coe_evalRingHom] using dRegular
  have nNonzero : Ne≠0 := fun zero => nCoefficient (by rw [zero,coeff_zero])
  have dNonzero : De≠0 := fun zero => dCoefficient (by rw [zero,coeff_zero])
  have mappedFactor : X^m∣De := by
    have mapped := (_root_.map_dvd (clockSpecialize eps)) dFactor
    simpa only [De,map_pow,clockSpecialize,coe_mapRingHom,Polynomial.map_X] using mapped
  have dOrder : m≤De.rootMultiplicity 0 := by
    apply (le_rootMultiplicity_iff dNonzero).mpr
    simpa only [map_zero,sub_zero] using mappedFactor
  have nOrder : Ne.rootMultiplicity 0≤j := by
    rw [rootMultiplicity_eq_natTrailingDegree']
    exact natTrailingDegree_le_of_ne_zero nCoefficient
  by_contra positive
  have zeroOrder : R.denom.rootMultiplicity 0=0 := Nat.eq_zero_of_not_pos positive
  have cross := reduced_cross_identity Ne De dNonzero
  have rightNonzero : Ne*R.denom≠0 := mul_ne_zero nNonzero (RatFunc.denom_ne_zero R)
  have leftNonzero : R.num*De≠0 := by rw [cross]; exact rightNonzero
  have lower := le_rootMultiplicity_mul 0 leftNonzero
  have same : (R.num*De).rootMultiplicity 0=Ne.rootMultiplicity 0 := by
    rw [cross,rootMultiplicity_mul rightNonzero,zeroOrder,add_zero]
  rw [same] at lower
  omega

private theorem source_clock_pole (N D : (ℂ[X])[X]) (m : ℕ) (dFactor : X^m∣D)
    (dNonzero : D.coeff m≠0) (failure : ¬X^m∣N) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 ({0}ᶜ),
      0<poleOrder (readFraction (clockSpecialize eps N) (clockSpecialize eps D)) 0 := by
  have coefficient : ¬∀ j < m, N.coeff j=0 := fun zero => failure (X_pow_dvd_iff.mpr zero)
  push Not at coefficient
  obtain ⟨j,less,nonzero⟩ := coefficient
  filter_upwards [source_static_punctured_chart _ dNonzero,source_static_punctured_chart _ nonzero] with eps dRegular nRegular
  exact specialized_clock_pole N D m j less dFactor eps dRegular nRegular

theorem source_frequency_clock_responsibility (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (nonzero : frequencyClockDeterminant event eps n≠0)
    (failure : ¬FrequencyClockFinite event eps n pd ps dL dR sL sR) :
    ∀ᶠ s : ℝ in nhdsWithin 0 ({0}ᶜ),
      (∃mu nu, 0<poleOrder (readFraction
        (clockSpecialize s (frequencyClockEMNumerator event eps n mu nu))
        (clockSpecialize s (frequencyClockDeterminant event eps n))) 0) ∨
      0<poleOrder (readFraction
        (clockSpecialize s (frequencyClockProbeNumerator event eps n pd ps dL dR sL sR))
        (clockSpecialize s (frequencyClockDeterminant event eps n))) 0 := by
  classical
  by_cases emFactors : ∀mu nu, X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu
  · have probeFailure : ¬X^frequencyClockOrder event eps n∣frequencyClockProbeNumerator event eps n pd ps dL dR sL sR :=
      fun factor => failure ⟨emFactors,factor⟩
    exact (source_clock_pole _ _ (frequencyClockOrder event eps n) (source_frequency_clock_factor event eps n)
      (source_frequency_denominator_nonzero event eps n nonzero) probeFailure).mono (fun _ pole => Or.inr pole)
  · push Not at emFactors
    obtain ⟨mu,nu,factorFailure⟩ := emFactors
    exact (source_clock_pole _ _ (frequencyClockOrder event eps n) (source_frequency_clock_factor event eps n)
      (source_frequency_denominator_nonzero event eps n nonzero) factorFailure).mono
        (fun _ pole => Or.inl ⟨mu,nu,pole⟩)

/-- This consumes the actual zero-clock return before exposing any frequency principal. -/
theorem actual_zero_clock_frequency_principal (event : DressedEvent) (eps omega : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (chart : (zeroClockFrequencyDenominator event eps n).eval ((omega/eps^2 : ℝ) : ℂ)≠0)
    (factor : X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu))
    (away : (omega : ℂ)≠physicalFrequencyPole eps a)
    (regular : (rootRemainder (zeroClockFrequencyEMFraction event eps n mu nu) a).eval
      ((omega/eps^2 : ℝ) : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => correctedEMTensor event eps (omega/eps^2) sigma n mu nu)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 ((∑k ∈ Finset.range (poleOrder (zeroClockFrequencyEMFraction event eps n mu nu) a),
        clockPrincipalCoefficient (zeroClockFrequencyEMFraction event eps n mu nu) a (eps^2 : ℂ) k*
          ((omega : ℂ)-physicalFrequencyPole eps a)^k/
            ((omega : ℂ)-physicalFrequencyPole eps a)^poleOrder (zeroClockFrequencyEMFraction event eps n mu nu) a)+
        (analyticNumerator (zeroClockFrequencyEMFraction event eps n mu nu) a).eval ((omega/eps^2 : ℝ) : ℂ)/
          (rootRemainder (zeroClockFrequencyEMFraction event eps n mu nu) a).eval ((omega/eps^2 : ℝ) : ℂ))) := by
  have actual := actual_zero_clock_frequency_em_entry event eps (omega/eps^2) n mu nu chart factor
  have full := source_affine_principal_return (zeroClockFrequencyEMFraction event eps n mu nu)
    a (eps^2 : ℂ) 0 (omega : ℂ) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr nonzero)) root
    (by simpa only [physicalFrequencyPole,zero_add,Complex.ofReal_pow] using away)
    (by simpa only [sub_zero,Complex.ofReal_div,Complex.ofReal_pow] using regular)
  simp only [sub_zero,zero_add] at full
  change Tendsto _ _ (𝓝 ((zeroClockFrequencyEMFraction event eps n mu nu).num.eval ((omega/eps^2 : ℝ) : ℂ)/
    (zeroClockFrequencyEMFraction event eps n mu nu).denom.eval ((omega/eps^2 : ℝ) : ℂ))) at actual
  rw [Complex.ofReal_div,Complex.ofReal_pow,full] at actual
  simpa only [physicalFrequencyPole,Complex.ofReal_div,Complex.ofReal_pow] using actual

/-- Simple, repeated, nonreal and zero roots remain source-generated alternatives. -/
inductive FrequencyPoleKind (R : RatFunc ℂ) (a : ℂ) : Type
  | nonreal (imaginary : a.im≠0)
  | zero (stationary : a=0)
  | simpleReal (real : a.im=0) (moving : a≠0) (simple : poleOrder R a=1)
  | repeatedReal (real : a.im=0) (moving : a≠0) (repeated : poleOrder R a≠1)

def sourceFrequencyPoleKind (R : RatFunc ℂ) (a : ℂ) : FrequencyPoleKind R a := by
  classical
  exact if real : a.im=0 then
    if stationary : a=0 then .zero stationary else
      if simple : poleOrder R a=1 then .simpleReal real stationary simple else .repeatedReal real stationary simple
    else .nonreal real

structure FrequencyPrincipal (eps : ℝ) (R : RatFunc ℂ) (a : ℂ) where
  canonical : a∈visibleRoots R
  order : ℕ
  order_generated : order=poleOrder R a
  positive : 0<order
  frequency : ℂ
  frequency_generated : frequency=physicalFrequencyPole eps a
  coefficients : List ℂ
  coefficients_generated : coefficients=List.ofFn (fun k : Fin (poleOrder R a) =>
    clockPrincipalCoefficient R a (eps^2 : ℂ) k.val)
  residue : ℂ
  residue_generated : residue=clockResidue R a (eps^2 : ℂ)
  kind : FrequencyPoleKind R a

def sourceFrequencyPrincipal (eps : ℝ) (R : RatFunc ℂ)
    (a : {a : ℂ // a∈visibleRoots R}) : FrequencyPrincipal eps R a.val :=
  ⟨a.property,poleOrder R a.val,rfl,visible_pole_order_positive R a.val a.property,
    physicalFrequencyPole eps a.val,rfl,
    List.ofFn (fun k : Fin (poleOrder R a.val) => clockPrincipalCoefficient R a.val (eps^2 : ℂ) k.val),rfl,
    clockResidue R a.val (eps^2 : ℂ),rfl,sourceFrequencyPoleKind R a.val⟩

def sourceFrequencyPrincipals (eps : ℝ) (R : RatFunc ℂ) :
    Multiset (Σa : ℂ, FrequencyPrincipal eps R a) :=
  (visibleRoots R).attach.map (fun a => ⟨a.val,sourceFrequencyPrincipal eps R a⟩)

/-- All sixteen original EM observations and the complete independent electron current remain separate. -/
def sourceZeroClockFrequencyPrincipals (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    Option ((∀mu nu : Fin 4, Multiset (Σa : ℂ, FrequencyPrincipal eps
      (zeroClockFrequencyEMFraction event eps n mu nu) a)) ×
      Multiset (Σa : ℂ, FrequencyPrincipal eps (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR) a)) := by
  classical
  exact if frequencyClockDeterminant event eps n=0 ∨ ¬FrequencyClockFinite event eps n pd ps dL dR sL sR then none else
    some ⟨fun mu nu => sourceFrequencyPrincipals eps (zeroClockFrequencyEMFraction event eps n mu nu),
      sourceFrequencyPrincipals eps (zeroClockFrequencyProbeFraction event eps n pd ps dL dR sL sR)⟩

inductive FrequencyClockReturn (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : Type
  | singular (zero : frequencyClockDeterminant event eps n=0)
  | clockResponsibility (nonzero : frequencyClockDeterminant event eps n≠0)
      (failure : ¬FrequencyClockFinite event eps n pd ps dL dR sL sR)
  | finite (nonzero : frequencyClockDeterminant event eps n≠0)
      (factors : FrequencyClockFinite event eps n pd ps dL dR sL sR)
      (tensor_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => correctedEMTensor event eps s sigma n) (nhdsWithin 0 (Ioi 0))
          (𝓝 (zeroClockFrequencyEMRead event eps s n)))
      (probe_return : ∀s : ℝ, (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0 →
        Tendsto (fun sigma : ℝ => correctedProbeRead event eps s sigma n pd ps dL dR sL sR)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyProbeRead event eps s n pd ps dL dR sL sR)))

def sourceFrequencyClockReturn (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    FrequencyClockReturn event eps n pd ps dL dR sL sR := by
  classical
  by_cases zero : frequencyClockDeterminant event eps n=0
  · exact .singular zero
  · by_cases factors : FrequencyClockFinite event eps n pd ps dL dR sL sR
    · exact .finite zero factors
        (fun s regular => actual_zero_clock_frequency_tensor event eps s n regular factors.1)
        (fun s regular => actual_zero_clock_frequency_probe event eps s n pd ps dL dR sL sR regular factors.2)
    · exact .clockResponsibility zero factors

end LowEnergy.GaussComposite.ActualDressedZeroClockFrequency

