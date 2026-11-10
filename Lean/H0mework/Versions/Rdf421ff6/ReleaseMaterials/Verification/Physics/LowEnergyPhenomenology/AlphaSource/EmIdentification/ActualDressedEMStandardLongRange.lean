import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMPhysicalPropagation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularWholeSphereChart
import Mathlib.Algebra.MvPolynomial.Funext

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPhysicalRead
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource PreparationVacuumPhysicalPoleSheet
open ActualEMCarrierOwn ActualDressedFullCoulomb ActualDressedOrderedStatic ActualDressedEMTensorClock
open ActualDressedAngularSpherePrice ActualDressedAngularSectorFourier ActualDressedAngularWholeChart
open ActualDressedNoetherCoulombUnit ActualCompositeFieldCurrent ActualDressedCorrectedElectronRead
open ActualDressedZeroClockFrequency ActualDressedZeroClockVector ActualDressedEMZeroClockColumns
open ActualEMCurrentSplit ActualDressedEMSourceSpectrum ActualDressedEMNativeMomentum
open ActualDressedEMNativeCoulomb ActualDressedEMCorrectedCouplingSource
open LowEnergy.ActualDressedVisiblePole LowEnergy.ActualDressedPoleWardMode
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology SchwartzMap
attribute [local irreducible] directionLeadingDenominator directionScaledNumerator directionZeroClockEM
  directionZeroClockProbe directionLeadingRead noetherPairScale

def sourceSpatialSquarePolynomial : DirectionParameters :=
  MvPolynomial.X (0 : Fin 3)^2+MvPolynomial.X (1 : Fin 3)^2+MvPolynomial.X (2 : Fin 3)^2

def sourceSpatialVariable : Fin 4 → DirectionParameters :=
  ![0,MvPolynomial.X (0 : Fin 3),MvPolynomial.X (1 : Fin 3),MvPolynomial.X (2 : Fin 3)]

/-- The numerator is extracted from the actual full289 adjugate, after the original damping
and spatial divisibility. Both action-normalized vertices are paid once. -/
def sourceStaticNoetherNumerator (event : DressedEvent) (mu nu : Fin 4) : DirectionParameters :=
  -MvPolynomial.C (noetherPairScale^2)*(directionScaledNumerator event (directionZeroClockEM event mu nu)).coeff 0

def sourceStaticNoetherTensor (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  noetherPairScale^2 • directionEMCoefficient event n

theorem source_spatial_square_polynomial (n : PhysicalMomentum) :
    MvPolynomial.eval (directionValues n) sourceSpatialSquarePolynomial=(spatialSquare n : ℂ) := by
  simp only [sourceSpatialSquarePolynomial,map_add,map_pow,MvPolynomial.eval_X,directionValues,
    spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]

private theorem source_square_polynomial_nonzero : sourceSpatialSquarePolynomial≠0 := by
  intro zero
  have paid := source_spatial_square_polynomial (Pi.single 0 1)
  rw [zero,map_zero] at paid
  norm_num [spatialSquare,Pi.single_apply,Fin.ext_iff] at paid

private theorem source_transverse_polynomial_nonzero :
    sourceSpatialSquarePolynomial-sourceSpatialVariable 3^2≠0 := by
  intro zero
  have paid := congrArg (MvPolynomial.eval (directionValues (Pi.single 0 1))) zero
  simp only [map_sub,map_pow,source_spatial_square_polynomial,sourceSpatialVariable,
    Matrix.cons_val_three,map_zero] at paid
  norm_num [spatialSquare,directionValues,Pi.single_apply,Fin.ext_iff] at paid

/-- A reference coefficient is selected from a finite nonzero source support, rather than
sampling or averaging a physical direction. -/
def sourceCoefficientAddress (P : DirectionParameters) : Fin 3 →₀ ℕ := by
  classical
  exact if nonzero : P≠0 then Classical.choose (MvPolynomial.exists_coeff_ne_zero nonzero) else 0

theorem source_coefficient_address_nonzero (P : DirectionParameters) (nonzero : P≠0) :
    MvPolynomial.coeff (sourceCoefficientAddress P) P≠0 := by
  classical
  simp only [sourceCoefficientAddress,dif_pos nonzero]
  exact Classical.choose_spec (MvPolynomial.exists_coeff_ne_zero nonzero)

def sourceStaticTemporalCoefficient (event : DressedEvent) : ℂ :=
  let D := directionLeadingDenominator event*sourceSpatialSquarePolynomial
  let N := sourceSpatialSquarePolynomial^2*sourceStaticNoetherNumerator event 0 0
  MvPolynomial.coeff (sourceCoefficientAddress D) N/MvPolynomial.coeff (sourceCoefficientAddress D) D

def sourceStaticSpatialCoefficient (event : DressedEvent) : ℂ :=
  let D := directionLeadingDenominator event*(sourceSpatialSquarePolynomial-sourceSpatialVariable 3^2)
  let N := sourceSpatialSquarePolynomial^2*sourceStaticNoetherNumerator event 3 3
  MvPolynomial.coeff (sourceCoefficientAddress D) N/MvPolynomial.coeff (sourceCoefficientAddress D) D

def sourceStandardStaticNumerator (electric magnetic : ℂ) (mu nu : Fin 4) : DirectionParameters :=
  if mu=0 ∧ nu=0 then MvPolynomial.C electric*sourceSpatialSquarePolynomial else
    if mu=0 ∨ nu=0 then 0 else
      MvPolynomial.C magnetic*((if mu=nu then sourceSpatialSquarePolynomial else 0)-sourceSpatialVariable mu*sourceSpatialVariable nu)

def sourceStandardStaticTensor (electric magnetic : ℂ) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => MvPolynomial.eval (directionValues n) (sourceStandardStaticNumerator electric magnetic mu nu)/(spatialSquare n : ℂ)^2

/-- This finite remainder is computed from the original adjugate numerator and determinant.
It is not defined as a difference between an assumed target and a physical read. -/
def sourceStandardStaticRemainder (event : DressedEvent) : Matrix (Fin 4) (Fin 4) DirectionParameters :=
  fun mu nu => sourceSpatialSquarePolynomial^2*sourceStaticNoetherNumerator event mu nu-
    directionLeadingDenominator event*sourceStandardStaticNumerator
      (sourceStaticTemporalCoefficient event) (sourceStaticSpatialCoefficient event) mu nu

theorem source_static_noether_quotient (event : DressedEvent) (n : PhysicalMomentum) (mu nu : Fin 4) :
    sourceStaticNoetherTensor event n mu nu=
      MvPolynomial.eval (directionValues n) (sourceStaticNoetherNumerator event mu nu)/directionLeadingRead event n := by
  simp only [sourceStaticNoetherTensor,Matrix.smul_apply,smul_eq_mul,directionEMCoefficient,
    directionCoulombCoefficient,sourceStaticNoetherNumerator,map_mul,map_neg,MvPolynomial.eval_C]
  ring1

/-- The primitive remainder gives the exact discrepancy denominator at every actual regular
physical direction; no scalar-response equality is supplied by the caller. -/
theorem source_static_remainder_read (event : DressedEvent) (n : PhysicalMomentum) (mu nu : Fin 4)
    (regular : directionLeadingRead event n≠0) (q_ne : spatialSquare n≠0) :
    sourceStaticNoetherTensor event n mu nu-
      sourceStandardStaticTensor (sourceStaticTemporalCoefficient event) (sourceStaticSpatialCoefficient event) n mu nu=
    MvPolynomial.eval (directionValues n) (sourceStandardStaticRemainder event mu nu)/
      (directionLeadingRead event n*(spatialSquare n : ℂ)^2) := by
  rw [source_static_noether_quotient]
  simp only [sourceStandardStaticTensor,sourceStandardStaticRemainder,map_sub,map_mul,map_pow,
    source_spatial_square_polynomial]
  rw [show MvPolynomial.eval (directionValues n) (directionLeadingDenominator event)=directionLeadingRead event n by unfold directionLeadingRead; rfl]
  field_simp [regular,Complex.ofReal_ne_zero.mpr q_ne]

private theorem polynomial_real_ext (P : DirectionParameters)
    (zero : ∀n : PhysicalMomentum,MvPolynomial.eval (directionValues n) P=0) : P=0 := by
  apply MvPolynomial.funext_set (fun _ : Fin 3 => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  let n : PhysicalMomentum := fun i => (z i).re
  have coordinates : directionValues n=z := by
    funext i
    obtain ⟨r,eq⟩ := hz i (Set.mem_univ i)
    simp only [directionValues,n,←eq,Complex.ofReal_re]
  rw [←coordinates,map_zero]
  exact zero n

private theorem polynomial_real_nonzero (P : DirectionParameters) (nonzero : P≠0) :
    ∃n : PhysicalMomentum,MvPolynomial.eval (directionValues n) P≠0 := by
  by_contra every
  push Not at every
  exact nonzero (polynomial_real_ext P every)

/-- A nonzero source remainder generates an actual physical direction where the source
denominator and spatial norm are regular and the standard tensor fails. -/
theorem source_static_obstruction_direction (event : DressedEvent)
    (denominator : directionLeadingDenominator event≠0) (mu nu : Fin 4)
    (nonzero : sourceStandardStaticRemainder event mu nu≠0) :
    ∃n : PhysicalMomentum,directionLeadingRead event n≠0 ∧ spatialSquare n≠0 ∧
      sourceStaticNoetherTensor event n mu nu≠
        sourceStandardStaticTensor (sourceStaticTemporalCoefficient event) (sourceStaticSpatialCoefficient event) n mu nu := by
  obtain ⟨n,paid⟩ := polynomial_real_nonzero
    (directionLeadingDenominator event*sourceSpatialSquarePolynomial*sourceStandardStaticRemainder event mu nu)
    (mul_ne_zero (mul_ne_zero denominator source_square_polynomial_nonzero) nonzero)
  simp only [map_mul,source_spatial_square_polynomial,mul_ne_zero_iff] at paid
  have regular : directionLeadingRead event n≠0 := by simpa only [directionLeadingRead] using paid.1.1
  have q_ne : spatialSquare n≠0 := Complex.ofReal_ne_zero.mp paid.1.2
  refine ⟨n,regular,q_ne,?_⟩
  intro scalar
  have discrepancy := source_static_remainder_read event n mu nu regular q_ne
  rw [scalar,sub_self] at discrepancy
  have residualZero := (div_eq_zero_iff.mp discrepancy.symm).resolve_right
    (mul_ne_zero regular (pow_ne_zero 2 paid.1.2))
  exact paid.2 residualZero

/-- Whole-direction standard identification is equivalent to sixteen finite source polynomial
checks. The converse is certified on real physical directions, not complex-only probes. -/
theorem source_static_standard_iff (event : DressedEvent) (denominator : directionLeadingDenominator event≠0) :
    sourceStandardStaticRemainder event=0 ↔
      ∀n : PhysicalMomentum,directionLeadingRead event n≠0→spatialSquare n≠0→
        sourceStaticNoetherTensor event n=
          sourceStandardStaticTensor (sourceStaticTemporalCoefficient event) (sourceStaticSpatialCoefficient event) n := by
  constructor
  · intro checked n regular q_ne
    funext mu nu
    have discrepancy := source_static_remainder_read event n mu nu regular q_ne
    have zero : sourceStandardStaticRemainder event mu nu=0 := congrFun (congrFun checked mu) nu
    rw [zero,map_zero,zero_div] at discrepancy
    exact sub_eq_zero.mp discrepancy
  · intro standard
    by_contra failed
    have entry : ∃mu nu,sourceStandardStaticRemainder event mu nu≠0 := by
      by_contra every
      push Not at every
      exact failed (funext fun mu => funext (every mu))
    obtain ⟨mu,nu,nonzero⟩ := entry
    obtain ⟨n,regular,q_ne,different⟩ := source_static_obstruction_direction event denominator mu nu nonzero
    exact different (congrFun (congrFun (standard n regular q_ne) mu) nu)

inductive EMStaticStandardDisposition (event : DressedEvent) : Type
  | singular (zero : directionLeadingDenominator event=0)
  | standard (denominator : directionLeadingDenominator event≠0)
      (checked : sourceStandardStaticRemainder event=0)
      (whole : ∀n : PhysicalMomentum,directionLeadingRead event n≠0→spatialSquare n≠0→
        sourceStaticNoetherTensor event n=
          sourceStandardStaticTensor (sourceStaticTemporalCoefficient event) (sourceStaticSpatialCoefficient event) n)
  | obstruction (denominator : directionLeadingDenominator event≠0)
      (mu nu : Fin 4) (monomial : Fin 3 →₀ ℕ)
      (nonzero_coefficient : MvPolynomial.coeff monomial (sourceStandardStaticRemainder event mu nu)≠0)
      (actual_direction : ∃n : PhysicalMomentum,directionLeadingRead event n≠0 ∧ spatialSquare n≠0 ∧
        sourceStaticNoetherTensor event n mu nu≠
          sourceStandardStaticTensor (sourceStaticTemporalCoefficient event) (sourceStaticSpatialCoefficient event) n mu nu)

/-- All source coefficients and branch tests are computed before a consumer asks for a scalar.
A nonzero monomial and actual direction are emitted rather than hidden in an isotropy premise. -/
def sourceEMStaticStandardDisposition (event : DressedEvent) : EMStaticStandardDisposition event := by
  classical
  by_cases singular : directionLeadingDenominator event=0
  · exact .singular singular
  · by_cases checked : sourceStandardStaticRemainder event=0
    · exact .standard singular checked ((source_static_standard_iff event singular).mp checked)
    · have entry : ∃mu nu,sourceStandardStaticRemainder event mu nu≠0 := by
        by_contra every
        push Not at every
        exact checked (funext fun mu => funext (every mu))
      let mu := Classical.choose entry
      let nu := Classical.choose (Classical.choose_spec entry)
      have nonzero := Classical.choose_spec (Classical.choose_spec entry)
      exact .obstruction singular mu nu (sourceCoefficientAddress (sourceStandardStaticRemainder event mu nu))
        (source_coefficient_address_nonzero _ nonzero) (source_static_obstruction_direction event singular mu nu nonzero)

def sourceStaticPureCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (noetherEMCurrent pd dL dR) (sourceStaticNoetherTensor event n*ᵥnoetherEMCurrent ps sL sR)

def sourceStaticNonPureCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  directionProbeCoefficient event pd ps dL dR sL sR n-sourceStaticPureCoefficient event n pd ps dL dR sL sR

def sourceStaticOtherEMCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  ∑mu : Fin 4,∑nu : Fin 4,if mu=0 ∧ nu=0 then 0 else
    noetherEMCurrent pd dL dR mu*sourceStaticNoetherTensor event n mu nu*noetherEMCurrent ps sL sR nu

/-- The new coefficient of the three actual non-pure pieces is generated by their full
zero-damping read. Neither external source charge nor an EM-only approximation replaces it. -/
theorem source_static_nonpure_return (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (regular : directionLeadingRead event n≠0)
    (spatial : DirectionSpatialFinite event pd ps dL dR sL sR) :
    Tendsto (fun eps : ℝ => -(eps : ℂ)^4*zeroNonPureRead event eps n pd ps dL dR sL sR)
      (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceStaticNonPureCoefficient event n pd ps dL dR sL sR)) := by
  have returned := actual_direction_coulomb_coefficient event pd ps dL dR sL sR n regular spatial
  let observe := fun T : Matrix (Fin 4) (Fin 4) ℂ =>
    dotProduct (noetherEMCurrent pd dL dR) ((noetherPairScale^2 • T)*ᵥnoetherEMCurrent ps sL sR)
  have continuous : Continuous observe := by
    dsimp only [observe]
    simp only [Matrix.mulVec,dotProduct,Matrix.smul_apply,smul_eq_mul]
    fun_prop
  have scale (a : ℂ) (T : Matrix (Fin 4) (Fin 4) ℂ) : observe (a • T)=a*observe T := by
    dsimp only [observe]
    rw [smul_comm,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  have pure := continuous.continuousAt.tendsto.comp returned.1
  simp only [Function.comp_def,scale] at pure
  change Tendsto (fun eps : ℝ => -(eps : ℂ)^4*zeroNoetherPureRead event eps n pd ps dL dR sL sR)
    (nhdsWithin 0 ({0}ᶜ)) (𝓝 (sourceStaticPureCoefficient event n pd ps dL dR sL sR)) at pure
  have difference := returned.2.sub pure
  apply Tendsto.congr' _ difference
  filter_upwards with eps
  simp only [zeroNonPureRead]
  ring1

private theorem complete_temporal_split (T : Matrix (Fin 4) (Fin 4) ℂ) (qd qs : Fin 4 → ℂ) :
    dotProduct qd (T*ᵥqs)=qd 0*T 0 0*qs 0+
      ∑mu : Fin 4,∑nu : Fin 4,if mu=0 ∧ nu=0 then 0 else qd mu*T mu nu*qs nu := by
  simp [dotProduct,Matrix.mulVec,Fin.sum_univ_four]
  ring1

/-- This full actual current-scattering coefficient keeps both source charge calibrations,
the other fifteen EM reads and all three non-pure response pieces. -/
theorem source_static_complete_current_scattering (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    directionProbeCoefficient event pd ps dL dR sL sR n/(4*(Real.pi : ℂ))=
      sourceInputCharge dR*sourceInputCharge sR*(sourceStaticNoetherTensor event n 0 0/(4*(Real.pi : ℂ)))+
      (noetherChargeCalibration pd dL dR*sourceInputCharge sR+
        sourceInputCharge dR*noetherChargeCalibration ps sL sR+
        noetherChargeCalibration pd dL dR*noetherChargeCalibration ps sL sR)*
          (sourceStaticNoetherTensor event n 0 0/(4*(Real.pi : ℂ)))+
      sourceStaticOtherEMCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ))+
      sourceStaticNonPureCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ)) := by
  have split := complete_temporal_split (sourceStaticNoetherTensor event n)
    (noetherEMCurrent pd dL dR) (noetherEMCurrent ps sL sR)
  rw [actual_calibrated_noether_charge,actual_calibrated_noether_charge] at split
  dsimp only [sourceStaticNonPureCoefficient,sourceStaticPureCoefficient,sourceStaticOtherEMCoefficient]
  rw [split]
  ring1

def sourceGeneratedScalarCEM (event : DressedEvent) : ℂ :=
  sourceStaticTemporalCoefficient event/(4*(Real.pi : ℂ))

private theorem source_standard_temporal (electric magnetic : ℂ) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    sourceStandardStaticTensor electric magnetic n 0 0=electric := by
  simp only [sourceStandardStaticTensor,sourceStandardStaticNumerator,and_self,if_true,
    map_mul,MvPolynomial.eval_C,source_spatial_square_polynomial,unit,Complex.ofReal_one,one_pow,mul_one,div_one]

private theorem source_spatial_nonnegative (k : PhysicalMomentum) : 0 ≤ spatialSquare k := by
  unfold spatialSquare
  positivity

/-- The whole source chart and finite adjugate checks turn the actual temporal tensor symbol
into the standard Newton multiplier on every physical momentum, without an angular average. -/
theorem source_standard_temporal_symbol (event : DressedEvent) (chart : SourceWholeDirectionChart event)
    (denominator : directionLeadingDenominator event≠0) (checked : sourceStandardStaticRemainder event=0)
    (k : PhysicalMomentum) :
    noetherPairScale^2*sectorCoefficientSymbol event (directionZeroClockEM event 0 0) chart.eta k=
      sourceStaticTemporalCoefficient event/(spatialSquare k : ℂ) := by
  classical
  by_cases positive : 0<spatialSquare k
  · let n := sectorDirection k
    have unit : spatialSquare n=1 := sector_direction_unit k positive
    have member := whole_source_chart_membership event chart n unit
    have regular := (direction_chart_regular event chart.eta chart.positive n member).2
    have whole := (source_static_standard_iff event denominator).mp checked n regular (by rw [unit];norm_num)
    have temporal := congrFun (congrFun whole 0) 0
    rw [source_standard_temporal _ _ n unit] at temporal
    change noetherPairScale^2*directionCoulombCoefficient event (directionZeroClockEM event 0 0) n=
      sourceStaticTemporalCoefficient event at temporal
    rw [sectorCoefficientSymbol,if_pos ⟨positive,member.2⟩]
    change noetherPairScale^2*((spatialSquare k : ℂ)⁻¹*directionCoulombCoefficient event (directionZeroClockEM event 0 0) n)=_
    rw [show noetherPairScale^2*((spatialSquare k : ℂ)⁻¹*directionCoulombCoefficient event (directionZeroClockEM event 0 0) n)=
      (noetherPairScale^2*directionCoulombCoefficient event (directionZeroClockEM event 0 0) n)/(spatialSquare k : ℂ) by ring1,temporal]
  · have zero : spatialSquare k=0 := le_antisymm (le_of_not_gt positive) (source_spatial_nonnegative k)
    simp [sectorCoefficientSymbol,zero]

/-- Actual full-source temporal response, rather than a single-direction coefficient packet,
has the standard real-space one-over-radius convolution and the original single four-pi. -/
theorem source_standard_actual_coulomb_convolution (event : DressedEvent)
    (chart : SourceWholeDirectionChart event) (denominator : directionLeadingDenominator event≠0)
    (checked : sourceStandardStaticRemainder event=0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    noetherPairScale^2*sectorCoefficientPacket event (directionZeroClockEM event 0 0) chart.eta test x=
      ∫y : PhysicalMomentum,sourceGeneratedScalarCEM event/
        (Real.sqrt (spatialSquare y) : ℂ)*emPacket test (x-y) := by
  have newton : noetherPairScale^2*sectorCoefficientPacket event (directionZeroClockEM event 0 0) chart.eta test x=
      sourceStaticTemporalCoefficient event*emNewtonPacket 1 0 test x := by
    have emptyPacket : emNewtonPacket 1 0 test x=
        ∫frequency,sourceSpatialPhase frequency x*test frequency/(spatialSquare (sourceSpatialMomentum frequency) : ℂ) := by
      unfold emNewtonPacket emFourierMoment
      change (∫frequency,(1 : ℂ)*sourceSpatialPhase frequency x*test frequency*emNewtonMultiplier 1 0 frequency)=_
      simp only [one_mul,emNewtonMultiplier,Complex.ofReal_zero,zero_pow (by decide : 2≠0),
        zero_mul,add_zero,div_eq_mul_inv]
    rw [sectorCoefficientPacket,emptyPacket,←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with frequency
    have generated := source_standard_temporal_symbol event chart denominator checked (sourceSpatialMomentum frequency)
    linear_combination (sourceSpatialPhase frequency x*test frequency)*generated
  rw [newton,em_newton_massless_convolution,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [sourceGeneratedScalarCEM,div_eq_mul_inv,mul_inv_rev]
  ring1

/-- The standard spatial potential is the outer limit of the actual source packet only after
the original inner positive-damping response has returned on the complete direction chart. -/
theorem source_standard_coulomb_spatial_return (event : DressedEvent) (chart : SourceWholeDirectionChart event)
    (denominator : directionLeadingDenominator event≠0) (checked : sourceStandardStaticRemainder event=0)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ => noetherPairScale^2*
      sectorFourierPacket event (directionZeroClockEM event 0 0) chart.eta scale test x)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∫y : PhysicalMomentum,sourceGeneratedScalarCEM event/
        (Real.sqrt (spatialSquare y) : ℂ)*emPacket test (x-y))) := by
  have returned := (actual_sector_fourier_return event (directionZeroClockEM event 0 0)
    chart.eta chart.positive test x).const_mul (noetherPairScale^2)
  rw [source_standard_actual_coulomb_convolution event chart denominator checked test x] at returned
  exact returned

/-- These two effective stiffnesses are read from the full source's electric and magnetic
static coefficients, with its literal Gram and two Noether vertices preserved. -/
def sourceGeneratedElectricStiffness (event : DressedEvent) : ℂ :=
  -(3/4 : ℂ)*noetherPairScale^2/sourceStaticTemporalCoefficient event

def sourceGeneratedMagneticStiffness (event : DressedEvent) : ℂ :=
  (3/4 : ℂ)*noetherPairScale^2/sourceStaticSpatialCoefficient event

def sourceFrequencySpatialValue (eps : ℝ) (n : PhysicalMomentum) : Fin 4 → ℂ[X] :=
  ![0,C (((eps^2 : ℝ) • n) 0 : ℂ),C (((eps^2 : ℝ) • n) 1 : ℂ),C (((eps^2 : ℝ) • n) 2 : ℂ)]

def sourceStandardFrequencyMatrix (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] :=
  let electric := C (sourceGeneratedElectricStiffness event)
  let magnetic := C (sourceGeneratedMagneticStiffness event)
  let omega := C (eps^2 : ℂ)*X
  let q := C (spatialSquare ((eps^2 : ℝ) • n) : ℂ)
  let k := sourceFrequencySpatialValue eps n
  Matrix.of (fun mu nu => if mu=0 ∧ nu=0 then electric*q else
    if mu=0 then electric*omega*k nu else
    if nu=0 then electric*omega*k mu else
      (if mu=nu then electric*omega^2-magnetic*q else 0)+magnetic*k mu*k nu)

/-- The original conserved-current projection keeps its charge, projects the spatial input,
and generates the longitudinal spatial current required by the same physical clock. -/
def sourceFrequencyCurrentProjection (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] :=
  let omega := C (eps^2 : ℂ)*X
  let q := C (spatialSquare ((eps^2 : ℝ) • n) : ℂ)
  let k := sourceFrequencySpatialValue eps n
  Matrix.of (fun mu nu => if mu=0 ∧ nu=0 then q else
    if mu=0 then 0 else
    if nu=0 then omega*k mu else (if mu=nu then q else 0)-k mu*k nu)

def sourceAllEMColumnPolynomials (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 4) ℂ[X] := Matrix.of (fun i nu => zeroClockEMColumn event eps n nu i)

/-- This check applies the source-generated effective Maxwell coefficients to all complete
original adjugate columns. The native current constraint remains an output projection. -/
def sourceDynamicStandardRemainder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] :=
  C (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
      (sourceStandardFrequencyMatrix event eps n*(emInsertion.map C).transpose*sourceAllEMColumnPolynomials event eps n)-
    (C (3/4 : ℂ)*zeroClockFrequencyDenominator event eps n) • sourceFrequencyCurrentProjection eps n

private theorem polynomial_matrix_eval_mul {ι κ ρ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ[X]) (B : Matrix κ ρ ℂ[X]) (s : ℂ) :
    (A*B).map (Polynomial.eval s)=A.map (Polynomial.eval s)*B.map (Polynomial.eval s) := by
  funext i j
  simp only [Matrix.map_apply,Matrix.mul_apply,eval_finsetSum,eval_mul]

private theorem polynomial_matrix_eval_smul {ι κ : Type*} (A : Matrix ι κ ℂ[X]) (c : ℂ[X]) (s : ℂ) :
    (c • A).map (Polynomial.eval s)=c.eval s • A.map (Polynomial.eval s) := by
  funext i j
  simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,eval_mul]

private theorem polynomial_matrix_scalar_commute {ι κ ρ : Type*} [Fintype κ]
    (E : Matrix ι κ ℂ[X]) (P : Matrix κ ρ ℂ[X]) (d c : ℂ[X]) :
    E*((c*d) • P)=d • (E*(c • P)) := by
  rw [Matrix.mul_smul,Matrix.mul_smul,smul_smul]
  exact congrArg (fun z : ℂ[X] => z • (E*P)) (mul_comm c d)

private theorem polynomial_matrix_column_mul {ι κ ρ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ[X]) (B : Matrix κ ρ ℂ[X]) (j : ρ) :
    (fun i => (A*B) i j)=A*ᵥ(fun k => B k j) := rfl

private theorem source_quotient_matrix_law (M : Matrix (Fin 4) (Fin 4) ℂ)
    (E : Matrix (Fin 289) (Fin 4) ℂ) (V : Matrix (Fin 289) (Fin 4) ℂ)
    (P : Matrix (Fin 4) (Fin 4) ℂ) (d q c : ℂ) (d_ne : d≠0)
    (paid : (q • (M*E.transpose))*V=(c*d) • P) :
    q • (M*(d⁻¹ • (E.transpose*V)))=c • P := by
  calc
    _=d⁻¹ • ((q • (M*E.transpose))*V) := by
      rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
      simp only [smul_smul]
      exact congrArg (fun z : ℂ => z • (M*(E.transpose*V))) (mul_comm q d⁻¹)
    _=d⁻¹ • ((c*d) • P) := congrArg (fun T => d⁻¹ • T) paid
    _=c • P := by
      rw [smul_smul]
      exact congrArg (fun z : ℂ => z • P) (by field_simp [d_ne])

/-- All source pole orders can consume this same cleared standard response law;
no simple-pole or scalar-dispersion premise enters the original full column. -/
theorem source_dynamic_standard_cleared (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (checked : sourceDynamicStandardRemainder event eps n=0) :
    (C (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
      (sourceStandardFrequencyMatrix event eps n*(emInsertion.map C).transpose))*sourceAllEMColumnPolynomials event eps n=
      (C (3/4 : ℂ)*zeroClockFrequencyDenominator event eps n) • sourceFrequencyCurrentProjection eps n := by
  unfold sourceDynamicStandardRemainder at checked
  have source := sub_eq_zero.mp checked
  simpa only [Matrix.smul_mul,Matrix.mul_assoc] using source

private theorem source_frequency_column_quotient (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (nu : Fin 4) (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0) :
    zeroClockEMColumnRead event eps s n nu=fun i =>
      (zeroClockEMColumn event eps n nu i).eval (s : ℂ)/(zeroClockFrequencyDenominator event eps n).eval (s : ℂ) := by
  funext i
  exact reduced_read_at_regular _ _ _ regular

/-- The finite source checks are consumed by the actual all-sixteen EM tensor after the
original positive-damping limit. This is a standard Maxwell response, with the source Ward
projection retained instead of assuming that every external current is already conserved. -/
theorem source_dynamic_standard_actual_tensor (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (checked : sourceDynamicStandardRemainder event eps n=0)
    (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0) :
    (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
      ((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval (s : ℂ))*zeroClockFrequencyEMRead event eps s n)=
      (3/4 : ℂ) • (sourceFrequencyCurrentProjection eps n).map (Polynomial.eval (s : ℂ)) := by
  have cleared := congrArg (fun T : Matrix (Fin 4) (Fin 4) ℂ[X] => T.map (Polynomial.eval (s : ℂ)))
    (source_dynamic_standard_cleared event eps n checked)
  simp only [polynomial_matrix_eval_mul,polynomial_matrix_eval_smul,eval_C,eval_mul] at cleared
  have insertion : ((emInsertion.map C).transpose).map (Polynomial.eval (s : ℂ))=emInsertion.transpose := by
    funext i j
    simp only [Matrix.map_apply,Matrix.transpose_apply,eval_C]
  rw [insertion] at cleared
  have tensorAll : zeroClockFrequencyEMRead event eps s n=
      ((zeroClockFrequencyDenominator event eps n).eval (s : ℂ))⁻¹ •
        (emInsertion.transpose*(sourceAllEMColumnPolynomials event eps n).map (Polynomial.eval (s : ℂ))) := by
    funext alpha nu
    have read := actual_zero_clock_em_column_tensor event eps s n alpha nu regular finite
    rw [source_frequency_column_quotient event eps s n nu regular] at read
    rw [←read]
    simp only [dotProduct,Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,Matrix.transpose_apply,
      Matrix.map_apply,sourceAllEMColumnPolynomials,Matrix.of_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring1
  rw [tensorAll]
  exact source_quotient_matrix_law _ _ _ _ _ _ _ regular cleared

inductive EMDynamicStandardDisposition (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : Type
  | standard (checked : sourceDynamicStandardRemainder event eps n=0)
      (actual : ∀s : ℝ,EMColumnsClockFinite event eps n→
        (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0→
        (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
          ((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval (s : ℂ))*zeroClockFrequencyEMRead event eps s n)=
            (3/4 : ℂ) • (sourceFrequencyCurrentProjection eps n).map (Polynomial.eval (s : ℂ)))
  | feedback (mu nu : Fin 4) (order : ℕ)
      (coefficient_nonzero : (sourceDynamicStandardRemainder event eps n mu nu).coeff order≠0)

def sourceEMDynamicStandardDisposition (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    EMDynamicStandardDisposition event eps n := by
  classical
  by_cases checked : sourceDynamicStandardRemainder event eps n=0
  · exact .standard checked (fun s finite regular => source_dynamic_standard_actual_tensor event eps s n checked finite regular)
  · have entry : ∃mu nu,sourceDynamicStandardRemainder event eps n mu nu≠0 := by
      by_contra every
      push Not at every
      exact checked (funext fun mu => funext (every mu))
    let mu := Classical.choose entry
    let nu := Classical.choose (Classical.choose_spec entry)
    have nonzero := Classical.choose_spec (Classical.choose_spec entry)
    have coefficient : ∃k,(sourceDynamicStandardRemainder event eps n mu nu).coeff k≠0 := by
      by_contra every
      push Not at every
      exact nonzero (Polynomial.ext fun k => (every k).trans (coeff_zero _).symm)
    exact .feedback mu nu (Classical.choose coefficient) (Classical.choose_spec coefficient)

/-- The new Maxwell law consumes the original all289 cancellation order and full mode.
No column residue, pole multiplicity, or sigma-left defect is replaced. -/
theorem source_dynamic_standard_pole_kernel (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (checked : sourceDynamicStandardRemainder event eps n=0)
    (q_ne : spatialSquare ((eps^2 : ℝ) • n)≠0) :
    (sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval a.val)*ᵥ
      (emInsertion.transpose*ᵥsourcePhysicalPoleMode event eps n a c)=0 := by
  let E := emInsertion.map C
  let M := C (spatialSquare ((eps^2 : ℝ) • n) : ℂ) • sourceStandardFrequencyMatrix event eps n
  let H := E*M*E.transpose
  let F := E*((C (3/4 : ℂ)) • sourceFrequencyCurrentProjection eps n)
  let D := zeroClockFrequencyDenominator event eps n
  have core : H*sourceAllEMColumnPolynomials event eps n=D • F := by
    calc
      _=E*((C (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
        (sourceStandardFrequencyMatrix event eps n*E.transpose))*sourceAllEMColumnPolynomials event eps n) := by
          simp only [H,M,Matrix.mul_assoc,Matrix.smul_mul]
      _=E*((C (3/4 : ℂ)*D) • sourceFrequencyCurrentProjection eps n) := by
        rw [source_dynamic_standard_cleared event eps n checked]
      _=D • F := by
        exact polynomial_matrix_scalar_commute E (sourceFrequencyCurrentProjection eps n) D (C (3/4 : ℂ))
  have column : H*ᵥzeroClockEMColumn event eps n c.val.2=D • (fun i => F i c.val.2) := by
    have source := congrArg (fun T : Matrix (Fin 289) (Fin 4) ℂ[X] => fun i => T i c.val.2) core
    rw [polynomial_matrix_column_mul] at source
    have left : (fun i => sourceAllEMColumnPolynomials event eps n i c.val.2)=zeroClockEMColumn event eps n c.val.2 := by
      funext i
      simp only [sourceAllEMColumnPolynomials,Matrix.of_apply]
    have right : (fun i => (D • F) i c.val.2)=D • (fun i => F i c.val.2) := by
      funext i
      rfl
    exact (congrArg (fun v => H*ᵥv) left).symm.trans (source.trans right)
  have observed : a.val∈visibleRoots (readFraction
      (dotProduct (fun i => C (emInsertion i c.val.1)) (zeroClockEMColumn event eps n c.val.2)) D) := by
    rw [actual_zero_clock_em_column_observer]
    exact c.property
  have full := source_visible_full_kernel H (zeroClockEMColumn event eps n c.val.2)
    (fun i => F i c.val.2) D (fun i => emInsertion i c.val.1) a.val column observed
  have Eeval : E.map (Polynomial.eval a.val)=emInsertion := by
    funext i j
    simp only [E,Matrix.map_apply,eval_C]
  have transposeEval : E.transpose.map (Polynomial.eval a.val)=emInsertion.transpose := by
    funext i j
    simp only [E,Matrix.map_apply,Matrix.transpose_apply,eval_C]
  have Heval : H.map (Polynomial.eval a.val)=
      emInsertion*((spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
        (sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval a.val))*emInsertion.transpose := by
    dsimp only [H]
    rw [polynomial_matrix_eval_mul,polynomial_matrix_eval_mul,Eeval,transposeEval]
    simp only [M,polynomial_matrix_eval_smul,eval_C]
  rw [Heval,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,Matrix.smul_mulVec] at full
  have embedded : emInsertion*ᵥ((spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
      ((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval a.val)*ᵥ
        (emInsertion.transpose*ᵥsourcePhysicalPoleMode event eps n a c)))=0 := by
    simpa only [D,sourcePhysicalPoleMode,actualEMZeroClockMode] using full
  have read := congrArg (fun v : Fin 289 → ℂ => emInsertion.transpose*ᵥv) embedded
  rw [Matrix.mulVec_mulVec,em_coordinate_gram,Matrix.smul_mulVec,Matrix.one_mulVec,Matrix.mulVec_zero] at read
  have normalized := (smul_eq_zero.mp read).resolve_left (by norm_num : (3/4 : ℂ)≠0)
  exact (smul_eq_zero.mp normalized).resolve_left (Complex.ofReal_ne_zero.mpr q_ne)

private theorem dynamic_four_one (v : Fin 4 → ℂ) (h : 1<4) : v (⟨1,h⟩ : Fin 4)=v 1 := rfl
private theorem dynamic_four_two (v : Fin 4 → ℂ) (h : 2<4) : v (⟨2,h⟩ : Fin 4)=v 2 := rfl
private theorem dynamic_four_three (v : Fin 4 → ℂ) (h : 3<4) : v (⟨3,h⟩ : Fin 4)=v 3 := rfl

private def sourceComplexMaxwellMatrix (electric magnetic omega : ℂ) (k : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let K : Fin 4 → ℂ := ![0,(k 0 : ℂ),(k 1 : ℂ),(k 2 : ℂ)]
  let q := (spatialSquare k : ℂ)
  Matrix.of (fun mu nu => if mu=0 ∧ nu=0 then electric*q else
    if mu=0 then electric*omega*K nu else
    if nu=0 then electric*omega*K mu else
      (if mu=nu then electric*omega^2-magnetic*q else 0)+magnetic*K mu*K nu)

private theorem standard_frequency_evaluated (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) (a : ℂ) :
    (sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval a)=
      sourceComplexMaxwellMatrix (sourceGeneratedElectricStiffness event)
        (sourceGeneratedMagneticStiffness event) ((eps^2 : ℂ)*a) ((eps^2 : ℝ) • n) := by
  have spatial (mu : Fin 4) : (sourceFrequencySpatialValue eps n mu).eval a=
      (![0,(((eps^2 : ℝ) • n) 0 : ℂ),(((eps^2 : ℝ) • n) 1 : ℂ),(((eps^2 : ℝ) • n) 2 : ℂ)] : Fin 4 → ℂ) mu := by
    fin_cases mu <;> simp [sourceFrequencySpatialValue]
  funext mu nu
  simp only [Matrix.map_apply,sourceStandardFrequencyMatrix,sourceComplexMaxwellMatrix,Matrix.of_apply]
  split_ifs <;> simp only [eval_C,eval_mul,eval_pow,eval_X,eval_sub,eval_add,eval_zero,spatial]

private theorem complex_maxwell_transverse (electric magnetic omega : ℂ) (k : PhysicalMomentum)
    (v : Fin 4 → ℂ) (q_ne : spatialSquare k≠0) :
    nativeTransverseRead k (sourceComplexMaxwellMatrix electric magnetic omega k*ᵥv)=
      (electric*omega^2-magnetic*(spatialSquare k : ℂ)) • nativeTransverseRead k v := by
  have q : (spatialSquare k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr q_ne
  funext i
  fin_cases i <;> simp [nativeTransverseRead,nativeSpatialContraction,sourceComplexMaxwellMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four,Fin.succ,Pi.smul_apply,smul_eq_mul]
  all_goals simp only [spatialSquare,Complex.ofReal_add,Complex.ofReal_pow] at q ⊢
  all_goals field_simp [q]
  all_goals ring1

theorem source_standard_transverse_frequency (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (a : ℂ) (v : Fin 4 → ℂ) (q_ne : spatialSquare ((eps^2 : ℝ) • n)≠0) :
    nativeTransverseRead ((eps^2 : ℝ) • n)
      ((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval a)*ᵥv)=
      (sourceGeneratedElectricStiffness event*((eps^2 : ℂ)*a)^2-
        sourceGeneratedMagneticStiffness event*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)) •
          nativeTransverseRead ((eps^2 : ℝ) • n) v := by
  rw [standard_frequency_evaluated]
  exact complex_maxwell_transverse _ _ _ _ _ q_ne

/-- An actual transverse source mode propagates on the standard Maxwell cone generated by
the complete static response and the original dynamic column checks, rather than by naming a rate c. -/
theorem source_standard_actual_transverse_cone (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) (propagation : SourceEMTransversePropagation event eps n eps_ne a c real)
    (checked : sourceDynamicStandardRemainder event eps n=0) :
    sourceGeneratedElectricStiffness event*(sourceFrequency eps a.val.re : ℂ)^2-
      sourceGeneratedMagneticStiffness event*(spatialSquare ((eps^2 : ℝ) • n) : ℂ)=0 := by
  have kernel := source_dynamic_standard_pole_kernel event eps n a c checked propagation.spatial_positive.ne'
  have read := congrArg (nativeTransverseRead ((eps^2 : ℝ) • n)) kernel
  rw [source_standard_transverse_frequency event eps n a.val _ propagation.spatial_positive.ne'] at read
  have zero : nativeTransverseRead ((eps^2 : ℝ) • n) (0 : Fin 4 → ℂ)=0 := by
    funext i
    simp [nativeTransverseRead,nativeSpatialContraction]
  rw [zero] at read
  have coordinate := congrFun read propagation.coordinate
  simp only [Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at coordinate
  have coefficient := (mul_eq_zero.mp coordinate).resolve_right propagation.coordinate_nonzero
  have physical := source_em_spectral_real_frequency eps a.val real
  unfold physicalFrequencyPole at physical
  rw [physical] at coefficient
  exact coefficient

theorem source_generated_stiffness_ratio (event : DressedEvent)
    (electric : sourceStaticTemporalCoefficient event≠0) (magnetic : sourceStaticSpatialCoefficient event≠0) :
    sourceGeneratedElectricStiffness event≠0 ∧
      sourceGeneratedMagneticStiffness event/sourceGeneratedElectricStiffness event=
        -sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event := by
  have h : noetherPairScale≠0 := by
    unfold noetherPairScale
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne')
  constructor
  · exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h)) electric
  · unfold sourceGeneratedElectricStiffness sourceGeneratedMagneticStiffness
    field_simp [electric,magnetic,h]

/-- The speed is identified through the standard Maxwell cone of every actual emitted
transverse mode at this source occurrence. Complete energy and all source debts stay on the mode. -/
theorem source_standard_corrected_speed_identity (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (eps_ne : eps≠0) (a : EMSourcePole event eps n) (c : EMSourceVisibleChannel event eps n a)
    (real : a.val.im=0) (propagation : SourceEMTransversePropagation event eps n eps_ne a c real)
    (checked : sourceDynamicStandardRemainder event eps n=0)
    (electric : sourceStaticTemporalCoefficient event≠0) (magnetic : sourceStaticSpatialCoefficient event≠0) :
    (actualRootPhaseSpeedSquared eps a.val.re n : ℂ)=
      -sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event := by
  have cone := source_standard_actual_transverse_cone event eps n eps_ne a c real propagation checked
  have ratio := source_generated_stiffness_ratio event electric magnetic
  have q : (spatialSquare ((eps^2 : ℝ) • n) : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr propagation.spatial_positive.ne'
  rw [←ratio.2]
  simp only [ActualDressedEMCorrectedCouplingSource.actualRootPhaseSpeedSquared,Complex.ofReal_div,Complex.ofReal_pow]
  field_simp [q,ratio.1]
  linear_combination cone

def sourceProjectedPhysicalCurrent (eps s : ℝ) (n : PhysicalMomentum) (j : Fin 4 → ℂ) : Fin 4 → ℂ :=
  (spatialSquare ((eps^2 : ℝ) • n) : ℂ)⁻¹ •
    ((sourceFrequencyCurrentProjection eps n).map (Polynomial.eval (s : ℂ))*ᵥj)

def sourceExternalCurrentWardResidual (eps s : ℝ) (n : PhysicalMomentum) (j : Fin 4 → ℂ) : Fin 4 → ℂ :=
  j-sourceProjectedPhysicalCurrent eps s n j

/-- The actual external current remains in the full scattering read. Its discarded Ward
component appears in three explicit additional terms; the conserved projection is never
substituted for the original charged source or detector. -/
theorem source_actual_current_projection_scattering (event : DressedEvent) (eps s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    let T := noetherPairScale^2 • correctedEMTensor event eps s sigma n
    let jd := noetherEMCurrent pd dL dR
    let js := noetherEMCurrent ps sL sR
    dotProduct jd (T*ᵥjs)=
      dotProduct (sourceProjectedPhysicalCurrent eps s n jd) (T*ᵥsourceProjectedPhysicalCurrent eps s n js)+
      dotProduct (sourceExternalCurrentWardResidual eps s n jd) (T*ᵥsourceProjectedPhysicalCurrent eps s n js)+
      dotProduct (sourceProjectedPhysicalCurrent eps s n jd) (T*ᵥsourceExternalCurrentWardResidual eps s n js)+
      dotProduct (sourceExternalCurrentWardResidual eps s n jd) (T*ᵥsourceExternalCurrentWardResidual eps s n js) := by
  dsimp only
  simp only [sourceExternalCurrentWardResidual,Matrix.mulVec_sub,dotProduct_sub,sub_dotProduct]
  ring1

/-- The original positive-sigma return, all sixteen response entries and the source current
projection are consumed in their physical order before the standard Maxwell read is returned. -/
theorem source_dynamic_standard_damping_return (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum)
    (checked : sourceDynamicStandardRemainder event eps n=0) (finite : EMColumnsClockFinite event eps n)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
      ((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval (s : ℂ))*correctedEMTensor event eps s sigma n))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 ((3/4 : ℂ) • (sourceFrequencyCurrentProjection eps n).map (Polynomial.eval (s : ℂ)))) := by
  have original : Tendsto (fun sigma : ℝ => correctedEMTensor event eps s sigma n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockFrequencyEMRead event eps s n)) := by
    apply tendsto_pi_nhds.2
    intro mu
    apply tendsto_pi_nhds.2
    intro nu
    exact actual_zero_clock_frequency_em_entry event eps s n mu nu regular
      (source_em_columns_pay_tensor_factors event eps n finite mu nu)
  have continuous : Continuous (fun T : Matrix (Fin 4) (Fin 4) ℂ =>
      (spatialSquare ((eps^2 : ℝ) • n) : ℂ) •
        ((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval (s : ℂ))*T)) := by
    apply continuous_pi
    intro mu
    apply continuous_pi
    intro nu
    change Continuous (fun T : Matrix (Fin 4) (Fin 4) ℂ =>
      (spatialSquare ((eps^2 : ℝ) • n) : ℂ)*
        ∑i : Fin 4,((sourceStandardFrequencyMatrix event eps n).map (Polynomial.eval (s : ℂ))) mu i*T i nu)
    fun_prop
  have generated := continuous.continuousAt.tendsto.comp original
  simp only [Function.comp_def,source_dynamic_standard_actual_tensor event eps s n checked finite regular] at generated
  exact generated

def sourceGeneratedPhysicalC (event : DressedEvent) : ℝ :=
  Real.sqrt (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).re

private theorem source_physical_c_square (event : DressedEvent)
    (real : (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).im=0)
    (positive : 0<(-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).re) :
    (((sourceGeneratedPhysicalC event)^2 : ℝ) : ℂ)=
      -sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event := by
  have square : (sourceGeneratedPhysicalC event)^2=
      (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).re := by
    exact Real.sq_sqrt positive.le
  calc
    (((sourceGeneratedPhysicalC event)^2 : ℝ) : ℂ)=
        ((-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).re : ℂ) :=
      congrArg Complex.ofReal square
    _=-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event := by
      apply Complex.ext
      · exact Complex.ofReal_re _
      · simpa only [Complex.ofReal_im] using real.symm

inductive EMStandardPhysicalReturn (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Type
  | zeroScale (zero : eps=0)
  | zeroMomentum (zero : spatialSquare ((eps^2 : ℝ) • n)=0)
  | angularResponsibility (source : AngularSourceDisposition event pd ps dL dR sL sR)
      (failure : directionClockDeterminant event=0 ∨ ¬DirectionClockFinite event pd ps dL dR sL sR ∨
        ¬DirectionSpatialFinite event pd ps dL dR sL sR)
  | exceptionalDirection (actual : (sourceExceptionalDirections event).Nonempty)
  | staticResponsibility (failure : directionLeadingDenominator event=0 ∨ sourceStandardStaticRemainder event≠0)
      (source : EMStaticStandardDisposition event)
  | zeroElectric (zero : sourceStaticTemporalCoefficient event=0)
  | zeroMagnetic (zero : sourceStaticSpatialCoefficient event=0)
  | nonrealConstitutive (imaginary : (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).im≠0)
  | nonpositiveConstitutive (nonpositive : (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).re≤0)
  | dynamicResponsibility (failure : sourceDynamicStandardRemainder event eps n≠0)
      (source : EMDynamicStandardDisposition event eps n)
  | standard (denominator : directionLeadingDenominator event≠0) (static_checked : sourceStandardStaticRemainder event=0)
      (electric : sourceStaticTemporalCoefficient event≠0) (magnetic : sourceStaticSpatialCoefficient event≠0)
      (real : (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).im=0)
      (positive : 0<sourceGeneratedPhysicalC event)
      (dynamic_checked : sourceDynamicStandardRemainder event eps n=0)
      (chart : SourceWholeDirectionChart event)
      (clock : DirectionClockFinite event pd ps dL dR sL sR)
      (spatial : DirectionSpatialFinite event pd ps dL dR sL sR)
      (source_chart_return : DirectionActualChartReturn event pd ps dL dR sL sR)
      (spectrum : EMCompleteSourceSpectrumReturn event eps n)
      (standard_modes : ∀eps_ne : eps≠0,∀a : EMSourcePole event eps n,∀c : EMSourceVisibleChannel event eps n a,
        ∀real : a.val.im=0,∀_propagation : SourceEMTransversePropagation event eps n eps_ne a c real,
          actualRootPhaseSpeedSquared eps a.val.re n=(sourceGeneratedPhysicalC event)^2)
      (standard_potential : ∀test : 𝓢(PhysicalMomentum,ℂ),∀x : PhysicalMomentum,
        noetherPairScale^2*sectorCoefficientPacket event (directionZeroClockEM event 0 0) chart.eta test x=
          ∫y : PhysicalMomentum,sourceGeneratedScalarCEM event/
            (Real.sqrt (spatialSquare y) : ℂ)*emPacket test (x-y))
      (standard_spatial_return : ∀test : 𝓢(PhysicalMomentum,ℂ),∀x : PhysicalMomentum,
        Tendsto (fun scale : ℝ => noetherPairScale^2*sectorFourierPacket event (directionZeroClockEM event 0 0) chart.eta scale test x)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (∫y : PhysicalMomentum,sourceGeneratedScalarCEM event/
            (Real.sqrt (spatialSquare y) : ℂ)*emPacket test (x-y))))
      (whole_probe_return : ∀test : 𝓢(PhysicalMomentum,ℂ),∀x : PhysicalMomentum,
        Tendsto (fun scale : ℝ => sectorFourierPacket event (directionZeroClockProbe event pd ps dL dR sL sR) chart.eta scale test x)
          (nhdsWithin 0 (Ioi 0)) (𝓝 (sectorCoefficientPacket event (directionZeroClockProbe event pd ps dL dR sL sR) chart.eta test x)))

/-- The source checks its original clock/spatial responsibility and whole direction coverage
before accepting the finite Maxwell checks. Complete original current scattering and spectral
failures remain outputs; no projected current replaces an external charged state. -/
def sourceEMStandardPhysicalReturn (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : EMStandardPhysicalReturn event eps n pd ps dL dR sL sR := by
  classical
  by_cases eps_zero : eps=0
  · exact .zeroScale eps_zero
  · by_cases momentum_zero : spatialSquare ((eps^2 : ℝ) • n)=0
    · exact .zeroMomentum momentum_zero
    · cases sourceAngularDisposition event pd ps dL dR sL sR with
      | singular failed => exact .angularResponsibility (.singular failed) (Or.inl failed)
      | clockResponsibility nonzero failed =>
        exact .angularResponsibility (.clockResponsibility nonzero failed) (Or.inr (Or.inl failed))
      | spatialResponsibility nonzero clock failed =>
        exact .angularResponsibility (.spatialResponsibility nonzero clock failed) (Or.inr (Or.inr failed))
      | chart nonzero clock spatial source_return =>
        cases sourceWholeDirectionDisposition event with
        | exceptional actual => exact .exceptionalDirection actual
        | whole chart =>
          let static := sourceEMStaticStandardDisposition event
          by_cases denominator : directionLeadingDenominator event=0
          · exact .staticResponsibility (Or.inl denominator) static
          · by_cases checked : sourceStandardStaticRemainder event=0
            · by_cases electric : sourceStaticTemporalCoefficient event=0
              · exact .zeroElectric electric
              · by_cases magnetic : sourceStaticSpatialCoefficient event=0
                · exact .zeroMagnetic magnetic
                · by_cases real : (-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).im=0
                  · by_cases positive : 0<(-sourceStaticTemporalCoefficient event/sourceStaticSpatialCoefficient event).re
                    · by_cases dynamic : sourceDynamicStandardRemainder event eps n=0
                      · exact .standard denominator checked electric magnetic real (Real.sqrt_pos.mpr positive) dynamic
                          chart clock spatial source_return (sourceEMCompleteSpectrumReturn event eps n)
                          (fun eps_ne a c realPole propagation => Complex.ofReal_injective
                            ((source_standard_corrected_speed_identity event eps n eps_ne a c realPole propagation dynamic electric magnetic).trans
                              (source_physical_c_square event real positive).symm))
                          (fun test x => source_standard_actual_coulomb_convolution event chart denominator checked test x)
                          (fun test x => source_standard_coulomb_spatial_return event chart denominator checked test x)
                          (fun test x => source_sector_full_probe_packet_return event pd ps dL dR sL sR chart.eta chart.positive test x)
                      · exact .dynamicResponsibility dynamic (sourceEMDynamicStandardDisposition event eps n)
                    · exact .nonpositiveConstitutive (le_of_not_gt positive)
                  · exact .nonrealConstitutive real
            · exact .staticResponsibility (Or.inr checked) static

def sourceProjectedEMForce (eps s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289 → ℂ) : Fin 289 → ℂ :=
  emInsertion*ᵥsourceProjectedPhysicalCurrent eps s n (emCoordinateCurrent forcing)

def sourceWholeWardProjectionResidual (eps s : ℝ) (n : PhysicalMomentum)
    (forcing : Fin 289 → ℂ) : Fin 289 → ℂ :=
  emInsertion*ᵥsourceExternalCurrentWardResidual eps s n (emCoordinateCurrent forcing)+emCurrentResidual forcing

/-- The original full forcing splits into its read projection plus the complete actual Ward
and non-EM forcing. Neither component is replaced by a counterfactual prepared current. -/
theorem source_whole_current_projection_complete (eps s : ℝ) (n : PhysicalMomentum) (forcing : Fin 289 → ℂ) :
    forcing=sourceProjectedEMForce eps s n forcing+sourceWholeWardProjectionResidual eps s n forcing := by
  have complete := em_current_complete forcing
  rw [em_current_force_insertion] at complete
  have generated : sourceProjectedEMForce eps s n forcing+sourceWholeWardProjectionResidual eps s n forcing=
      emInsertion*ᵥemCoordinateCurrent forcing+emCurrentResidual forcing := by
    simp only [sourceProjectedEMForce,sourceWholeWardProjectionResidual,sourceExternalCurrentWardResidual,
      Matrix.mulVec_sub]
    abel
  rw [generated]
  exact complete

/-- The same actual full Green transports the actual projected input and its full residual
into the original V read. This identity pays the omitted Ward and non-pure response explicitly. -/
theorem source_actual_full_v_projection (event : DressedEvent) (eps s sigma : ℝ) (n p : PhysicalMomentum)
    (left right : CompositeLeg) :
    ActualDressedCorrectedGreen.correctedResponse event eps s sigma n (ActualCompositeFieldCurrent.compositeCurrent p left right)=
      ActualDressedCorrectedGreen.correctedResponse event eps s sigma n
        (sourceProjectedEMForce eps s n (ActualCompositeFieldCurrent.compositeCurrent p left right))+
      ActualDressedCorrectedGreen.correctedResponse event eps s sigma n
        (sourceWholeWardProjectionResidual eps s n (ActualCompositeFieldCurrent.compositeCurrent p left right)) := by
  unfold ActualDressedCorrectedGreen.correctedResponse
  rw [←Matrix.mulVec_add]
  exact congrArg (fun v => ActualDressedCorrectedGreen.correctedGreen event eps s sigma n*ᵥv)
    (source_whole_current_projection_complete eps s n (ActualCompositeFieldCurrent.compositeCurrent p left right))

end LowEnergy.GaussComposite.ActualDressedEMPhysicalRead
