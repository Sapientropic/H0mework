import H0mework.Physics.DiracEvolution.WeakSpatialGalerkinMass
import H0mework.Physics.Dirac.DiracMatterHermitianEnergyIdentity
import Mathlib.Analysis.ODE.Gronwall

/-!
# Stage-nine weak Galerkin energy

The Hermitian weak mass generates a symmetric finite energy.  Testing the
finite weak equation against its own coefficient converts its derivative to
the mass-coefficient variation minus twice the action-owned stiffness.  A
single form-level rate constant therefore yields the same Grönwall estimate
for every finite mode carrier to which that constant applies.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterWeakGalerkinEnergy

open Metric Set
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracMatterGalerkinEvolution
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterHermitianEnergyIdentity
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakSpatialGalerkinMass
open scoped ComplexOrder

noncomputable section

set_option autoImplicit false

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

theorem diracExteriorMatterEnergyPairing_symm
    (matrix : DiracMatrix)
    (hermitian : Matrix.IsHermitian matrix)
    (first second : DiracExteriorMatterCarrier) :
    diracExteriorMatterEnergyPairing matrix first second =
      diracExteriorMatterEnergyPairing matrix second first := by
  unfold diracExteriorMatterEnergyPairing
  have equality := congrArg Complex.re
    (diracExteriorMatterCoordinatePairing_action_star
      matrix hermitian first second)
  simpa using equality

variable {modeCount : ℕ}

theorem diracMatterWeakMassFormValue_symm
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (hermitian : ∀ space, Matrix.IsHermitian (matrix space))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassFormValue matrix basis first second =
      diracMatterWeakMassFormValue matrix basis second first := by
  unfold diracMatterWeakMassFormValue
  apply MeasureTheory.integral_congr_ae
  filter_upwards with space
  unfold diracMatterWeakMassDensity
  exact diracExteriorMatterEnergyPairing_symm
    (matrix space) (hermitian space) _ _

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def galerkinWeakEnergy
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (time : ℝ) : ℝ :=
  massForm time (coefficient time) (coefficient time)

def galerkinWeakEnergyRate
    (massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (time : ℝ) : ℝ :=
  massDerivative time (coefficient time) (coefficient time) -
    2 * stiffnessForm time (coefficient time) (coefficient time)

def galerkinWeakTestPairing
    (massForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (test : H)
    (time : ℝ) : ℝ :=
  massForm time (coefficient time) test

def galerkinWeakTestPairingRate
    (massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (test : H)
    (time : ℝ) : ℝ :=
  massDerivative time (coefficient time) test -
    stiffnessForm time (coefficient time) test

/-- Testing the generated finite weak equation against one fixed coefficient
identifies the time derivative of its action-owned mass pairing. -/
theorem galerkinWeakTestPairing_hasDerivWithinAt
    (massForm massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (velocity test : H)
    (set : Set ℝ)
    (time : ℝ)
    (massHasDeriv : HasDerivWithinAt massForm (massDerivative time) set time)
    (coefficientHasDeriv : HasDerivWithinAt coefficient velocity set time)
    (weakEquation :
      massForm time velocity test +
        stiffnessForm time (coefficient time) test = 0) :
    HasDerivWithinAt (galerkinWeakTestPairing massForm coefficient test)
      (galerkinWeakTestPairingRate massDerivative stiffnessForm coefficient
        test time)
      set time := by
  have firstApplication := massHasDeriv.clm_apply coefficientHasDeriv
  have testDerivative : HasDerivWithinAt (fun _candidateTime : ℝ ↦ test) 0
      set time := (hasDerivAt_const time test).hasDerivWithinAt
  have fullDerivative := firstApplication.clm_apply testDerivative
  have velocityPairing :
      massForm time velocity test =
        -stiffnessForm time (coefficient time) test := by
    linarith [weakEquation]
  have derivativeValue :
      ((massDerivative time (coefficient time) + massForm time velocity) test +
        massForm time (coefficient time) 0) =
        galerkinWeakTestPairingRate massDerivative stiffnessForm coefficient
          test time := by
    simp only [add_apply, map_zero, add_zero]
    rw [velocityPairing]
    rfl
  change HasDerivWithinAt
    (fun candidateTime ↦
      massForm candidateTime (coefficient candidateTime) test)
    (galerkinWeakTestPairingRate massDerivative stiffnessForm coefficient test
      time)
    set time
  exact fullDerivative.congr_deriv derivativeValue

theorem galerkinWeakEnergy_hasDerivWithinAt
    (massForm massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (velocity : H)
    (set : Set ℝ)
    (time : ℝ)
    (massHasDeriv : HasDerivWithinAt massForm (massDerivative time) set time)
    (coefficientHasDeriv : HasDerivWithinAt coefficient velocity set time)
    (massSymmetric : ∀ first second,
      massForm time first second = massForm time second first)
    (weakEquation :
      massForm time velocity (coefficient time) +
        stiffnessForm time (coefficient time) (coefficient time) = 0) :
    HasDerivWithinAt (galerkinWeakEnergy massForm coefficient)
      (galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time)
      set time := by
  have firstApplication := massHasDeriv.clm_apply coefficientHasDeriv
  have fullDerivative := firstApplication.clm_apply coefficientHasDeriv
  have velocityPairing :
      massForm time velocity (coefficient time) =
        -stiffnessForm time (coefficient time) (coefficient time) := by
    linarith [weakEquation]
  have derivativeValue :
      ((massDerivative time (coefficient time) + massForm time velocity)
          (coefficient time) +
        massForm time (coefficient time) velocity) =
        galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time := by
    simp only [add_apply]
    rw [massSymmetric (coefficient time) velocity, velocityPairing]
    unfold galerkinWeakEnergyRate
    ring
  change HasDerivWithinAt
    (fun candidateTime =>
      massForm candidateTime (coefficient candidateTime)
        (coefficient candidateTime))
    (galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time)
    set time
  exact fullDerivative.congr_deriv derivativeValue

theorem galerkinWeakEnergy_norm_le_of_modeUniformRate
    (massForm massDerivative : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (stiffnessForm : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (coefficient : ℝ → H)
    (velocity : ℝ → H)
    (a b K : ℝ)
    (massHasDeriv : ∀ time ∈ Set.Ico a b,
      HasDerivWithinAt massForm (massDerivative time) (Set.Ici time) time)
    (coefficientHasDeriv : ∀ time ∈ Set.Ico a b,
      HasDerivWithinAt coefficient (velocity time) (Set.Ici time) time)
    (massSymmetric : ∀ time ∈ Set.Ico a b, ∀ first second,
      massForm time first second = massForm time second first)
    (weakEquation : ∀ time ∈ Set.Ico a b,
      massForm time (velocity time) (coefficient time) +
        stiffnessForm time (coefficient time) (coefficient time) = 0)
    (energyContinuous :
      ContinuousOn (galerkinWeakEnergy massForm coefficient) (Set.Icc a b))
    (rateBound : ∀ time ∈ Set.Ico a b,
      ‖galerkinWeakEnergyRate massDerivative stiffnessForm coefficient time‖ ≤
        K * ‖galerkinWeakEnergy massForm coefficient time‖) :
    ∀ time ∈ Set.Icc a b,
      ‖galerkinWeakEnergy massForm coefficient time‖ ≤
        ‖galerkinWeakEnergy massForm coefficient a‖ *
          Real.exp (K * (time - a)) := by
  intro time timeMem
  have estimate :=
    norm_le_gronwallBound_of_norm_deriv_right_le
      (f := galerkinWeakEnergy massForm coefficient)
      (f' := galerkinWeakEnergyRate massDerivative stiffnessForm coefficient)
      (δ := ‖galerkinWeakEnergy massForm coefficient a‖)
      (K := K) (ε := 0)
      energyContinuous
      (fun candidate candidateMem =>
        galerkinWeakEnergy_hasDerivWithinAt massForm massDerivative stiffnessForm
          coefficient (velocity candidate) (Set.Ici candidate) candidate
          (massHasDeriv candidate candidateMem)
          (coefficientHasDeriv candidate candidateMem)
          (massSymmetric candidate candidateMem)
          (weakEquation candidate candidateMem))
      (le_refl _)
      (fun candidate candidateMem => by
        simpa using rateBound candidate candidateMem)
  simpa [gronwallBound_ε0] using estimate time timeMem

/-- Compact coefficient control generates one quadratic energy-rate constant
before any finite mode carrier is selected. -/
theorem exists_modeUniformQuadraticRateBound
    {X : Type*}
    [TopologicalSpace X]
    [FiniteDimensional ℝ H] [Nontrivial H]
    (carrier : Set X)
    (carrierCompact : IsCompact carrier)
    (carrierNonempty : carrier.Nonempty)
    (energy rate : X → H → ℝ)
    (energyContinuous : Continuous fun input : X × H ↦
      energy input.1 input.2)
    (rateContinuous : Continuous fun input : X × H ↦
      rate input.1 input.2)
    (energyPositive : ∀ point ∈ carrier, ∀ field, field ≠ 0 →
      0 < energy point field)
    (energy_smul : ∀ point (parameter : ℝ) field,
      energy point (parameter • field) = parameter ^ 2 * energy point field)
    (rate_smul : ∀ point (parameter : ℝ) field,
      rate point (parameter • field) = parameter ^ 2 * rate point field) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ point ∈ carrier, ∀ field,
      ‖rate point field‖ ≤ K * energy point field := by
  let unitCarrier : Set (X × H) := carrier ×ˢ sphere (0 : H) 1
  have unitCarrierCompact : IsCompact unitCarrier :=
    carrierCompact.prod (isCompact_sphere (0 : H) 1)
  have sphereNonempty : (sphere (0 : H) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have unitCarrierNonempty : unitCarrier.Nonempty :=
    carrierNonempty.prod sphereNonempty
  obtain ⟨minimumPoint, minimumPointMem, minimumPointLower⟩ :=
    unitCarrierCompact.exists_isMinOn unitCarrierNonempty
      energyContinuous.continuousOn
  obtain ⟨maximumPoint, maximumPointMem, maximumPointUpper⟩ :=
    unitCarrierCompact.exists_isMaxOn unitCarrierNonempty
      rateContinuous.norm.continuousOn
  let lower := energy minimumPoint.1 minimumPoint.2
  let upper := ‖rate maximumPoint.1 maximumPoint.2‖
  have minimumNorm : ‖minimumPoint.2‖ = 1 := by
    simpa [unitCarrier, mem_sphere] using minimumPointMem.2
  have minimumNonzero : minimumPoint.2 ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at minimumNorm
    norm_num at minimumNorm
  have lowerPositive : 0 < lower :=
    energyPositive minimumPoint.1 minimumPointMem.1 minimumPoint.2
      minimumNonzero
  have upperNonnegative : 0 ≤ upper := norm_nonneg _
  refine ⟨upper / lower, div_nonneg upperNonnegative lowerPositive.le, ?_⟩
  intro point pointMem field
  by_cases fieldZero : field = 0
  · have rateZero : rate point (0 : H) = 0 := by
      simpa using rate_smul point 0 (0 : H)
    have energyZero : energy point (0 : H) = 0 := by
      simpa using energy_smul point 0 (0 : H)
    rw [fieldZero, rateZero, energyZero]
    simp
  · have normPositive : 0 < ‖field‖ := norm_pos_iff.mpr fieldZero
    let unitField : H := ‖field‖⁻¹ • field
    have unitFieldNorm : ‖unitField‖ = 1 := by
      simp [unitField, norm_smul, inv_mul_cancel₀ normPositive.ne']
    have unitFieldMem : (point, unitField) ∈ unitCarrier := by
      exact ⟨pointMem, by simpa [mem_sphere] using unitFieldNorm⟩
    have lowerBound : lower ≤ energy point unitField :=
      minimumPointLower unitFieldMem
    have upperBound : ‖rate point unitField‖ ≤ upper :=
      maximumPointUpper unitFieldMem
    have reconstruct : ‖field‖ • unitField = field := by
      rw [show ‖field‖ • unitField =
          (‖field‖ * ‖field‖⁻¹) • field by
        simp [unitField, smul_smul]]
      simp [normPositive.ne']
    have rateScale :
        rate point field = ‖field‖ ^ 2 * rate point unitField := by
      calc
        rate point field = rate point (‖field‖ • unitField) := by rw [reconstruct]
        _ = ‖field‖ ^ 2 * rate point unitField :=
          rate_smul point ‖field‖ unitField
    have energyScale :
        energy point field = ‖field‖ ^ 2 * energy point unitField := by
      calc
        energy point field = energy point (‖field‖ • unitField) := by
          rw [reconstruct]
        _ = ‖field‖ ^ 2 * energy point unitField :=
          energy_smul point ‖field‖ unitField
    calc
      ‖rate point field‖ =
          ‖field‖ ^ 2 * ‖rate point unitField‖ := by
        rw [rateScale, norm_mul, Real.norm_of_nonneg (sq_nonneg ‖field‖)]
      _ ≤ ‖field‖ ^ 2 * upper :=
        mul_le_mul_of_nonneg_left upperBound (sq_nonneg _)
      _ = (upper / lower) * (‖field‖ ^ 2 * lower) := by
        field_simp [lowerPositive.ne']
      _ ≤ (upper / lower) *
          (‖field‖ ^ 2 * energy point unitField) := by
        apply mul_le_mul_of_nonneg_left _
          (div_nonneg upperNonnegative lowerPositive.le)
        exact mul_le_mul_of_nonneg_left lowerBound (sq_nonneg _)
      _ = (upper / lower) * energy point field := by rw [energyScale]

/-- A continuous one-homogeneous readout on a compact coefficient carrier has
one norm bound before any later finite mode carrier is selected. -/
theorem exists_modeUniformLinearRateBound
    {X : Type*}
    [TopologicalSpace X]
    [FiniteDimensional ℝ H]
    (carrier : Set X)
    (carrierCompact : IsCompact carrier)
    (carrierNonempty : carrier.Nonempty)
    (rate : X → H → ℝ)
    (rateContinuous : Continuous fun input : X × H ↦
      rate input.1 input.2)
    (rate_smul : ∀ point (parameter : ℝ) field,
      rate point (parameter • field) = parameter * rate point field) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ point ∈ carrier, ∀ field,
      ‖rate point field‖ ≤ C * ‖field‖ := by
  let unitCarrier : Set (X × H) := carrier ×ˢ closedBall (0 : H) 1
  have unitCarrierCompact : IsCompact unitCarrier :=
    carrierCompact.prod (isCompact_closedBall (0 : H) 1)
  have unitCarrierNonempty : unitCarrier.Nonempty := by
    obtain ⟨point, pointMem⟩ := carrierNonempty
    exact ⟨(point, 0), pointMem, by simp⟩
  obtain ⟨maximumPoint, maximumPointMem, maximumPointUpper⟩ :=
    unitCarrierCompact.exists_isMaxOn unitCarrierNonempty
      rateContinuous.norm.continuousOn
  let C := ‖rate maximumPoint.1 maximumPoint.2‖
  have CNonnegative : 0 ≤ C := norm_nonneg _
  refine ⟨C, CNonnegative, ?_⟩
  intro point pointMem field
  by_cases fieldZero : field = 0
  · have rateZero : rate point (0 : H) = 0 := by
      simpa using rate_smul point 0 (0 : H)
    simp [fieldZero, rateZero]
  · have normPositive : 0 < ‖field‖ := norm_pos_iff.mpr fieldZero
    let unitField : H := ‖field‖⁻¹ • field
    have unitFieldNorm : ‖unitField‖ = 1 := by
      simp [unitField, norm_smul, inv_mul_cancel₀ normPositive.ne']
    have unitFieldMem : (point, unitField) ∈ unitCarrier := by
      refine ⟨pointMem, ?_⟩
      simpa [mem_closedBall, dist_eq_norm, unitFieldNorm]
    have upperBound : ‖rate point unitField‖ ≤ C :=
      maximumPointUpper unitFieldMem
    have reconstruct : ‖field‖ • unitField = field := by
      rw [show ‖field‖ • unitField =
          (‖field‖ * ‖field‖⁻¹) • field by
        simp [unitField, smul_smul]]
      simp [normPositive.ne']
    have rateScale :
        rate point field = ‖field‖ * rate point unitField := by
      calc
        rate point field = rate point (‖field‖ • unitField) := by
          rw [reconstruct]
        _ = ‖field‖ * rate point unitField :=
          rate_smul point ‖field‖ unitField
    calc
      ‖rate point field‖ = ‖field‖ * ‖rate point unitField‖ := by
        rw [rateScale, norm_mul, Real.norm_of_nonneg (norm_nonneg field)]
      _ ≤ ‖field‖ * C :=
        mul_le_mul_of_nonneg_left upperBound (norm_nonneg field)
      _ = C * ‖field‖ := mul_comm _ _

/-- A positive continuous quadratic energy on a compact carrier has one
strict coercivity constant before any later finite carrier is selected. -/
theorem exists_modeUniformQuadraticCoercivity
    {X : Type*}
    [TopologicalSpace X]
    [FiniteDimensional ℝ H] [Nontrivial H]
    (carrier : Set X)
    (carrierCompact : IsCompact carrier)
    (carrierNonempty : carrier.Nonempty)
    (energy : X → H → ℝ)
    (energyContinuous : Continuous fun input : X × H ↦
      energy input.1 input.2)
    (energyPositive : ∀ point ∈ carrier, ∀ field, field ≠ 0 →
      0 < energy point field)
    (energy_smul : ∀ point (parameter : ℝ) field,
      energy point (parameter • field) = parameter ^ 2 * energy point field) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ point ∈ carrier, ∀ field,
      κ * ‖field‖ ^ 2 ≤ energy point field := by
  let unitCarrier : Set (X × H) := carrier ×ˢ sphere (0 : H) 1
  have unitCarrierCompact : IsCompact unitCarrier :=
    carrierCompact.prod (isCompact_sphere (0 : H) 1)
  have sphereNonempty : (sphere (0 : H) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have unitCarrierNonempty : unitCarrier.Nonempty :=
    carrierNonempty.prod sphereNonempty
  obtain ⟨minimumPoint, minimumPointMem, minimumPointLower⟩ :=
    unitCarrierCompact.exists_isMinOn unitCarrierNonempty
      energyContinuous.continuousOn
  let κ := energy minimumPoint.1 minimumPoint.2
  have minimumNorm : ‖minimumPoint.2‖ = 1 := by
    simpa [unitCarrier, mem_sphere] using minimumPointMem.2
  have minimumNonzero : minimumPoint.2 ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at minimumNorm
    norm_num at minimumNorm
  have κPositive : 0 < κ :=
    energyPositive minimumPoint.1 minimumPointMem.1 minimumPoint.2
      minimumNonzero
  refine ⟨κ, κPositive, ?_⟩
  intro point pointMem field
  by_cases fieldZero : field = 0
  · have energyZero : energy point (0 : H) = 0 := by
      simpa using energy_smul point 0 (0 : H)
    rw [fieldZero, energyZero, norm_zero]
    simp
  · have normPositive : 0 < ‖field‖ := norm_pos_iff.mpr fieldZero
    let unitField : H := ‖field‖⁻¹ • field
    have unitFieldNorm : ‖unitField‖ = 1 := by
      simp [unitField, norm_smul, inv_mul_cancel₀ normPositive.ne']
    have unitFieldMem : (point, unitField) ∈ unitCarrier := by
      exact ⟨pointMem, by simpa [mem_sphere] using unitFieldNorm⟩
    have lowerBound : κ ≤ energy point unitField :=
      minimumPointLower unitFieldMem
    have reconstruct : ‖field‖ • unitField = field := by
      rw [show ‖field‖ • unitField =
          (‖field‖ * ‖field‖⁻¹) • field by
        simp [unitField, smul_smul]]
      simp [normPositive.ne']
    have energyScale :
        energy point field = ‖field‖ ^ 2 * energy point unitField := by
      calc
        energy point field = energy point (‖field‖ • unitField) := by
          rw [reconstruct]
        _ = ‖field‖ ^ 2 * energy point unitField :=
          energy_smul point ‖field‖ unitField
    calc
      κ * ‖field‖ ^ 2 = ‖field‖ ^ 2 * κ := by ring
      _ ≤ ‖field‖ ^ 2 * energy point unitField :=
        mul_le_mul_of_nonneg_left lowerBound (sq_nonneg _)
      _ = energy point field := energyScale.symm

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterWeakGalerkinEnergy
