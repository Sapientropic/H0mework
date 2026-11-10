import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderJetProlongation

/-!
# Fixed P506/L0 closed all-order matter energy estimate

The mother-action forcing at every selected hierarchy order is controlled by
the same complete spatial jet.  Uniform pointwise coercivity therefore absorbs
the entire forcing budget into the whole-order energy and closes the rate
estimate without introducing a higher-order jet.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyClosure

open Set
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedEnergyRate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedVolterraEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderJetProlongation
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderVolterraEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyRate
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open ProofFreeRicherAnholonomicSource

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

local instance allOrderClosureMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance fixedMatterSpatialWordIndexNonempty (order : ℕ) :
    Nonempty (FixedMatterSpatialWordIndex order) :=
  ⟨⟨⟨0, Nat.succ_pos order⟩, fun index => Fin.elim0 index⟩⟩

private def FixedMatterSpatialWordIndex.embed
    {lower upper : ℕ}
    (order : lower ≤ upper)
    (word : FixedMatterSpatialWordIndex lower) :
    FixedMatterSpatialWordIndex upper :=
  ⟨⟨word.1.1, lt_of_lt_of_le word.1.2 (Nat.succ_le_succ order)⟩,
    word.2⟩

@[simp] private theorem FixedMatterSpatialWordIndex.toList_embed
    {lower upper : ℕ}
    (order : lower ≤ upper)
    (word : FixedMatterSpatialWordIndex lower) :
    (FixedMatterSpatialWordIndex.embed order word).toList = word.toList := by
  rfl

private theorem fixedMatterSpatialJetAt_norm_mono
    {lower upper : ℕ}
    (order : lower ≤ upper)
    (field : BasePoint → MatterCoordinateCarrier)
    (point : BasePoint) :
    ‖fixedMatterSpatialJetAt lower field point‖ ≤
      ‖fixedMatterSpatialJetAt upper field point‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (norm_nonneg (fixedMatterSpatialJetAt upper field point))).2
  intro word
  change ‖fixedSpatialWordDerivative word.toList field point‖ ≤ _
  rw [← FixedMatterSpatialWordIndex.toList_embed order word]
  exact norm_le_pi_norm
    (fixedMatterSpatialJetAt upper field point)
    (FixedMatterSpatialWordIndex.embed order word)

private theorem matterCoordinateFiberCoefficientCLM_norm
    (coordinates : MatterCoordinateCarrier) :
    ‖matterCoordinateFiberCoefficientCLM coordinates‖ = ‖coordinates‖ := by
  rw [PiLp.norm_eq_sum (by norm_num)]
  rw [PiLp.norm_eq_sum (by norm_num)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp [matterCoordinateFiberCoefficientCLM,
    matterCoordinateFiberCoefficientLinear]

theorem fixedCoordinatePointwiseEnergy_coerciveOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ time ∈ Icc timeStart timeEnd,
        ∀ space ∈ Icc a b,
          ∀ coordinates : MatterCoordinateCarrier,
            κ * ‖coordinates‖ ^ 2 ≤
              fixedCoordinatePointwiseEnergy time space coordinates := by
  let carrier : Set (ℝ × DiracMatterSpatialCoordinates) :=
    Icc timeStart timeEnd ×ˢ Icc a b
  have carrierCompact : IsCompact carrier :=
    isCompact_Icc.prod isCompact_Icc
  have carrierNonempty : carrier.Nonempty :=
    ⟨(timeStart, a), ⟨⟨le_rfl, timeOrder⟩, ⟨le_rfl, boxOrder⟩⟩⟩
  obtain ⟨κ, κPositive, coercivity⟩ :=
    exists_fixedModeUniformPointwiseEnergyCoercivity
      carrier carrierCompact carrierNonempty
  refine ⟨κ, κPositive, ?_⟩
  intro time timeMem space spaceMem coordinates
  have bound := coercivity (time, space) ⟨timeMem, spaceMem⟩
    (matterCoordinateFiberCoefficientCLM coordinates)
  rwa [matterCoordinateFiberCoefficientCLM_norm] at bound

theorem fixedMatterSpatialJet_norm_sq_le_energy
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (κ : ℝ)
    (κNonnegative : 0 ≤ κ)
    (coercivity : ∀ coordinates : MatterCoordinateCarrier,
      κ * ‖coordinates‖ ^ 2 ≤
        fixedCoordinatePointwiseEnergy time space coordinates) :
    κ * ‖fixedMatterSpatialJetAt order field
        (diracMatterSpacetimeCoordinatePoint time space)‖ ^ 2 ≤
      fixedMatterAllOrderPointwiseEnergy order field time space := by
  let jet := fixedMatterSpatialJetAt order field
    (diracMatterSpacetimeCoordinatePoint time space)
  obtain ⟨word, wordNorm⟩ := (IsGreatest.pi_norm jet).1
  have wordCoercivity := coercivity (jet word)
  have wordMem : word ∈ (Finset.univ : Finset (FixedMatterSpatialWordIndex order)) :=
    Finset.mem_univ word
  change κ * ‖jet‖ ^ 2 ≤ _
  calc
    κ * ‖jet‖ ^ 2 = κ * ‖jet word‖ ^ 2 := by
      exact congrArg (fun value : ℝ => κ * value ^ 2) wordNorm.symm
    _ ≤ fixedCoordinatePointwiseEnergy time space (jet word) := wordCoercivity
    _ ≤ ∑ candidate : FixedMatterSpatialWordIndex order,
        fixedCoordinatePointwiseEnergy time space (jet candidate) := by
      exact Finset.single_le_sum
        (fun candidate _ =>
          (mul_nonneg κNonnegative (sq_nonneg ‖jet candidate‖)).trans
            (coercivity (jet candidate)))
        wordMem
    _ = fixedMatterAllOrderPointwiseEnergy order field time space := by
      rfl

theorem exists_fixedMatterAllOrderPointwiseForcingBudgetAbsorptionOnBox
    (order : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ κ L : ℝ, 0 < κ ∧ 0 ≤ L ∧
      ∀ (field : BasePoint → MatterCoordinateCarrier),
        ContDiff ℝ ∞ field →
        (∀ point,
          matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            field point = 0) →
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            κ * fixedMatterAllOrderPointwiseForcingBudget
                order field time space ≤
              L * fixedMatterAllOrderPointwiseEnergy
                order field time space := by
  obtain ⟨κ, κPositive, coercivity⟩ :=
    fixedCoordinatePointwiseEnergy_coerciveOnBox
      timeStart timeEnd a b timeOrder boxOrder
  obtain ⟨inverseBound, inverseBoundNonnegative, inverseEstimate⟩ :=
    exists_fixedTemporalPrincipalInverseBoundOnBox
      timeStart timeEnd a b
  obtain ⟨forcingBound, forcingBoundNonnegative, forcingEstimate⟩ :=
    exists_fixedMatterAllOrderCommutedForcingSpatialJetBoundOnBox
      order timeStart timeEnd a b
  let L : ℝ :=
    (Fintype.card (FixedMatterSpatialWordIndex order) : ℝ) *
      (inverseBound * forcingBound) ^ 2
  refine ⟨κ, L, κPositive,
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _), ?_⟩
  intro field fieldSmooth actionZero time timeMem space spaceMem
  let point := diracMatterSpacetimeCoordinatePoint time space
  let jet := fixedMatterSpatialJetAt order field point
  have jetEnergy : κ * ‖jet‖ ^ 2 ≤
      fixedMatterAllOrderPointwiseEnergy order field time space := by
    exact fixedMatterSpatialJet_norm_sq_le_energy order field time space κ
      κPositive.le (coercivity time timeMem space spaceMem)
  have individualSquareBound (word : FixedMatterSpatialWordIndex order) :
      ‖fixedMatterAllOrderWordForcing word field time space‖ ^ 2 ≤
        (inverseBound * forcingBound) ^ 2 * ‖jet‖ ^ 2 := by
    have wordLengthLe : word.toList.length ≤ order := by
      unfold FixedMatterSpatialWordIndex.toList
      simp only [List.length_ofFn]
      exact Nat.le_of_lt_succ word.1.2
    have smallerJetBound :
        ‖fixedMatterSpatialJetAt word.toList.length field point‖ ≤
          ‖jet‖ := by
      exact fixedMatterSpatialJetAt_norm_mono wordLengthLe field point
    have commutedBound := forcingEstimate word field fieldSmooth actionZero
      time timeMem space spaceMem
    have inverseBoundAt := inverseEstimate time timeMem space spaceMem
    have forceNormBound :
        ‖fixedMatterAllOrderWordForcing word field time space‖ ≤
          (inverseBound * forcingBound) * ‖jet‖ := by
      rw [fixedMatterAllOrderWordForcing_of_actionZero word field actionZero,
        norm_neg]
      calc
        ‖fixedEvolutionTemporalPrincipalInverseCoordinateCLM point
            (fixedMatterAllOrderCommutedForcing word.toList field point)‖ ≤
            ‖fixedEvolutionTemporalPrincipalInverseCoordinateCLM point‖ *
              ‖fixedMatterAllOrderCommutedForcing word.toList field point‖ :=
          (fixedEvolutionTemporalPrincipalInverseCoordinateCLM point).le_opNorm _
        _ ≤ inverseBound *
              (forcingBound *
                ‖fixedMatterSpatialJetAt word.toList.length field point‖) := by
          exact mul_le_mul inverseBoundAt commutedBound (norm_nonneg _)
            inverseBoundNonnegative
        _ ≤ inverseBound * (forcingBound * ‖jet‖) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left smallerJetBound forcingBoundNonnegative)
            inverseBoundNonnegative
        _ = (inverseBound * forcingBound) * ‖jet‖ := by ring
    calc
      ‖fixedMatterAllOrderWordForcing word field time space‖ ^ 2 ≤
          ((inverseBound * forcingBound) * ‖jet‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (mul_nonneg inverseBoundNonnegative
            forcingBoundNonnegative) (norm_nonneg _))).2 forceNormBound
      _ = (inverseBound * forcingBound) ^ 2 * ‖jet‖ ^ 2 := by ring
  unfold fixedMatterAllOrderPointwiseForcingBudget
  calc
    κ * ∑ word : FixedMatterSpatialWordIndex order,
        ‖fixedMatterAllOrderWordForcing word field time space‖ ^ 2 ≤
        κ * ∑ _word : FixedMatterSpatialWordIndex order,
          (inverseBound * forcingBound) ^ 2 * ‖jet‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun word _ => individualSquareBound word)
        κPositive.le
    _ = L * (κ * ‖jet‖ ^ 2) := by
      simp [L]
      ring
    _ ≤ L * fixedMatterAllOrderPointwiseEnergy order field time space := by
      exact mul_le_mul_of_nonneg_left jetEnergy
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- After the all-order coefficient forcing is absorbed, the mother-action
zero fiber obeys one closed energy-rate inequality at the selected hierarchy
order.  No higher spatial jet appears on the right-hand side. -/
theorem exists_fixedMatterAllOrderClosedPointwiseRateBoundOnBox
    (order : ℕ)
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ κ K : ℝ, 0 < κ ∧ 0 ≤ K ∧
      ∀ (field : BasePoint → MatterCoordinateCarrier),
        ContDiff ℝ ∞ field →
        (∀ point,
          matterCoordinateFirstOrderOperator
            fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
            field point = 0) →
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            κ * fixedMatterAllOrderPointwiseRateMagnitude
                order field time space ≤
              K * fixedMatterAllOrderPointwiseEnergy
                order field time space := by
  obtain ⟨hierarchyBound, hierarchyBoundNonnegative, hierarchyEstimate⟩ :=
    exists_fixedMatterAllOrderPointwiseHierarchyBoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  obtain ⟨κ, forcingCoefficient, κPositive,
      forcingCoefficientNonnegative, forcingAbsorption⟩ :=
    exists_fixedMatterAllOrderPointwiseForcingBudgetAbsorptionOnBox
      order timeStart timeEnd a b timeOrder boxOrder
  refine ⟨κ, hierarchyBound * (κ + forcingCoefficient), κPositive,
    mul_nonneg hierarchyBoundNonnegative
      (add_nonneg κPositive.le forcingCoefficientNonnegative), ?_⟩
  intro field fieldSmooth actionZero time timeMem space spaceMem
  have rateEstimate := hierarchyEstimate order field
    time timeMem space spaceMem
  have forcingEstimate := forcingAbsorption field fieldSmooth actionZero
    time timeMem space spaceMem
  calc
    κ * fixedMatterAllOrderPointwiseRateMagnitude
          order field time space ≤
        κ * (hierarchyBound *
          (fixedMatterAllOrderPointwiseEnergy order field time space +
            fixedMatterAllOrderPointwiseForcingBudget
              order field time space)) :=
      mul_le_mul_of_nonneg_left rateEstimate κPositive.le
    _ = hierarchyBound *
        (κ * fixedMatterAllOrderPointwiseEnergy order field time space +
          κ * fixedMatterAllOrderPointwiseForcingBudget
            order field time space) := by ring
    _ ≤ hierarchyBound *
        (κ * fixedMatterAllOrderPointwiseEnergy order field time space +
          forcingCoefficient *
            fixedMatterAllOrderPointwiseEnergy order field time space) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) forcingEstimate) hierarchyBoundNonnegative
    _ = (hierarchyBound * (κ + forcingCoefficient)) *
        fixedMatterAllOrderPointwiseEnergy order field time space := by ring

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyClosure
