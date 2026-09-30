import H0mework.Versions.X.NavierStokes.HigherTreeOctic.InitialShift
import H0mework.Versions.X.NavierStokes.HigherTreeOctic.L1Response

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator

namespace NativeUnheatedTreeHeatGrowth
open NativeUnheatedTreeRieszKernel (Wave)
open NativeUnheatedTreeHeatTopology NativeUnheatedTreeHeatEvaluation

/-- The output wave read back by adding every leaf wave of one tree. -/
def total : (tree : Tree) → (Leaf tree → Wave) → Wave
  | .leaf, read => read PUnit.unit
  | .fork left right, read => total left (fun leaf => read (.inl leaf)) + total right (fun leaf => read (.inr leaf))

theorem total_wave (tree : Tree) (k : Wave) (index : Index tree) : total tree (wave tree k index) = k := by
  induction tree generalizing k with
  | leaf => rfl
  | fork left right leftProof rightProof =>
    change total left (wave left index.1 index.2.1) + total right (wave right (k-index.1) index.2.2) = k
    rw [leftProof, rightProof]
    abel

theorem wave_injective (tree : Tree) (k : Wave) : Function.Injective (wave tree k) := by
  induction tree generalizing k with
  | leaf =>
    intro first last _
    cases first
    cases last
    rfl
  | fork left right leftProof rightProof =>
    intro first last same
    have leftSame : wave left first.1 first.2.1 = wave left last.1 last.2.1 :=
      funext fun leaf => congrFun same (.inl leaf)
    have split : first.1 = last.1 := by
      rw [← total_wave left first.1 first.2.1, ← total_wave left last.1 last.2.1, leftSame]
    have rightSame : wave right (k-first.1) first.2.2 = wave right (k-last.1) last.2.2 :=
      funext fun leaf => congrFun same (.inr leaf)
    rw [split] at leftSame rightSame
    exact Prod.ext split (Prod.ext (leftProof last.1 leftSame) (rightProof (k-last.1) rightSame))

end NativeUnheatedTreeHeatGrowth

namespace NativeUnheatedTreeHeatPacket
open NativeUnheatedTreeRieszKernel (Wave)

theorem nodes_injective {nu : Viscosity} {n : ℕ} {I : Type}
    {nodes : Wave → I → Fin (n+1) → NativeUnheatedTreeTime.Slot} {raw : Wave → I → ℂ}
    (paid : Alignment nu nodes raw) (k : Wave) {first last : I}
    (same : ∀ number, (nodes k first number).1 = (nodes k last number).1) : first = last := by
  apply (paid.indices k).injective
  apply NativeUnheatedTreeHeatGrowth.wave_injective paid.tree k
  funext leaf
  obtain ⟨number, rfl⟩ := paid.order.surjective leaf
  rw [paid.wave_at, paid.wave_at, same]

end NativeUnheatedTreeHeatPacket

namespace NativeUnheatedOcticGramDual
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open RationalVorticityEvaluator.ButterflyStackedExpansionMaterial
open NativeUnheatedTreeTime
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem lp_single_pythagoras {ι α E : Type*} [DecidableEq α] [NormedAddCommGroup E]
    (family : Finset ι) (index : ι → α) (value : ι → E) (distinct : Set.InjOn index family) :
    ‖∑ e ∈ family, (lp.single 2 (index e) (value e) : lp (fun _ : α => E) 2)‖^2 =
      ∑ e ∈ family, ‖value e‖^2 := by
  rcases family.eq_empty_or_nonempty with empty | ⟨start, _⟩
  · simp [empty]
  have : Nonempty ι := ⟨start⟩
  have back (e : ι) (inside : e ∈ family) : Function.invFunOn index (family : Set ι) (index e) = e :=
    distinct.leftInvOn_invFunOn inside
  have vectors : ∑ e ∈ family, (lp.single 2 (index e) (value e) : lp (fun _ : α => E) 2) =
      ∑ w ∈ family.image index, lp.single 2 w (value (Function.invFunOn index (family : Set ι) w)) := by
    rw [Finset.sum_image distinct]
    exact Finset.sum_congr rfl fun e inside => by rw [back e inside]
  have norms : ∑ e ∈ family, ‖value e‖^2 =
      ∑ w ∈ family.image index, ‖value (Function.invFunOn index (family : Set ι) w)‖^2 := by
    rw [Finset.sum_image distinct]
    exact Finset.sum_congr rfl fun e inside => by rw [back e inside]
  have paid := lp.norm_sum_single (E := fun _ : α => E) (p := 2) (by norm_num)
    (fun w => value (Function.invFunOn index (family : Set ι) w)) (family.image index)
  rw [vectors, norms]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using paid

theorem velocity_le_budget {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    ‖NativeUnheatedTriadRows.velocity seed time wave coordinate‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  rw [NativeUnheatedTriadRows.velocity_original]
  calc _ ≤ ‖NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave‖ :=
        norm_le_pi_norm _ coordinate
    _ ≤ ‖NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst‖ :=
        lp.norm_apply_le_norm (by norm_num) _ wave
    _ ≤ ‖(NativeUnifiedCompleteSource.source seed time).fst‖ :=
        NativeEndpointVelocityCarrier.wholeVelocity_norm_le _
    _ ≤ _ := NativeUnheatedSourceWeightedTail.velocity_bound seed time

theorem product_le_budget {nu : Viscosity} {n : ℕ} (seed : GeneratedWholeRestartCurrent nu)
    (slots : Fin n → Slot) (time : ℝ) :
    ‖product seed slots time‖ ≤ NativeUnifiedCompleteSource.budget seed^n := by
  unfold product
  rw [norm_prod]
  calc ∏ number, ‖NativeUnheatedTriadRows.velocity seed time (slots number).1 (slots number).2‖ ≤
        ∏ _number : Fin n, NativeUnifiedCompleteSource.budget seed :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun number _ => velocity_le_budget seed time _ _)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem budget_nonnegative {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) :
    0 ≤ NativeUnifiedCompleteSource.budget seed :=
  (norm_nonneg _).trans (NativeUnheatedSourceWeightedTail.velocity_bound seed 0)

variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

/-- The seven actual slot frequencies of one complete Gram address. -/
def code (entry : Address) : Fin 7 → IntegerWavevector :=
  fun number => (slots slot leaf position newest i j outside l m p q r s u v selected b entry number).1

theorem code_sum (entry : Address) :
    ∑ number, code slot leaf position newest i j outside l m p q r s u v selected b entry number =
      entry.1-entry.2.2 :=
  slots_frequency slot leaf position newest i j outside l m p q r s u v selected b entry

/-- The Gram inside wave and the seven slot frequencies recover the whole original address. -/
theorem entry_injective {first last : Address} (inside : first.2.2 = last.2.2)
    (same : code slot leaf position newest i j outside l m p q r s u v selected b first =
      code slot leaf position newest i j outside l m p q r s u v selected b last) : first = last := by
  have output : first.1 = last.1 := by
    have paid := congrArg (fun read : Fin 7 → IntegerWavevector => ∑ number, read number) same
    simp only [code_sum] at paid
    rw [inside] at paid
    exact sub_left_injective paid
  have waves (number : Fin 7) :
      (nodes slot leaf position newest i j outside l m p q r s u v first number).1 =
        (nodes slot leaf position newest i j outside l m p q r s u v last number).1 := by
    by_cases chosen : number = selected
    · subst chosen
      have paid := congrFun same 0
      simp only [code, slots, Fin.cons_zero, other] at paid
      rw [inside] at paid
      exact sub_left_injective paid
    · obtain ⟨small, rfl⟩ := Fin.exists_succAbove_eq chosen
      have paid := congrFun same small.succ
      simpa only [code, slots, Fin.cons_succ] using paid
  have index : first.2.1 = last.2.1 := by
    apply NativeUnheatedTreeHeatPacket.nodes_injective
      (NativeUnheatedSepticAlignment.septic butterflyGainViscosity slot leaf position newest i j i outside
        l m p q r s u v) first.1
    intro number
    have paid := waves number
    simp only [nodes, NativeUnheatedOcticEightRows.parent] at paid
    rw [← output] at paid
    exact paid
  exact Prod.ext output (Prod.ext index inside)

/-- The finite table of original zero-time slot frequencies. -/
def initialCodes : Finset (Fin 7 → IntegerWavevector) :=
  Fintype.piFinset fun _ : Fin 7 => butterflyFirstStackModes

theorem mem_initialCodes (f : Fin 7 → IntegerWavevector) :
    f ∈ initialCodes ↔ ∀ number, f number ∈ butterflyFirstStackModes := by
  unfold initialCodes
  exact Fintype.mem_piFinset

/-- One address-free cap for a single original initial Gram fibre. -/
def initialScale : ℝ :=
  NativeUnifiedCompleteSource.budget stackedShortCurrent^7 *
    ((2*Real.pi)⁻¹ * (2*NativeUnheatedTreeHeatTopology.factor butterflyGainViscosity)^6 *
      (NativeUnheatedTreeLocalHeat.cap butterflyGainViscosity * (2*Real.pi)))

/-- The complete initial Gram cap, independent of every address and observation set. -/
def initialCap : ℝ := (initialCodes.card : ℝ) * initialScale

theorem initialScale_nonnegative : 0 ≤ initialScale := by
  have budget0 := budget_nonnegative stackedShortCurrent
  unfold initialScale
  positivity [NativeUnheatedTreeHeatTopology.factor_positive butterflyGainViscosity,
    NativeUnheatedTreeLocalHeat.cap_positive butterflyGainViscosity]

theorem initialCap_nonnegative : 0 ≤ initialCap :=
  mul_nonneg (Nat.cast_nonneg _) initialScale_nonnegative

/-- The zero-time coefficient of one original Gram address inside its inside-wave slot. -/
def initialContent (test : Test) (entry : Address) : NativeUnheatedOcticGramDualPulse.Pulse :=
  product stackedShortCurrent (slots slot leaf position newest i j outside l m p q r s u v selected b entry) 0 •
    (constant (nu := butterflyGainViscosity) slot leaf position newest i j response outside l m p q r s u v
        selected a b test entry •
      NativeUnheatedOcticGramDualPulse.pulse (nu := butterflyGainViscosity)
        (rest (nu := butterflyGainViscosity) slot leaf position newest i j outside l m p q r s u v selected entry)
        (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected entry)
        (other slot leaf position newest i j outside l m p q r s u v selected entry))

theorem initial_term (test : Test) (entry : Address) :
    product stackedShortCurrent (slots slot leaf position newest i j outside l m p q r s u v selected b entry) 0 •
      basis (nu := butterflyGainViscosity) slot leaf position newest i j response outside l m p q r s u v
        selected a b test entry =
      lp.single 2 entry.2.2
        (initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry) :=
  (lp.single_smul 2 entry.2.2 _ _).symm

theorem initialContent_bound (test : Test) (entry : Address) :
    ‖initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖ ≤
      initialScale * ‖test entry.1‖ := by
  have basisBound := basis_upper (nu := butterflyGainViscosity) slot leaf position newest i j response outside
    l m p q r s u v selected a b test entry
  rw [basis, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), oldCap_eq] at basisBound
  unfold initialContent
  rw [norm_smul]
  calc _ ≤ NativeUnifiedCompleteSource.budget stackedShortCurrent^7 *
        (‖test entry.1‖ * ((2*Real.pi)⁻¹ * (2*NativeUnheatedTreeHeatTopology.factor butterflyGainViscosity)^6) *
          (NativeUnheatedTreeLocalHeat.cap butterflyGainViscosity * (2*Real.pi))) :=
        mul_le_mul (product_le_budget _ _ _) basisBound (norm_nonneg _)
          (pow_nonneg (budget_nonnegative stackedShortCurrent) 7)
    _ = _ := by unfold initialScale; ring

theorem initial_product_zero (entry : Address)
    (outsideCodes : code slot leaf position newest i j outside l m p q r s u v selected b entry ∉ initialCodes) :
    product stackedShortCurrent (slots slot leaf position newest i j outside l m p q r s u v selected b entry) 0 = 0 := by
  by_contra nonzero
  apply outsideCodes
  rw [mem_initialCodes]
  intro number
  by_contra missing
  exact nonzero (original_product_zero _ number missing)

theorem vector_initial_supported (test : Test) (observed : Finset Address) :
    vector slot leaf position newest i j response outside l m p q r s u v selected a b test
        stackedShortCurrent observed 0 =
      ∑ entry ∈ observed with
          code slot leaf position newest i j outside l m p q r s u v selected b entry ∈ initialCodes,
        lp.single 2 entry.2.2
          (initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry) := by
  rw [vector_source, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases member : code slot leaf position newest i j outside l m p q r s u v selected b entry ∈ initialCodes
  · rw [if_pos member]
    exact initial_term slot leaf position newest i j response outside l m p q r s u v selected a b test entry
  · rw [if_neg member, initial_product_zero slot leaf position newest i j outside l m p q r s u v selected b entry
      member, zero_smul]

/-- One fixed-code fibre is an orthogonal family indexed by distinct outputs. -/
theorem initial_fiber_bound (test : Test) (family : Finset Address) (f : Fin 7 → IntegerWavevector)
    (fiberCode : ∀ entry ∈ family, code slot leaf position newest i j outside l m p q r s u v selected b entry = f) :
    ‖∑ entry ∈ family, (lp.single 2 entry.2.2
        (initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry) :
          NativeUnheatedOcticGramDualPulse.Space)‖ ≤
      initialScale * ‖test‖ := by
  have insideInj : Set.InjOn (fun entry : Address => entry.2.2) family := by
    intro first firstMember last lastMember same
    exact entry_injective slot leaf position newest i j outside l m p q r s u v selected b same
      ((fiberCode first firstMember).trans (fiberCode last lastMember).symm)
  have outputInj : Set.InjOn (fun entry : Address => entry.1) family := by
    intro first firstMember last lastMember same
    have firstSum := code_sum slot leaf position newest i j outside l m p q r s u v selected b first
    have lastSum := code_sum slot leaf position newest i j outside l m p q r s u v selected b last
    rw [fiberCode first firstMember] at firstSum
    rw [fiberCode last lastMember] at lastSum
    have inside : first.2.2 = last.2.2 := by
      have paid := firstSum.symm.trans lastSum
      have sameOutput : first.1 = last.1 := same
      rw [sameOutput] at paid
      exact sub_right_injective paid
    exact entry_injective slot leaf position newest i j outside l m p q r s u v selected b inside
      ((fiberCode first firstMember).trans (fiberCode last lastMember).symm)
  have pythagoras := lp_single_pythagoras family (fun entry : Address => entry.2.2)
    (initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test) insideInj
  have imageSum : ∑ k ∈ family.image (fun entry : Address => entry.1), ‖test k‖^2 =
      ∑ entry ∈ family, ‖test entry.1‖^2 :=
    Finset.sum_image (f := fun k => ‖test k‖^2) outputInj
  have testSum : ∑ entry ∈ family, ‖test entry.1‖^2 ≤ ‖test‖^2 := by
    rw [← imageSum]
    have paid := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) test
      (family.image fun entry : Address => entry.1)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using paid
  have squares : ‖∑ entry ∈ family, (lp.single 2 entry.2.2
        (initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry) :
          NativeUnheatedOcticGramDualPulse.Space)‖^2 ≤
      (initialScale * ‖test‖)^2 := by
    rw [pythagoras]
    calc ∑ entry ∈ family,
          ‖initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry‖^2 ≤
          ∑ entry ∈ family, initialScale^2 * ‖test entry.1‖^2 := by
          apply Finset.sum_le_sum
          intro entry _
          calc _ ≤ (initialScale * ‖test entry.1‖)^2 :=
                pow_le_pow_left₀ (norm_nonneg _)
                  (initialContent_bound slot leaf position newest i j response outside l m p q r s u v
                    selected a b test entry) 2
            _ = _ := by ring
      _ = initialScale^2 * ∑ entry ∈ family, ‖test entry.1‖^2 := by rw [Finset.mul_sum]
      _ ≤ initialScale^2 * ‖test‖^2 := mul_le_mul_of_nonneg_left testSum (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg initialScale_nonnegative (norm_nonneg _)) two_ne_zero).mp squares

/-- Every finite code table carrying the zero-time support pays the fibres one by one. -/
theorem supported_fiber_bound (test : Test) (observed : Finset Address) (T : Finset (Fin 7 → IntegerWavevector)) :
    ‖∑ entry ∈ observed with code slot leaf position newest i j outside l m p q r s u v selected b entry ∈ T,
        (lp.single 2 entry.2.2
          (initialContent slot leaf position newest i j response outside l m p q r s u v selected a b test entry) :
            NativeUnheatedOcticGramDualPulse.Space)‖ ≤ (T.card : ℝ) * (initialScale * ‖test‖) := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := T) (g := code slot leaf position newest i j outside l m p q r s u v selected b)
    (fun entry member => (Finset.mem_filter.mp member).2)]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _f ∈ T, initialScale * ‖test‖ := by
        apply Finset.sum_le_sum
        intro f _
        apply initial_fiber_bound slot leaf position newest i j response outside l m p q r s u v selected a b test _ f
        intro entry member
        exact (Finset.mem_filter.mp member).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The complete original initial Gram vector is uniformly bounded over every finite observation. -/
theorem vector_initial_bound (test : Test) (observed : Finset Address) :
    ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test
        stackedShortCurrent observed 0‖ ≤ initialCap * ‖test‖ := by
  rw [vector_initial_supported, initialCap, mul_assoc]
  exact supported_fiber_bound slot leaf position newest i j response outside l m p q r s u v selected a b
    test observed initialCodes

/-- The original L¹ response now starts from the uniform complete initial Gram cap. -/
theorem vector_initial_response (test : Test) (observed : Finset Address) (time : ℝ) (nonnegative : 0 ≤ time) :
    ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test
        stackedShortCurrent observed time‖ ≤
      initialCap * ‖test‖ + 2 * ∫ t in (0 : ℝ)..time,
        ‖forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test
          stackedShortCurrent observed t‖ := by
  have growth := vector_l1_bound slot leaf position newest i j response outside l m p q r s u v selected a b
    test stackedShortCurrent observed 0 time le_rfl nonnegative nonnegative
  have initial := vector_initial_bound slot leaf position newest i j response outside l m p q r s u v selected a b
    test observed
  linarith

/-- The original Φ₈−bare pairing consumes the uniform initial cap and the actual forcing work. -/
theorem pairing_initial_response (test : Test) (observed : Finset Address) (time : ℝ) (nonnegative : 0 ≤ time) :
    ‖original slot leaf position newest i j response outside l m p q r s u v selected a b test
        stackedShortCurrent observed time -
      bare slot leaf position newest i j response outside l m p q r s u v selected a b test
        stackedShortCurrent observed time‖^2 ≤
      NativeUnifiedCompleteSource.budget stackedShortCurrent^2 *
        (initialCap * ‖test‖ + 2 * ∫ t in (0 : ℝ)..time,
          ‖forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test
            stackedShortCurrent observed t‖)^2 := by
  have paid := pairing_bound slot leaf position newest i j response outside l m p q r s u v selected a b test
    stackedShortCurrent observed time
  rw [work] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _)
      (vector_initial_response slot leaf position newest i j response outside l m p q r s u v selected a b
        test observed time nonnegative) 2) (sq_nonneg _))

end
end NativeUnheatedOcticGramDual
end SaturationMonoid.NavierStokes
