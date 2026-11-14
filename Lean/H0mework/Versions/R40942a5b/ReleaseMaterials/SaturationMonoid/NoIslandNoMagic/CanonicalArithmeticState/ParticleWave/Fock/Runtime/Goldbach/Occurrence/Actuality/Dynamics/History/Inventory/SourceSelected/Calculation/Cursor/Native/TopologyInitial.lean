import H0mework.Versions.R40942a5b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.Goldbach.Occurrence.Actuality.Dynamics.History.Inventory.SourceSelected.Calculation.Cursor.Native.TopologyInverse

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native

open NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
open CategoryTheory CategoryTheory.Limits CofinalAllPrimeTopology SourceGeneratedPrimePowerCompletion

local notation "A" => fun depth => SourceOperationNative.sourceAction (process depth)
local notation "B" => fun depth => NativeRecovery.backward (R.old depth) (R.origin depth) (R.reader depth)
local notation "initialPointAt" => fun depth => SourceOperationNative.point (C.mathRuntime depth 0)

/-- Both sides of the full native decomposition survive in every topology carrier. -/
theorem actual_native_topology_decomposition (depth : Nat) :
    type_of% (topology_successor_decomposition (A depth) (B depth)
      (initialCoefficient depth) (initialInclusion depth) (actual_native_action_decomposition depth)) :=
  topology_successor_decomposition (A depth) (B depth)
    (initialCoefficient depth) (initialInclusion depth) (actual_native_action_decomposition depth)

/-- The omitted initial coordinate is the entire image condition at each stage. -/
theorem actual_native_stage_image (depth : Nat) (p : Nat.Primes) (j : Nat)
    (value : StageResidual (L := FullCarrier depth) p j) :
    value ∈ Set.range (stageMap p j (A depth)) ↔
      stageMap p j (initialCoefficient depth) value = 0 := by
  constructor
  · rintro ⟨previous, rfl⟩
    obtain ⟨word, rfl⟩ := (powerRange (L := FullCarrier depth) p j).mkQ_surjective previous
    change stageMap p j (initialCoefficient depth) (stageMap p j (A depth) (stageProjection p j word)) = 0
    simp only [stage_successor_apply, actual_native_action_initial_coefficient, map_zero]
  · intro zero
    refine ⟨stageMap p j (B depth) value, ?_⟩
    have complete := stage_successor_decomposition (A depth) (B depth)
      (initialCoefficient depth) (initialInclusion depth) (actual_native_action_decomposition depth) p j value
    rwa [zero, map_zero, add_zero] at complete

/-- A coherent native successor has a predecessor exactly when its initial coefficient vanishes. -/
theorem actual_native_prime_image (depth : Nat) (value : AllPrimeCompletion (FullCarrier depth)) :
    value ∈ Set.range (allPrimeSuccessor (A depth)) ↔
      allPrimeSuccessor (initialCoefficient depth) value = 0 := by
  constructor
  · rintro ⟨previous, rfl⟩
    funext p
    apply Concrete.limit_ext (tower (L := ℤ) p)
    rintro ⟨j⟩
    change (restriction (L := ℤ) p j).hom
      ((allPrimeSuccessor (initialCoefficient depth) (allPrimeSuccessor (A depth) previous)) p) =
      (restriction (L := ℤ) p j).hom 0
    rw [map_zero]
    have restrict := (allPrime_successor_restriction (initialCoefficient depth) p j
      (allPrimeSuccessor (A depth) previous)).trans
      (congrArg (stageMap p j (initialCoefficient depth))
        (allPrime_successor_restriction (A depth) p j previous))
    exact restrict.trans ((actual_native_stage_image depth p j _).mp ⟨_, rfl⟩)
  · intro absent
    refine ⟨allPrimeSuccessor (B depth) value, ?_⟩
    have complete := (actual_native_topology_decomposition depth).2.1 value
    simpa only [absent, map_zero, add_zero] using complete

theorem actual_native_coimage_image (depth : Nat) (value : AllPrimeFaithfulCoimage (L := FullCarrier depth)) :
    value ∈ Set.range (allPrimeCoimageSuccessor (A depth)) ↔
      allPrimeCoimageSuccessor (initialCoefficient depth) value = 0 := by
  constructor
  · rintro ⟨previous, rfl⟩
    obtain ⟨word, rfl⟩ := (AllPrimeKernel (L := FullCarrier depth)).mkQ_surjective previous
    rw [allPrime_coimage_successor_source, allPrime_coimage_successor_source,
      actual_native_action_initial_coefficient, map_zero]
  · intro absent
    refine ⟨allPrimeCoimageSuccessor (B depth) value, ?_⟩
    have complete := (actual_native_topology_decomposition depth).2.2 value
    simpa only [absent, map_zero, add_zero] using complete

private theorem prime_stage_one_live (p : Nat.Primes) (j : Nat) :
    stageProjection (L := ℤ) p j 1 ≠ 0 := by
  intro erased
  obtain ⟨divided, equation⟩ := (stageProjection_eq_zero_iff p j (1 : ℤ)).mp erased
  have divides : (p.1 : ℤ)^(j+1) ∣ 1 :=
    ⟨divided, by simpa only [smul_eq_mul] using equation.symm⟩
  have bound := Int.natAbs_le_of_dvd_ne_zero divides (by norm_num : (1 : ℤ) ≠ 0)
  simp only [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_one] at bound
  exact (not_le_of_gt (one_lt_pow₀ p.property.one_lt (Nat.succ_ne_zero j))) bound

theorem actual_native_initial_outside_stage_image (depth : Nat) (p : Nat.Primes) (j : Nat) :
    stageProjection p j (initialPointAt depth) ∉ Set.range (stageMap p j (A depth)) := by
  have coeff : initialCoefficient depth (initialPointAt depth) = 1 :=
    initial_coefficient_inclusion depth 1
  rw [actual_native_stage_image, stage_successor_apply, coeff]
  exact prime_stage_one_live p j

theorem actual_native_initial_outside_prime_image (depth : Nat) :
    allPrimeMap (initialPointAt depth) ∉ Set.range (allPrimeSuccessor (A depth)) := by
  rintro ⟨previous, next⟩
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  have coordinate := congrArg (fun value : AllPrimeCompletion (FullCarrier depth) =>
    (restriction (L := FullCarrier depth) p 0).hom (value p)) next
  rw [allPrime_successor_restriction, allPrime_restriction] at coordinate
  exact actual_native_initial_outside_stage_image depth p 0 ⟨_, coordinate⟩

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
