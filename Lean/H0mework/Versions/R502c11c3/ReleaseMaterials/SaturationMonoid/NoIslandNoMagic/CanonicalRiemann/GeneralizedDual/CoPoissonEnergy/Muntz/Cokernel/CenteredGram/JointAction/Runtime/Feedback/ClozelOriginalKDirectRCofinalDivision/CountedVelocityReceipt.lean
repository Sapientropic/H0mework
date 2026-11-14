import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 160000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

open Filter BurnolPhysicalState Complex
open OriginalRieszFinitePairing.CoPoisson.Ward CountedJointStrong
open scoped Topology InnerProductSpace

open private literal_R from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity

local notation "Resolvent" => burnolDirectRightResolventCLM
local notation "Riesz" => burnolCompletedMellinRieszVector
local notation "physical" => OriginalKCombPhysicalAction.physicalProjection
local notation "exterior" => OriginalKCombPhysicalAction.physicalRemainder
local notation "nativeInput" => OriginalKCombFirstFullSourceDynamics.input

private def slotRead (kernel : BurnolL2) (pair : BurnolL2 × BurnolL2) :
    (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2) × ℂ :=
  ((physical pair.1,exterior pair.1),(physical pair.2,exterior pair.2),inner ℂ kernel (physical pair.2))

private theorem slotRead_continuous (kernel : BurnolL2) : Continuous (slotRead kernel) :=
  (((physical).continuous.comp continuous_fst).prodMk ((exterior).continuous.comp continuous_fst)).prodMk
    ((((physical).continuous.comp continuous_snd).prodMk ((exterior).continuous.comp continuous_snd)).prodMk
      ((innerSL ℂ kernel).continuous.comp ((physical).continuous.comp continuous_snd)))

private theorem slotRead_tendsto {f : Nat → BurnolL2 × BurnolL2} {input output kernel : BurnolL2}
    {old new : BurnolL2 × BurnolL2} {price : ℂ}
    (trajectory : Tendsto f atTop (𝓝 (input,output)))
    (first : (physical input,exterior input) = old)
    (second : (physical output,exterior output) = new)
    (read : inner ℂ kernel (physical output) = price) :
    Tendsto (fun m => slotRead kernel (f m)) atTop (𝓝 (old,new,price)) := by
  have moved := ((slotRead_continuous kernel).tendsto (input,output)).comp trajectory
  have data : slotRead kernel (input,output) = (old,new,price) := Prod.ext first (Prod.ext second read)
  rwa [data] at moved

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "before" => D.raw observation nontrivial half depth (ordinal+1)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "wave" => actualDivisionCompactWave observation nontrivial half depth (ordinal+1)

private theorem slots (n : Nat) :
    let y := D.raw observation nontrivial half depth (n+1)
    @Eq (BurnolL2 × BurnolL2) (physical y,exterior y)
      (nativeInput observation nontrivial half depth (n+1)) := by
  let y := D.raw observation nontrivial half depth (n+1)
  let x := D.raw observation nontrivial half depth n
  let p := OriginalKCombPhysicalAction.R observation nontrivial half x
  let split := fun value : BurnolL2 => (physical value, exterior value)
  have raw : @Eq BurnolL2 y p := D.raw_successor observation nontrivial half depth n
  exact (congrArg split raw).trans (OriginalKCombFirstFullSourceDynamics.next_pair observation nontrivial half depth n).symm

private theorem Riesz_read :
    inner ℂ (Riesz coord : BurnolL2) (physical after) =
      inner ℂ ((Resolvent coord).adjoint (Riesz coord : BurnolL2)) before := by
  let k := Riesz coord
  have actual : @Eq BurnolL2 after (Resolvent coord before) :=
    literal_R observation nontrivial half depth (ordinal+1)
  have projected := congrArg (fun value : BurnolL2 => inner ℂ (k : BurnolL2) (physical value)) actual
  exact projected.trans ((Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left k
    (Resolvent coord before)).trans (ContinuousLinearMap.adjoint_inner_left (Resolvent coord) before k).symm)

private theorem old_field_nonzero : before ≠ 0 := by
  open OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial in
  have quarter : burnolQuarterRestriction before ≠ 0 := by
    rw [actual_raw_quarter observation nontrivial half depth (ordinal+1)]
    exact smul_ne_zero (canonical_source_mean_ne observation half (ordinal+1)) (intervalConstant_ne_zero (by norm_num))
  intro zero
  exact quarter (by rw [zero, map_zero])

/-- The two-cutoff read supplies the exact original slots and independent K price. -/
theorem actual_counted_slots :
    ∃ limit : BurnolL2,
      Tendsto (fun N : Nat => (DualSource.source N after, FiniteForcing.source N wave))
        atTop (𝓝 (limit, fourierL2 limit)) ∧
      Tendsto (fun m => slotRead (Riesz coord : BurnolL2)
        (observedIncidence coord 1 (fun N => DualSource.source N after) limit m)) atTop
        (𝓝 (nativeInput observation nontrivial half depth (ordinal+1),
          nativeInput observation nontrivial half depth (ordinal+1+1),
          inner ℂ ((Resolvent coord).adjoint (Riesz coord : BurnolL2)) before)) ∧
      ∀ᶠ m : Nat in atTop,
        (observedIncidence coord 1 (fun N => DualSource.source N after) limit m).1 ≠ 0 := by
  have observed := actual_counted_incidence observation nontrivial half depth ordinal
  let limit := observed.choose
  have counted := observed.choose_spec.1
  have recovered := observed.choose_spec.2.1
  have same := slotRead_tendsto recovered (slots observation nontrivial half depth ordinal)
    (slots observation nontrivial half depth (ordinal+1)) (Riesz_read observation nontrivial half depth ordinal)
  have live := recovered.fst_nhds.eventually_ne (old_field_nonzero observation nontrivial half depth ordinal)
  exact ⟨limit,counted,same,live⟩

-- The original expanded receipt remains available to Lean without editor suggestion traversal.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_counted_division_receipt"

/-- The read closes on the original Division's actual source, relation, whole and successor. -/
theorem actual_counted_division_receipt :
    type_of% (actual_counted_slots observation nontrivial half depth ordinal) ∧
    type_of% (DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth (ordinal+1)) :=
  ⟨actual_counted_slots observation nontrivial half depth ordinal,
    DirectRDivisionControls.actual_division_action_same_root observation nontrivial half depth (ordinal+1)⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
