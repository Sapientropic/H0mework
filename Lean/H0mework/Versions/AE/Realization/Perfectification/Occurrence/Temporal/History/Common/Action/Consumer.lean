import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Root.Action
open RootLawDependentJointStateController RootLawDependentJointTransition
open CofinalHistoryTransition SourceGeneratedObservationAction SourceGeneratedActionObservationHistory
namespace R
export SourceHistoryCommon.Root (step sourceHistory targetHistory common left right)
end R
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (successor : StepLedgerSuccessorAt (R.step root visit recognition))
theorem measurement_source (value : Joint root visit recognition successor) :
    (measurement root visit recognition successor value).fst =
      (sourceExposure root visit recognition).measurement value.1 := rfl

theorem measurement_target (value : Joint root visit recognition successor) :
    (measurement root visit recognition successor value).snd =
      (targetExposure root visit recognition successor).measurement value.2 := rfl

def residual (value : Joint root visit recognition successor) : Measured H :=
  evolution root visit recognition successor (measurement root visit recognition successor value) -
    measurement root visit recognition successor (action root visit recognition successor value)

theorem source_residual (value : Joint root visit recognition successor) :
    (residual root visit recognition successor value).fst =
      (sourceExposure root visit recognition).hilbertEvolution ((sourceExposure root visit recognition).measurement value.1) -
        (sourceExposure root visit recognition).measurement ((sourceExposure root visit recognition).sourceAction.carrierAction value.1) := rfl

theorem target_residual (value : Joint root visit recognition successor) :
    (residual root visit recognition successor value).snd =
      (targetExposure root visit recognition successor).hilbertEvolution ((targetExposure root visit recognition successor).measurement value.2) -
        (targetExposure root visit recognition successor).measurement ((targetExposure root visit recognition successor).sourceAction.carrierAction value.2) := rfl

theorem pairing_original (value dual : Joint root visit recognition successor) :
    pairing root visit recognition successor value dual =
      stepSourcePairing (R.step root visit recognition) value.1 dual.1 +
      stepTargetPairing (R.step root visit recognition) successor value.2 dual.2 := rfl

theorem observation_original (value : Joint root visit recognition successor) :
    observation root visit recognition successor value =
      GeneratedTransition.completionMap (R.sourceHistory root visit recognition) (R.common root visit recognition successor)
        (R.left root visit recognition successor) value.1 +
      GeneratedTransition.completionMap (R.targetHistory root visit recognition successor) (R.common root visit recognition successor)
        (R.right root visit recognition successor) value.2 := rfl

theorem defect_exact (coordinate : LinearMap.ker (observation root visit recognition successor)) :
    defect root visit recognition successor coordinate = 0 ↔
      observation root visit recognition successor (action root visit recognition successor coordinate) = 0 :=
  actionDefect_value_zero_iff _ _ coordinate

theorem faithful_joint_action : type_of% (realization root visit recognition successor).perfectAction.canonicalMap_commutes :=
  (realization root visit recognition successor).perfectAction.canonicalMap_commutes
theorem residual_norm (value : Joint root visit recognition successor) :
    ‖residual root visit recognition successor value‖ ^ 2 =
      ‖(residual root visit recognition successor value).fst‖ ^ 2 +
        ‖(residual root visit recognition successor value).snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

theorem residual_zero_iff (value : Joint root visit recognition successor) :
    residual root visit recognition successor value = 0 ↔
      (sourceExposure root visit recognition).hilbertEvolution ((sourceExposure root visit recognition).measurement value.1) =
        (sourceExposure root visit recognition).measurement ((sourceExposure root visit recognition).sourceAction.carrierAction value.1) ∧
      (targetExposure root visit recognition successor).hilbertEvolution ((targetExposure root visit recognition successor).measurement value.2) =
        (targetExposure root visit recognition successor).measurement ((targetExposure root visit recognition successor).sourceAction.carrierAction value.2) := by
  constructor
  · intro zero
    constructor
    · exact sub_eq_zero.mp ((source_residual root visit recognition successor value).symm.trans (congrArg WithLp.fst zero))
    · exact sub_eq_zero.mp ((target_residual root visit recognition successor value).symm.trans (congrArg WithLp.snd zero))
  · rintro ⟨first,second⟩
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext
    · exact (source_residual root visit recognition successor value).trans (sub_eq_zero.mpr first)
    · exact (target_residual root visit recognition successor value).trans (sub_eq_zero.mpr second)
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value value_source trace paid_history)
end O
namespace P
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment no_refill wellFounded)
end P

theorem normal : O.value root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) =
    Finsupp.single (actualPlan root visit recognition successor) 1 :=
  (O.value_source root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).trans
    (SourceNativeBinary.lift_point _ _ _)

theorem cost : (O.trace root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).length = 3 :=
  (O.paid_history root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)).trans (by rfl)

abbrev payment (count : Fin 3) := P.activePayment root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)
  ⟨count.1, by exact count.2⟩

theorem no_refill (count : Nat) : type_of% (P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) count) :=
  P.no_refill root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor) count

theorem wellFounded : type_of% (P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)) :=
  P.wellFounded root.toAuthoritativeRoot visit.current (installedReader root visit recognition successor)

variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
theorem actual_action (count : Nat) : recoveredAction root visit recognition successor U7 calculus count = action root visit recognition successor := rfl

theorem actual_measurement (count : Nat) : recoveredMeasurement root visit recognition successor U7 calculus count = measurement root visit recognition successor := rfl

theorem actual_evolution (count : Nat) : recoveredEvolution root visit recognition successor U7 calculus count = evolution root visit recognition successor := rfl

theorem actual_defect (count : Nat) : recoveredDefect root visit recognition successor U7 calculus count = defect root visit recognition successor := rfl

namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (activated_query activated_answer activated_next)
end M
theorem query_answer_next (offset : Nat) :
    type_of% (M.activated_query (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) ∧
    type_of% (M.activated_answer (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) ∧
    type_of% (M.activated_next (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset) :=
  ⟨M.activated_query (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset,
    M.activated_answer (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset,
    M.activated_next (actualRoot root visit recognition successor) visit U7 calculus (installedReader root visit recognition successor) offset⟩
theorem actual_pairing (count : Nat) : recoveredPairing root visit recognition successor U7 calculus count = pairing root visit recognition successor := rfl

theorem actual_residual (count : Nat) (value : Joint root visit recognition successor) :
    recoveredResidual root visit recognition successor U7 calculus count value = residual root visit recognition successor value := rfl

theorem actual_residual_norm (count : Nat) (value : Joint root visit recognition successor) :
    ‖recoveredResidual root visit recognition successor U7 calculus count value‖ ^ 2 =
      ‖(residual root visit recognition successor value).fst‖ ^ 2 +
        ‖(residual root visit recognition successor value).snd‖ ^ 2 := residual_norm root visit recognition successor value

theorem actual_residual_zero_iff (count : Nat) (value : Joint root visit recognition successor) :
    recoveredResidual root visit recognition successor U7 calculus count value = 0 ↔
      (sourceExposure root visit recognition).hilbertEvolution ((sourceExposure root visit recognition).measurement value.1) =
        (sourceExposure root visit recognition).measurement ((sourceExposure root visit recognition).sourceAction.carrierAction value.1) ∧
      (targetExposure root visit recognition successor).hilbertEvolution ((targetExposure root visit recognition successor).measurement value.2) =
        (targetExposure root visit recognition successor).measurement ((targetExposure root visit recognition successor).sourceAction.carrierAction value.2) :=
  residual_zero_iff root visit recognition successor value

def actualRealization (count : Nat) : type_of% (realization root visit recognition successor) :=
  SourceGeneratedIntegralEquivariantPerfectRealization.generate
    (recoveredPairing root visit recognition successor U7 calculus count)
    (recoveredMeasurement root visit recognition successor U7 calculus count)
    (jointData root visit recognition successor)

theorem actual_realization_read (count : Nat) : actualRealization root visit recognition successor U7 calculus count =
    realization root visit recognition successor := rfl

theorem parent_next (count : Nat) : type_of%
    (SourceTemporalMaterial.Calculation.parent_next_preserved (sourceRoot root visit recognition successor)
      visit U7 calculus (installedReader root visit recognition successor) count) :=
  SourceTemporalMaterial.Calculation.parent_next_preserved (sourceRoot root visit recognition successor)
    visit U7 calculus (installedReader root visit recognition successor) count

theorem all_stage_whole_next (count : Nat) : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
      (actualRoot root visit recognition successor).toAuthoritativeRoot visit.current
      (installedReader root visit recognition successor) count) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.whole_next
    (actualRoot root visit recognition successor).toAuthoritativeRoot visit.current
    (installedReader root visit recognition successor) count
end SourceHistoryCommon.Root.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
