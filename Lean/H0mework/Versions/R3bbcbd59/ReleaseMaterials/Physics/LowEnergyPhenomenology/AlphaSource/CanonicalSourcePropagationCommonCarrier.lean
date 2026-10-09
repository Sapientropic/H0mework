import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationJointSource

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.SourcePropagationCommonMomentum
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumGradedTransport
open PreparationVacuumYukawaTransport
open NativeHistoryGrade (Label)
attribute [local irreducible] GaussCoreHilbert.coreEquiv GaussDiagonalHistory.diagonalAction
  CanonicalPhysicalSpatial.physicalAction

local instance physicalSpan_finite (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    FiniteDimensional ℂ (physicalSpan p F):=by
  convert! FiniteCoreEvolution.coreSpan_finite (CanonicalPhysicalSpatial.physical p) F using 1

private theorem partialSpan_common {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (D : Submodule ℂ E)
    (A B : D→ₗ[ℂ] E) (F : Finset D) :
    FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=A} : E→ₗ.[ℂ] E) F=
      FiniteCoreEvolution.coreSpan ({domain:=D,toFun:=B} : E→ₗ.[ℂ] E) F:=rfl

private theorem standardBasis_heq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S T : Submodule ℂ E)
    [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] (same : S=T) :
    HEq (stdOrthonormalBasis ℂ S) (stdOrthonormalBasis ℂ T):=by
  cases same
  rfl

private theorem standardBasis_value {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S T : Submodule ℂ E)
    [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] (same : S=T)
    (i : Fin (Module.finrank ℂ S)) :
    ((stdOrthonormalBasis ℂ S i) : E)=
      ((stdOrthonormalBasis ℂ T (Fin.cast (congrArg (fun D : Submodule ℂ E=>Module.finrank ℂ D) same) i)) : E):=by
  cases same
  rfl

private theorem projection_common {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S T : Submodule ℂ E)
    [CompleteSpace S] [CompleteSpace T] (same : S=T) (x : E) :
    S.starProjection x=T.starProjection x:=by
  cases same
  rfl

private theorem choose_common {E : Type*} {P Q : E→Prop} (same : P=Q)
    (first : ∃x,P x) (second : ∃x,Q x) : Classical.choose first=Classical.choose second:=by
  cases same
  rfl

/-- Momentum changes the action on the original core, not the core occurrence. -/
theorem physical_domain_common (p : PhysicalMomentum) :
    (CanonicalPhysicalSpatial.physical p).domain=Core:=rfl

theorem physicalSpan_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    physicalSpan p F=physicalSpan 0 F:=by
  exact partialSpan_common (E:=H) Core
    (embed.comp ((CanonicalPhysicalSpatial.physicalAction p).comp coreEquiv.symm.toLinearMap))
    (embed.comp ((CanonicalPhysicalSpatial.physicalAction 0).comp coreEquiv.symm.toLinearMap)) F

theorem physicalBasis_heq (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HEq (physicalBasis p F) (physicalBasis 0 F):=by
  unfold physicalBasis
  exact standardBasis_heq (physicalSpan p F) (physicalSpan 0 F) (physicalSpan_common p F)

def sourceIndexCast (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    PhysicalBasisIndex 0 F≃PhysicalBasisIndex p F:=
  finCongr (congrArg (fun D : Submodule ℂ H=>Module.finrank ℂ D) (physicalSpan_common p F).symm)

theorem physicalBasis_value_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (i : PhysicalBasisIndex 0 F) :
    ((physicalBasis p F (sourceIndexCast p F i) : physicalSpan p F) : H)=
      ((physicalBasis 0 F i : physicalSpan 0 F) : H):=by
  exact (standardBasis_value (physicalSpan 0 F) (physicalSpan p F) (physicalSpan_common p F).symm i).symm

theorem physicalFrame_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (i : Label×PhysicalBasisIndex 0 F) :
    physicalFrame p F (i.1,sourceIndexCast p F i.2)=physicalFrame 0 F i:=
  congrArg (NativeHistoryGrade.projection i.1) (physicalBasis_value_common p F i.2)

theorem bareTest_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (i : PhysicalBasisIndex 0 F) :
    bareTest p F (sourceIndexCast p F i)=bareTest 0 F i:=by
  apply congrArg coreEquiv.symm
  apply Subtype.ext
  exact physicalBasis_value_common p F i

theorem projectionTest_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x : H) :
    projectionTest p F x=projectionTest 0 F x:=by
  apply congrArg coreEquiv.symm
  apply Subtype.ext
  exact projection_common (physicalSpan p F) (physicalSpan 0 F) (physicalSpan_common p F) x

theorem gradedTest_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (g : Label) (x : H) :
    gradedTest p F g x=gradedTest 0 F g x:=projectionTest_common p F _

theorem finiteSourceSet_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    finiteSourceSet p F=finiteSourceSet 0 F:=by
  unfold finiteSourceSet
  rw [←(sourceIndexCast p F).surjective.iUnion_comp (fun i=>tsupport (bareTest p F i))]
  simp only [bareTest_common]

/-- The original choice sees the same proposition and hence the same proof. -/
theorem finiteRetainer_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    finiteRetainer p F=finiteRetainer 0 F:=by
  unfold finiteRetainer
  apply choose_common
  funext phi
  rw [finiteSourceSet_common]

theorem retainFiber_common (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    retainFiber p F=retainFiber 0 F:=by
  unfold retainFiber
  rw [finiteRetainer_common]

end LowEnergy.SourcePropagationCommonMomentum
