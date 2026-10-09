import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.WriteBack
import H0mework.Versions.PR.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedCompleteWordDual
variable {Index : Type u}
def pairing : (Index →₀ ℤ) →ₗ[ℤ] Module.Dual ℤ (Index →₀ ℤ) :=
 (Finsupp.bilinearCombination ℤ ℤ (α:=Index) (M:=ℤ)).comp (LinearMap.pi fun index => Finsupp.lapply index)
theorem single (word : Index →₀ ℤ) (index : Index) : pairing word (Finsupp.single index 1)=word index := by
 change Finsupp.linearCombination ℤ (fun index => word index) (Finsupp.single index 1)=_
 rw [Finsupp.linearCombination_single,one_smul]
theorem injective : Function.Injective (pairing (Index:=Index)) := by
 intro left right same
 ext index
 exact (single left index).symm.trans ((congrArg (fun dual => dual (Finsupp.single index 1)) same).trans (single right index))
def coimageRecovery : SourceGeneratedPerfectification.PerfectificationCarrier (pairing (Index:=Index)) →ₗ[ℤ] (Index →₀ ℤ) :=
 SourceGeneratedPerfectification.canonicalFactor pairing LinearMap.id (by
  intro word invisible
  have zero : pairing word=pairing 0 := invisible.trans (map_zero pairing).symm
  exact injective zero)
theorem recovery_source (word : Index →₀ ℤ) :
 coimageRecovery (SourceGeneratedPerfectification.canonicalMap pairing word)=word :=
 LinearMap.congr_fun (SourceGeneratedPerfectification.canonicalFactor_comp pairing LinearMap.id (by
  intro value invisible
  exact injective (invisible.trans (map_zero pairing).symm))) word
end SourceGeneratedCompleteWordDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
