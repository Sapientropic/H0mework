import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Exposure
set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon.Coordinates
variable {X : Type u}
def left (first second : RootedAccountedUnfolding X) (index : Fin first.trace.length) :
 Fin (SourceHistoryCommon.seed first second).trace.length := ⟨index.val+1,by
 change index.val+1 < (first.root::(first.trace++(second.trace++[]))).length
 simp only [List.length_cons,List.length_append,List.length_nil]
 have bounded := index.isLt
 omega⟩
def right (first second : RootedAccountedUnfolding X) (index : Fin second.trace.length) :
 Fin (SourceHistoryCommon.seed first second).trace.length := ⟨index.val+first.trace.length+1,by
 change index.val+first.trace.length+1 < (first.root::(first.trace++(second.trace++[]))).length
 simp only [List.length_cons,List.length_append,List.length_nil]
 have bounded := index.isLt
 omega⟩
theorem left_injective (first second : RootedAccountedUnfolding X) : Function.Injective (left first second) := by
 intro a b same
 apply Fin.ext
 have values := congrArg Fin.val same
 change a.val+1=b.val+1 at values
 omega
theorem right_injective (first second : RootedAccountedUnfolding X) : Function.Injective (right first second) := by
 intro a b same
 apply Fin.ext
 have values := congrArg Fin.val same
 change a.val+first.trace.length+1=b.val+first.trace.length+1 at values
 omega
theorem distinct (first second : RootedAccountedUnfolding X)
 (a : Fin first.trace.length) (b : Fin second.trace.length) : left first second a≠right first second b := by
 intro same
 have values := congrArg Fin.val same
 change a.val+1=b.val+first.trace.length+1 at values
 have bounded := a.isLt
 omega
theorem left_read (first second : RootedAccountedUnfolding X) (index : Fin first.trace.length) :
 (SourceHistoryCommon.seed first second).trace.get (left first second index)=first.trace.get index := by
 change (first.trace++(second.trace++[]))[index.val]=first.trace[index.val]
 exact List.getElem_append_left index.isLt
theorem right_read (first second : RootedAccountedUnfolding X) (index : Fin second.trace.length) :
 (SourceHistoryCommon.seed first second).trace.get (right first second index)=second.trace.get index := by
 change (first.trace++(second.trace++[]))[index.val+first.trace.length]=second.trace[index.val]
 exact (List.getElem_append_right' first.trace (by simpa only [List.length_append,List.length_nil,Nat.add_zero] using index.isLt)).symm.trans
  (List.getElem_append_left index.isLt)
end SourceHistoryCommon.Coordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
