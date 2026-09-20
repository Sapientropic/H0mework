import H0mework.Physics.MotherDeclarationsPhysical.LawsSource

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws

open MotherStreamLaws Stage9C.Revision

noncomputable section

theorem finite_native_approximation (K : Set Input) (finite : K.Finite)
    (target : Input → Stream) (m : ℕ) (ε : ℝ) (positive : 0 < ε) :
    ∃ programme : Programme, ∀ input ∈ K, ∀ output < m,
      dist (finiteLaw programme input output) (target input output) < ε := by
  obtain ⟨n, observations, separated⟩ := finite_coordinates K finite
  let feature : Input → Stream := fun input => pad n (fun index => observeInput (observations index) input)
  have faithful : K.InjOn feature := by
    intro first firstIn last lastIn same
    apply separated firstIn lastIn
    funext index
    have sampled := congrFun same index.val
    simpa only [feature, pad, dif_pos index.isLt] using sampled
  let restricted : K → Stream := fun input => feature input.val
  have restrictedFaithful : Function.Injective restricted := by
    intro first last same
    exact Subtype.ext (faithful first.property last.property same)
  let : Finite K := finite.to_subtype
  let onImage : Stream → Stream := Function.extend restricted (fun input : K => target input.val) (fun _ => 0)
  obtain ⟨polynomialCode, near⟩ := MotherPointwiseLaws.finite_native_approximation
    (Set.range restricted) (Set.finite_range restricted) onImage m ε positive
  obtain ⟨visit, points, formed⟩ := every_features n observations
  refine ⟨((visit, points), SpinPair.visit (10 + polynomialCode)), ?_⟩
  intro input inside output bound
  unfold finiteLaw
  rw [formed]
  have result := near (restricted ⟨input, inside⟩) (Set.mem_range_self _) output bound
  have recovered : onImage (restricted ⟨input, inside⟩) = target input :=
    restrictedFaithful.extend_apply _ _ ⟨input, inside⟩
  rw [recovered] at result
  exact result

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws
