import H0mework.Versions.R2.Arithmetic.UnitArithmetic.Root

/-! The original writer's receipt supplies the binary operation consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeBinary.UnitWriteConsumer

open ArithmeticGeneration CanonicalUnitArithmeticRoot
open SourceOperationDerivations

noncomputable section

def append_normalization (current : UnitHistory) :
    Derivation environment
      (expression UnitHistory.parallel current unitHistory)
      (.const (Finsupp.single (nativeWriteAt current).target 1)) :=
  nativeOperationProof current

theorem append_native_target (current : UnitHistory) :
    lift UnitHistory.parallel (Finsupp.single current 1) (Finsupp.single unitHistory 1) =
      Finsupp.single (nativeWriteAt current).target 1 :=
  (append_normalization current).sound

theorem write_keeps_original_recursion (current : UnitHistory) :
    (nativeWriteAt current).target = current.parallel unitHistory ∧
      (nativeWriteAt current).wholeWriteBack = current :=
  ⟨nativeOperation_target (append_normalization current), rfl⟩

#guard (nativeWriteAt (.next (.next .empty))).target.cardinalShadow == 3

end
end SourceNativeBinary.UnitWriteConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
