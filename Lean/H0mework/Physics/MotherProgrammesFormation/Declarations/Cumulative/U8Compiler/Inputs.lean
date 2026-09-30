import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Data

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}

def memberCode (domain : MotherArenaHigher.Material rank) : MotherAuthorityFamilies.Member domain ↪ MotherArenaHigher.Base rank :=
  ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def formInputs (domain : MotherArenaHigher.Material rank)
    (operandCode : Operand root visit ↪ MotherArenaHigher.Base rank)
    (material : MotherArenaHigher.Material rank) : Option (MotherAuthorityFamilies.Member domain → Operand root visit) :=
  MotherArenaReceipts.NativeSection.form (memberCode domain) (fun _ => operandCode) material

theorem every_inputs (domain : MotherArenaHigher.Material rank)
    (operandCode : Operand root visit ↪ MotherArenaHigher.Base rank)
    (values : MotherAuthorityFamilies.Member domain → Operand root visit) :
    ∃ material : MotherArenaHigher.Material rank, formInputs domain operandCode material = some values :=
  MotherArenaReceipts.NativeSection.every_section (memberCode domain) (fun _ => operandCode) values

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
