import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.FullResidual.Dynamics.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local instance] levelGroups
namespace AI
export Lower.SourceFamily.ActualInputCalculation (HasActualInput actual_environment withActualInput cofinal_actual_input next_after_born)
end AI
namespace CF
export Lower.SourceFamily.CalculationFactory (codeAt collapseValue)
end CF
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader afterEnvironment)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (datum actualOccurrence resultFace frames nextBorn next)
end S
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active rebase mathNext)
end E
namespace D
export Lower.SourceFamily.Admissions (packetAt packetAt_successor packetAt_successor_grade actual_index historyAt history_end_index)
end D
variable {W X : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (W target)]
variable (factory : SF.Factory W X PUnit.unit) (n : Nat)
variable (data : SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (sourceCfg : A.Programme (PhysicalValue := L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : sourceCfg.LowVar = X)

theorem written_value (name : sourceCfg.LowVar PUnit.unit) :
    (born factory n data sourceCfg language).activeEnvironment PUnit.unit name =
      (R.actualMaterial data.1 sourceCfg).raw.eval (N.input (R.actualMaterial data.1 sourceCfg)).environment :=
  (congrArg (fun env => env PUnit.unit name) (E.active (actual_writeback factory n data sourceCfg language))).trans
    (congrArg (fun env => env PUnit.unit name)
      (write_all factory n data sourceCfg language _))

variable (packet : AS.AdmissionPacket (W := W) (X := X) (s := PUnit.unit))
abbrev nextPacket := AS.bornAfterNative (AS.nativeAfterAdmission factory packet)

theorem packet_native_value (name : X PUnit.unit) :
    HEq ((nextPacket factory packet).2.1.1.activeEnvironment PUnit.unit name)
      ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
        (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment) := by
  rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    exact heq_of_eq (written_value factory grade data ⟨X, datum, inventory, pairInventory⟩ rfl name)

theorem programme_updated_value (sourceCode : Expr (PairValue W) X PUnit.unit) (grade : Nat)
    (programme : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := PUnit.unit))
    (sameVar : programme.LowVar = X)
    (sourceFrame : A.M.Frame (Value := L.Value W grade) (Var := X) (sort := PUnit.unit))
    (generated : AI.HasActualInput sourceCode grade programme sameVar) :
    HEq ((R.actualMaterial sourceFrame programme).raw.eval
      (N.input (R.actualMaterial sourceFrame programme)).environment)
      ((CF.codeAt sourceCode grade).eval (pairEnvironment (S.next sourceFrame programme).activeEnvironment 0)) := by
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value W grade) (PhysicalVar := X) (sort := PUnit.unit) :=
      ⟨X, datum, inventory, pairInventory⟩
    have before := (Lower.SourceFamily.ActivationSource.stock_action_reader sourceFrame cfg (S.actualOccurrence sourceFrame)).symm.trans
      (generated sourceFrame (S.actualOccurrence sourceFrame))
    have after := (Lower.SourceFamily.ActivationSource.stock_action_reader (S.next sourceFrame cfg) cfg
      (S.actualOccurrence (S.next sourceFrame cfg))).symm.trans
        (generated (S.next sourceFrame cfg) (S.actualOccurrence (S.next sourceFrame cfg)))
    have literal : (R.actualMaterial sourceFrame cfg).raw = CF.codeAt sourceCode grade :=
      congrArg (fun sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
        (Value := PairValue (L.Value W grade)) (Var := X) (sort := PUnit.unit) => sourceRaw.expression) before
    have environment : (N.input (R.actualMaterial sourceFrame cfg)).environment =
        pairEnvironment (S.next sourceFrame cfg).activeEnvironment 0 :=
      (add_sub_cancel (R.actualMaterial sourceFrame cfg).environment (R.afterEnvironment sourceFrame cfg)).trans
        ((congrArg (fun sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
          (Value := PairValue (L.Value W grade)) (Var := X) (sort := PUnit.unit) => sourceRaw.environment) after).trans
            (congrArg (fun env => pairEnvironment env (0 : Env (L.Value W grade) X))
              (AI.actual_environment (W := W) (X := X) grade (S.next sourceFrame cfg))))
    exact heq_of_eq ((congrArg (fun code => code.eval (N.input (R.actualMaterial sourceFrame cfg)).environment) literal).trans
      (congrArg (fun env => (CF.codeAt sourceCode grade).eval env) environment))

theorem born_next_active {V Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (V target)]
    (previous : A.M.Frame (Value := V) (Var := Y) (sort := PUnit.unit))
    (previousCfg activeCfg : A.Programme (PhysicalValue := V) (PhysicalVar := Y) (sort := PUnit.unit))
    (constant : E.At (S.nextBorn previous previousCfg) (S.nextBorn previous previousCfg).activeEnvironment) :
    (S.next (S.nextBorn previous previousCfg) activeCfg).activeEnvironment =
      (S.nextBorn previous previousCfg).activeEnvironment :=
  (congrArg (fun frame : A.M.Frame (Value := V) (Var := Y) (sort := PUnit.unit) => frame.activeEnvironment)
    (AI.next_after_born (W := V) (X := Y) 0 previous previousCfg activeCfg)).trans
      (E.active (E.mathNext constant))

theorem born_constant_of_decoder {V Y : PUnit.{u+1} → Type u} [∀ target, AddCommGroup (V target)]
    (sourceFrame : A.M.Frame (Value := V) (Var := Y) (sort := PUnit.unit))
    (cfg : A.Programme (PhysicalValue := V) (PhysicalVar := Y) (sort := PUnit.unit))
    (present : ∃ read, (S.datum sourceFrame cfg).nextEnvironmentReadAt = some read) :
    E.At (S.nextBorn sourceFrame cfg) (S.nextBorn sourceFrame cfg).activeEnvironment := by
  cases selected : (S.datum sourceFrame cfg).nextEnvironmentReadAt with
  | none =>
    rcases present with ⟨read, same⟩
    rw [selected] at same
    contradiction
  | some read =>
    apply E.rebase (env := read (S.actualOccurrence sourceFrame) (S.resultFace sourceFrame cfg).rootRead.2.2.1)
    intro current occurrence
    unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn
    dsimp only
    rw [selected]

abbrev nativeSelected (native : AS.AdmissionPacket (W := W) (X := X) (s := PUnit.unit)) :=
  S.frames native.2.1.1 (AS.stockCfg native.2.2.1) (0 + (AS.localNativeReceipt native).1)

theorem native_decoder_present :
    let native := AS.nativeAfterAdmission factory packet
    ∃ read, (S.datum (nativeSelected native) (AS.stockCfg native.2.2.1)).nextEnvironmentReadAt = some read := by
  rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = X at sameVar
    cases sameVar
    exact ⟨_, rfl⟩

theorem born_after_native_next_active (native : AS.AdmissionPacket (W := W) (X := X) (s := PUnit.unit))
    (present : ∃ read, (S.datum (nativeSelected native) (AS.stockCfg native.2.2.1)).nextEnvironmentReadAt = some read) :
    let born := AS.bornAfterNative native
    (S.next born.2.1.1 born.2.2.1).activeEnvironment = born.2.1.1.activeEnvironment :=
  born_next_active (V := L.Value W native.1) (Y := X)
    (nativeSelected native) (AS.stockCfg native.2.2.1) (AS.stockCfg native.2.2.1)
    (born_constant_of_decoder (nativeSelected native) (AS.stockCfg native.2.2.1) present)

theorem packet_next_active :
    (S.next (nextPacket factory packet).2.1.1 (nextPacket factory packet).2.2.1).activeEnvironment =
      (nextPacket factory packet).2.1.1.activeEnvironment :=
  born_after_native_next_active (AS.nativeAfterAdmission factory packet) (native_decoder_present factory packet)

variable (initial : A.M.Frame (Value := W) (Var := X) (sort := PUnit.unit))
variable (firstCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := PUnit.unit))
variable (firstLanguage : firstCfg.LowVar = X)

theorem cofinal_native_value (ordinal : Nat) (name : X PUnit.unit) :
    let packet := D.packetAt factory initial firstCfg firstLanguage ordinal
    let successor := D.packetAt factory initial firstCfg firstLanguage (ordinal + 1)
    HEq (successor.2.1.1.activeEnvironment PUnit.unit name)
      ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.eval
        (N.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment) := by
  dsimp only
  rw [D.packetAt_successor]
  exact packet_native_value factory _ name

theorem cofinal_next_active (ordinal : Nat) :
    let packet := D.packetAt factory initial firstCfg firstLanguage (ordinal + 1)
    (S.next packet.2.1.1 packet.2.2.1).activeEnvironment = packet.2.1.1.activeEnvironment := by
  dsimp only
  rw [D.packetAt_successor]
  exact packet_next_active factory _

theorem cofinal_after_value (sourceCode : Expr (PairValue W) X PUnit.unit)
    (baseFactory : SF.Factory W X PUnit.unit) (ordinal : Nat) (name : X PUnit.unit) :
    let packet := D.packetAt (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 1)
    let successor := D.packetAt (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 2)
    HEq (successor.2.1.1.activeEnvironment PUnit.unit name)
      ((CF.codeAt sourceCode packet.1).eval
        (pairEnvironment (S.next packet.2.1.1 packet.2.2.1).activeEnvironment 0)) :=
  (cofinal_native_value (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 1) name).trans
    (programme_updated_value sourceCode _ _ _ _
      (AI.cofinal_actual_input sourceCode baseFactory initial firstCfg firstLanguage ordinal))

theorem cofinal_current_value (sourceCode : Expr (PairValue W) X PUnit.unit)
    (baseFactory : SF.Factory W X PUnit.unit) (ordinal : Nat) (name : X PUnit.unit) :
    let packet := D.packetAt (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 1)
    let successor := D.packetAt (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 2)
    HEq (successor.2.1.1.activeEnvironment PUnit.unit name)
      ((CF.codeAt sourceCode packet.1).eval (pairEnvironment packet.2.1.1.activeEnvironment 0)) :=
  (cofinal_after_value initial firstCfg firstLanguage sourceCode baseFactory ordinal name).trans
    (heq_of_eq (congrArg (fun env => (CF.codeAt sourceCode _).eval (pairEnvironment env 0))
      (cofinal_next_active (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage ordinal)))

theorem collapse_generated_successor (grade nextGrade : Nat) (sameGrade : nextGrade = grade + 1)
    (next : L.Value W nextGrade PUnit.unit) (computed : PairValue (L.Value W grade) PUnit.unit)
    (sameValue : HEq next computed) :
    CF.collapseValue (W := W) nextGrade (next, 0) = CF.collapseValue (W := W) grade computed := by
  subst nextGrade
  have equal : next = computed := eq_of_heq sameValue
  cases equal
  exact congrArg (CF.collapseValue (W := W) grade) (add_zero computed)

theorem cofinal_collapsed_value (sourceCode : Expr (PairValue W) X PUnit.unit)
    (baseFactory : SF.Factory W X PUnit.unit) (ordinal : Nat) (name : X PUnit.unit) :
    let packet := D.packetAt (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 1)
    let successor := D.packetAt (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 2)
    CF.collapseValue successor.1 (successor.2.1.1.activeEnvironment PUnit.unit name, 0) =
      sourceCode.eval (fun target slot => CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target slot, 0)) :=
  (collapse_generated_successor _ _
    (D.packetAt_successor_grade (AI.withActualInput sourceCode baseFactory) initial firstCfg firstLanguage (ordinal + 1)) _ _
    (cofinal_current_value initial firstCfg firstLanguage sourceCode baseFactory ordinal name)).trans
      (Lower.SourceFamily.CalculationFactory.code_base_value sourceCode _ _)

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
