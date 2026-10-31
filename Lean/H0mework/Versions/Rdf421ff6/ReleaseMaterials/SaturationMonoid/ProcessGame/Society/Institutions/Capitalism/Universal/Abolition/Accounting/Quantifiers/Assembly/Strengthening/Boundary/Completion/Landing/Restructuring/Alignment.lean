import H0mework.Foundation.Ledger.Restructuring

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
  {current : V.Current} {occurrence : source.toRootSource.actual.OccurrenceAt current}
  {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}

def alignSplit {left right targetLeft targetRight : after.Entry}
    {same : (evolution.origin left).1 = (evolution.origin right).1}
    {targetSame : (evolution.origin targetLeft).1 = (evolution.origin targetRight).1}
    (leftEq : left = targetLeft) (rightEq : right = targetRight)
    (covered : SourceNativeSplitCoverageAt law occurrence evolution left right same) :
    SourceNativeSplitCoverageAt law occurrence evolution targetLeft targetRight targetSame := by
  cases leftEq
  cases rightEq
  exact covered

def alignMerge {left right targetLeft targetRight : before.Entry}
    {same : (evolution.destination left).1 = (evolution.destination right).1}
    {targetSame : (evolution.destination targetLeft).1 = (evolution.destination targetRight).1}
    (leftEq : left = targetLeft) (rightEq : right = targetRight)
    (covered : SourceNativeMergeCoverageAt law occurrence evolution left right same) :
    SourceNativeMergeCoverageAt law occurrence evolution targetLeft targetRight targetSame := by
  cases leftEq
  cases rightEq
  exact covered

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
