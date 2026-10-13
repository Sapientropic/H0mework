
open Lean Elab Command in
run_cmd modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPairedResponseGramAction"
