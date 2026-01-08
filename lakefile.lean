import Lake
open Lake DSL

package «software-foundations-lean4» where
  -- Package settings

@[default_target]
lean_lib «Basics» where
  srcDir := "."

@[default_target]
lean_lib «Induction» where
  srcDir := "."

@[default_target]
lean_lib «Lists» where
  srcDir := "."

@[default_target]
lean_lib «Poly» where
  srcDir := "."

@[default_target]
lean_lib «Tactics» where
  srcDir := "."

@[default_target]
lean_lib «Logic» where
  srcDir := "."
