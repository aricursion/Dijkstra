import Lake
open Lake DSL

package «djikstra» {
  -- add package configuration options here
}

lean_lib «Djikstra» {
  -- add library configuration options here
}

@[default_target]
lean_exe «djikstra» {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
