import Lake
open Lake DSL

package "CrashCource" where
  version := v!"0.1.0"

@[default_target]
lean_lib «CrashCource» where
  -- add library configuration options here
