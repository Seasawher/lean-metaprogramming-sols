import Lake
open Lake DSL

package «lean-metaprogramming-sols» where
  -- add package configuration options here

lean_lib «LeanMetaprogrammingSols» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-metaprogramming-sols» where
  root := `Main
