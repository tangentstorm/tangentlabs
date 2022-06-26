import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

package Bin {

}

lean_exe Main

