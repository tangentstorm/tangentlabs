-- toy implementation of binary numbers in lean4

inductive Bin where -- binary string
| B            -- infinite stream of zeros (high bits)
| O (x: Bin)   -- multiply by 2
| I (x: Bin)   -- multiply by 2 and add 1

namespace Bin

@[simp] def succ : Bin → Bin
| B   => I B
| O n => I n
| I n => O (succ n)

def ofNat : (n:Nat) → Bin
| 0 => Bin.B
| Nat.succ i => succ (ofNat i)
instance : OfNat Bin n := ⟨ofNat n⟩

-- not sure if lean needs this, but...
def toNat : (x:Bin) → Nat
| B => 0
| O n => 2 * toNat n
| I n => 1 + 2 * toNat n

def toString : Bin → String
| B   => "B"
| O n => "O (" ++ toString n ++ ")"
| I n => "I (" ++ toString n ++ ")"
instance : ToString Bin := ⟨toString⟩

@[simp] def add (x:Bin) (y:Bin) : Bin :=
match x, y with
| B, y  => y
| x, B  => x
| (O x), (O y) => O (add x y)
| (I x), (O y) => I (add x y)
| (O x), (I y) => I (add x y)
| (I x), (I y) => O (succ (add x y))
instance : Add Bin := ⟨add⟩

-- lean's dot notation lets you write the bits in the "normal" order.
-- here's how you write the number 2 in either direction:
example : O (I B) = B.I.O  := rfl

-- example: 2 + 3 = 5
example : add B.I.O B.I.I = B.I.O.I := by simp

-- ... now we can use the `+` symbol to trigger addition!
-- tactic `simp` can no longer prove it, but `rfl` can:
example : B.I.O + B.I.I = B.I.O.I := rfl

def wellFormed : Bin → Bool
| B => true
| O B => false
| O x => wellFormed x
| I x => wellFormed x

#check wellFormed (I (O B))
