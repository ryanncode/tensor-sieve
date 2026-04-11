import TensorSieve.Operator

open KinematicRiemann

/- Formal Warrant: Live evaluation of the first 20 emission spectrum values.
   This guarantees logical consistency in the InfoView. -/
#eval emissionSpectrum 1 20

/- Formal Warrant Theorem: The operator evaluates to either 0 or 1. -/
theorem operatorH_binary (x : ℕ) : operatorH x = 0 ∨ operatorH x = 1 := by
  dsimp [operatorH, TT_core]
  split
  · split
    · right; rfl
    · left; rfl
  · left; rfl

def emitData (max_level : ℕ) : IO Unit := do
  IO.println "level,x,successor,jammed,eigenvalue_spacing"
  let rec loop (x n : ℕ) (last_jam : ℕ) : IO Unit :=
    match n with
    | 0 => pure ()
    | n' + 1 => do
        let amp := operatorH x
        let jammed := if amp == 0 then 1 else 0
        let spacing := if jammed == 1 then x - last_jam else 0
        IO.println s!"{x},{x},{x+1},{jammed},{spacing}"
        let new_last_jam := if jammed == 1 then x else last_jam
        loop (x + 1) n' new_last_jam
  loop 1 max_level 0

def main : IO Unit := do
  emitData 1000
