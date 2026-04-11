import TensorSieve.Operator

open KinematicRiemann

/- Formal Warrant: Live evaluation of the emission spectrum values.
   Starting from a large node, sieving downward. -/
#eval emissionSpectrumDown 27720 20

def emitDataDown (start : ℕ) (max_steps : ℕ) : IO Unit := do
  IO.println "level,x,amplitude,local_degree,jammed,eigenvalue_spacing"
  let data := emissionSpectrumDown start max_steps
  let mut last_jam_level : ℕ := 0
  for (lvl, x, amp, deg, jammed) in data do
    let mut spacing : ℕ := 0
    if jammed == 1 then
      if last_jam_level > 0 then
        spacing := lvl - last_jam_level
      last_jam_level := lvl
    IO.println s!"{lvl},{x},{amp},{deg},{jammed},{spacing}"

def main : IO Unit := do
  -- Start from a highly composite number or a large node to see the sieve downward.
  -- 27720000 = 2^6 * 3^2 * 5^4 * 7 * 11
  emitDataDown 27720000 1000
