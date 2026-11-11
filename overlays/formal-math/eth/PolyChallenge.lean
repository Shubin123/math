import BestThreeSat

/-! The open target, stated with `sorry` in place of a proof, as `Challenge.lean` states the two
proved theorems. It is not among the default targets, so `lake build` does not build it; build it
alone with `lake build PolyChallenge`. A proof here, depending on no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`, would be a machine-checked algorithm deciding 3-SAT in
polynomial time. -/

theorem BestThreeSat.polyTime : BestThreeSat.PolyTime := by
  sorry
