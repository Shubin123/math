import BestThreeSat
import BestRate.Main
import Wrap.Arith
import ToTuring.EndLemmas

/-! The proof of `BestThreeSat.Statement`: it is `BestRate.oneMachineBest` of
proof/maintheorem/BestRate/Main.lean, whose statement `BestRate.OneMachineBest` is written in the
vocabulary of proof/statements; Lean accepts the term below by unfolding definitions. -/

/-- The five bounds for 3-SAT of `BestThreeSat.lean`, for one machine; no hypothesis. -/
theorem BestThreeSat.statement_holds : BestThreeSat.Statement := BestRate.oneMachineBest

/-- A check on the statement `BestThreeSat.PolyTime`, not a step toward it: polynomial time for
3-SAT would refute the Exponential Time Hypothesis, since (n+2)^d ≤ c'·2^{δn} for every δ > 0
(`Wrap.Arith.poly_below`). -/
theorem BestThreeSat.polyTime_ethIsFalse : BestThreeSat.PolyTime → MainResults.ETHIsFalse := by
  rintro ⟨M, c, d, hfin, hM⟩
  have h : ¬ Sat3.ETH_TM := Sat3.not_ETH_TM_iff.2 fun δ hδ => by
    obtain ⟨c', hc'⟩ := Wrap.Arith.poly_below d (ε := (δ : ℝ)) (by exact_mod_cast hδ)
    refine ⟨M, c * c', hfin, fun n φ hφ => ?_⟩
    obtain ⟨b, hb, ⟨ev⟩⟩ := hM n φ hφ
    refine ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (Nat.le_floor ?_)⟩⟩⟩
    push_cast
    calc (c : ℝ) * ((n : ℝ) + 2) ^ d ≤ (c : ℝ) * ((c' : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)) :=
          mul_le_mul_of_nonneg_left (hc' n) (Nat.cast_nonneg c)
      _ = (c : ℝ) * c' * (2 : ℝ) ^ ((δ : ℝ) * n) := by ring
  exact h
