import MainResults

/-!
# The sharpest time bounds for 3-SAT that this formalization proves, as Lean statements

This file has definitions only: no theorem, no proof. It imports `MainResults.lean` alone, which
imports Mathlib alone, and it uses that file's vocabulary: formulas `CNF n` on x₀ … x_{n−1},
instances `IsKCNF 3 φ` (at most 3 literals per clause, no clause written twice), the input word
`encClauses 3 φ`, `Satisfiable`, Mathlib's machines `Turing.FinTM2` with time counted in steps,
and `lg`, the logarithm to base 2.

`MainResults.MainTheorem` bounds the time to COUNT by 2^{C·min{km/√(log m), k²·n·log log n/√(log n)}}
on formulas in which every variable occurs, with m ≥ 2 and n ≥ 4; `MainResults.ETHIsFalse` uses
only that 3-SAT is in time O(2^{δn}) for every δ > 0, with a machine that may depend on δ. Inside
proof/, the strongest rate stated for 3-SAT is c·2^{c·n/(log(n+2))^{3/19}} (`Sat3.InRateTM (3/19)`).
`Statement` below asks for more, for ONE machine with finite alphabets, on EVERY 3-CNF (any n ≥ 0,
any number m of clauses, variables need not occur):

1. within c·(n+2)^c·2^{c·min{m/√(log(m+2)), n·log log(n+4)/√(log(n+4))}} steps: both halves of the
   minimum of the Main Theorem, at width 3. The factor (n+2)^c is there because the input names n
   variables even when m is small, and the machine has to read it;
2. within c·2^{c·n·log log(n+4)/√(log(n+4))} steps;
3. within c·2^{c·n/(log(n+2))^α} steps, for every α < 1/2;
4. within c·2^{c·n/√(log(n+2))} steps on the formulas with at most D·n clauses, for every D;
5. within c·2^{δn} steps, for every δ > 0.

The constants c depend on α, D and δ, and the proof says nothing about their size; the machine is
the same in all five. Logarithms are of n + 2, n + 4 and m + 2, so that none is below 1 and nothing
is divided by 0; for large n this changes nothing.
-/

namespace BestThreeSat

open MainResults Turing
open scoped NNReal

/-- The exponent in the number m of clauses: m/√(log(m+2)). -/
noncomputable def expM (m : ℕ) : ℝ := (m : ℝ) / Real.sqrt (lg ((m : ℝ) + 2))

/-- The exponent in the number n of variables: n·log log(n+4)/√(log(n+4)). -/
noncomputable def expN (n : ℕ) : ℝ := (n : ℝ) * lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4))

/-- `M` decides 3-SAT within t n m steps: started on `encClauses 3 φ`, for any n and any 3-CNF φ on
x₀ … x_{n−1} with m clauses, it halts within t n m steps with one bit as output, which is 1 if and
only if φ is satisfiable. As `DecidesKSat 3`, with a bound in n and m. -/
def DecidesWithinNM (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF 3 φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((encClauses 3 φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n φ.length))

/-- As `DecidesKSat 3`, for the formulas with at most D·n clauses only. -/
def DecidesSparseWithin (D : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF 3 φ → φ.length ≤ D * n → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((encClauses 3 φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))

/-- The five bounds of the head comment, for one machine. -/
def Statement : Prop :=
  ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
    (∃ c : ℕ, DecidesWithinNM M fun n m =>
      ⌊(c : ℝ) * ((n : ℝ) + 2) ^ c * (2 : ℝ) ^ ((c : ℝ) * min (expM m) (expN n))⌋₊) ∧
    (∃ c : ℕ, DecidesKSat 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * expN n)⌋₊) ∧
    (∀ α : ℝ, α < 1 / 2 → ∃ c : ℕ, DecidesKSat 3 M fun n =>
      ⌊(c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * n / lg ((n : ℝ) + 2) ^ α)⌋₊) ∧
    (∀ D : ℕ, ∃ c : ℕ, DecidesSparseWithin D M fun n =>
      ⌊(c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * ((n : ℝ) / Real.sqrt (lg ((n : ℝ) + 2))))⌋₊) ∧
    (∀ δ : ℝ≥0, 0 < δ → ∃ c : ℕ, DecidesKSat 3 M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊)

/-- **3-SAT in polynomial time** (an open problem; not proved anywhere in this repository): one
machine with finite alphabets and constants c, d such that the machine decides every 3-CNF on n
variables within c·(n+2)^d steps. A 3-CNF without repeated clauses on n variables has at most
(2n+1)³ clauses, so its code `encClauses 3 φ` has length polynomial in n, and a bound polynomial in n
is polynomial in the length of the input. By the Cook–Levin theorem (not formalized here) this
proposition is equivalent to P = NP. -/
def PolyTime : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c d : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    DecidesKSat 3 M fun n => c * (n + 2) ^ d

end BestThreeSat
