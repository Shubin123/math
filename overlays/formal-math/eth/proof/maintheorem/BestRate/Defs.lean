module

public import ThreeSatRateStatement
public import Wrap.Defs

/-! # The sharpest bounds for 3-SAT that the formalization gives: definitions

The Main Theorem bounds the time to count by 2^{C·min{km/√(log m), k²·n·log log n/√(log n)}}, but
proof/machines/Wrap carries only the bound in n over to 3-SAT on the plain code, and the rate stated
for 3-SAT (`Sat3.InRateTM`) is proved only with the exponent 3/19 of log n. This file defines the
statements that keep both halves of the minimum at width 3, for the plain code of
`ThreeSatStatement.lean` (every n ≥ 0, every 3-CNF without repeated clauses, variables need not
occur):

* `DecidesTMNM`: as `Sat3.DecidesTM`, with a time bound in n and in the number m of clauses.
* `boundNM`: c·(n+2)^c·2^{c·min{m/√(log(m+2)), n·log log(n+4)/√(log(n+4))}}, rounded down. The factor
  (n+2)^c pays for reading the input, which may name n variables in a formula with few clauses.
* `boundSparse`: c·2^{c·n/√(log(n+2))}, the bound for formulas with m ≤ D·n clauses.

Logarithms are to base 2 and of n + 2 or n + 4, so that none of them is below 1. -/

@[expose] public section

namespace BestRate

open Turing

/-- The exponent in the number m of clauses: m/√(log₂(m+2)). -/
noncomputable def expM3 (m : ℕ) : ℝ := (m : ℝ) / Real.sqrt (Real.logb 2 ((m : ℝ) + 2))

/-- The exponent in the number n of variables: n·log₂ log₂(n+4)/√(log₂(n+4)). -/
noncomputable def expN3 (n : ℕ) : ℝ :=
  (n : ℝ) * Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) / Real.sqrt (Real.logb 2 ((n : ℝ) + 4))

/-- c·(n+2)^c·2^{c·min{m/√(log(m+2)), n·log log(n+4)/√(log(n+4))}}, rounded down. -/
noncomputable def boundNM (c n m : ℕ) : ℕ :=
  ⌊(c : ℝ) * ((n : ℝ) + 2) ^ c * (2 : ℝ) ^ ((c : ℝ) * min (expM3 m) (expN3 n))⌋₊

/-- c·2^{c·n/√(log₂(n+2))}, rounded down. -/
noncomputable def boundSparse (c n : ℕ) : ℕ :=
  ⌊(c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * ((n : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2))))⌋₊

/-- `M`, started on the plain code of a 3-CNF φ on n variables with m clauses, halts within t n m
steps with the bit «φ is satisfiable» as output. -/
def DecidesTMNM (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → ∃ b : Bool, (b = true ↔ Sat3.Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((Sat3.enc φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n φ.length))

/-- `M` decides 3-SAT within t n steps on every formula with at most D·n clauses. -/
def DecidesTMSparse (D : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → φ.length ≤ D * n → ∃ b : Bool, (b = true ↔ Sat3.Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((Sat3.enc φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))

/-- One machine N, with finite alphabets, for all of the following at once:
* within c·(n+2)^c·2^{c·min{m/√(log(m+2)), n·log log(n+4)/√(log(n+4))}} steps (`boundNM`);
* within c·2^{c·n·log log(n+4)/√(log(n+4))} steps (`expN3`);
* within c·2^{c·n/(log(n+2))^α} steps, for every α < 1/2 (`Sat3.rateBound`);
* within c·2^{c·n/√(log(n+2))} steps on formulas with at most D·n clauses, for every D;
* within c·2^{δn} steps, for every δ > 0 (`Wrap.DecidesEveryDelta`).
The constants c depend on α, on D and on δ; the machine does not. -/
def OneMachineBest : Prop :=
  ∃ N : TM2ComputableAux Bool Bool, (∀ i, Finite (N.tm.Γ i)) ∧
    (∃ c : ℕ, DecidesTMNM N (boundNM c)) ∧
    (∃ c : ℕ, Sat3.DecidesTM N fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((c : ℝ) * expN3 n)⌋₊) ∧
    (∀ α : ℝ, α < 1 / 2 → ∃ C : ℕ, Sat3.DecidesTM N (Sat3.rateBound C α)) ∧
    (∀ D : ℕ, ∃ c : ℕ, DecidesTMSparse D N (boundSparse c)) ∧
    Wrap.DecidesEveryDelta N

end BestRate
