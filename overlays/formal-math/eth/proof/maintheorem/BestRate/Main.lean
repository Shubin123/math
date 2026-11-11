module

public import BestRate.Defs
import Wrap.Main
import Wrap.Arith
import Wrap.ArithRate
import Wrap.FrontEnd
import CountedRoute.Main
import NamesInOrder.General
import PaddedDescent.RateLemmas
import ToTuring.EndLemmas
import VariableBound.Paper.Arith
import VariableBound.Paper.MainTheorem
import VariableBound.Paper.Rename.End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The sharpest bounds for 3-SAT that the formalization gives: proofs

The statements are those of `BestRate/Defs.lean`. The machine is the wrapper of proof/machines/Wrap:
the front end that pads a 3-CNF with four forced variables, the counter of the Main Theorem, and «some
bit is 1». `Wrap.decidesTM_of_wraps_counter` keeps only the bound in n of the counter; here
`decidesTMNM_of_wraps_counter` keeps the whole minimum, with m + 4 clauses for the padded formula.

The steps:
1. `wrapped_time_le_nm`: the time of the wrapper, q·(⌊2^{C₁·min{m'/√(lg m'), n'·lg lg n'/√(lg n')}}⌋
   + C₂·L^{C₂} + X + 1)^q with m' = m + 4 and 4 ≤ n' ≤ n + 4, is at most `boundNM c n m`. The shift
   m ↦ m + 4 costs 4 in the exponent in m (`expM_shift`), the shift n' ≤ n + 4 costs 32 in the
   exponent in n (`Wrap.Arith.exponent_le`, `Wrap.Arith.rate_le_eight`), and the polynomial part
   goes into (n+2)^c.
2. `rN_le`: lg lg(n+4)/√(lg(n+4)) ≤ (2/ε)/(lg(n+2))^α with ε = 1/2 − α, for 0 ≤ α < 1/2, from
   log x ≤ x^ε/ε. So the bound in n gives `Sat3.rateBound` for every α < 1/2, where
   `Sat3.InRateTM (3/19)` was the rate proved before.
3. `boundNM_le_sparse`: for m ≤ D·n the exponent in m is at most (D+1)·n/√(lg(n+2)) + 2, and
   (n+2)^c is at most 2^{c·(64·n/√(lg(n+2)) + 128)}.

Throughout, lg is the logarithm to base 2. -/

public section

namespace BestRate

open Turing MainTheoremForms Wrap Wrap.Arith

/-! ### The exponents -/

/-- The exponent in n is n times the rate of proof/machines/Wrap. -/
theorem expN3_eq (n : ℕ) : expN3 n = (n : ℝ) * SatK.rN 1 (1 / 2) n := by
  rw [rate_eq]
  unfold expN3 MainTheoremForms.lg
  ring

theorem expN3_nonneg (n : ℕ) : 0 ≤ expN3 n := by
  rw [expN3_eq]
  exact mul_nonneg (Nat.cast_nonneg n) (rate_nonneg n)

theorem expM3_nonneg (m : ℕ) : 0 ≤ expM3 m := by
  unfold expM3
  positivity

/-- (m+4)/√(lg(m+4)) ≤ m/√(lg(m+2)) + 4. -/
theorem expM_shift (m : ℕ) : ((m + 4 : ℕ) : ℝ) / Real.sqrt (lg ((m + 4 : ℕ) : ℝ)) ≤ expM3 m + 4 := by
  have h1 : 1 ≤ Real.logb 2 ((m : ℝ) + 2) := Sat3.one_le_logb m
  have hle : Real.logb 2 ((m : ℝ) + 2) ≤ Real.logb 2 ((m : ℝ) + 4) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have hs1 : 1 ≤ Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := Real.one_le_sqrt.2 h1
  have hs : Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) ≤ Real.sqrt (Real.logb 2 ((m : ℝ) + 4)) := Real.sqrt_le_sqrt hle
  unfold expM3 MainTheoremForms.lg
  push_cast
  calc ((m : ℝ) + 4) / Real.sqrt (Real.logb 2 ((m : ℝ) + 4))
      ≤ ((m : ℝ) + 4) / Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := div_le_div_of_nonneg_left (by positivity) (by linarith) hs
    _ = (m : ℝ) / Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) + 4 / Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := by ring
    _ ≤ (m : ℝ) / Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) + 4 := by
        have := div_le_self (by norm_num : (0 : ℝ) ≤ 4) hs1
        linarith

/-! ### The time of the wrapper, in n and m -/

/-- For all q, C₁, C₂, a, d there is a c such that q·(⌊2^{C₁·min{m'/√(lg m'), n'·lg lg n'/√(lg
n')}}⌋ + C₂·L^{C₂} + X + 1)^q ≤ `boundNM c n m` whenever m' = m + 4, 4 ≤ n' ≤ n + 4 and
L, X ≤ a·(n+2)^d. -/
theorem wrapped_time_le_nm (q C₁ C₂ a d : ℕ) :
    ∃ c : ℕ, ∀ (n m n' L X : ℕ), 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((timeMin3 C₁ (m + 4) n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ boundNM c n m := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = d * C₂ + d := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C₂ * a ^ C₂ + a + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ ((C₁ : ℝ) * 32) + A := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨c₀, hc₀⟩ := exists_nat_ge ((q : ℝ) * K ^ q)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = c₀ + D * q + q * C₁ := ⟨_, rfl⟩
  refine ⟨c, fun n m n' L X hn' hnn hL hX => ?_⟩
  unfold boundNM
  refine Nat.le_floor ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min (expM3 m) (expN3 n) := ⟨_, rfl⟩
  rw [← hμ]
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact le_min (expM3_nonneg m) (expN3_nonneg n)
  -- the counter
  have hT : (timeMin3 C₁ (m + 4) n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((C₁ : ℝ) * μ) := by
    have h1 : ((m + 4 : ℕ) : ℝ) / Real.sqrt (lg ((m + 4 : ℕ) : ℝ)) ≤ expM3 m + 32 := by
      have := expM_shift m
      linarith
    have h2 : (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ expN3 n + 32 := by
      have h4 := exponent_le hn' hnn
      have h5 := rate_le_eight n
      rw [expN3_eq]
      linarith
    have hmin : min (((m + 4 : ℕ) : ℝ) / Real.sqrt (lg ((m + 4 : ℕ) : ℝ))) ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n')) ≤ μ + 32 := by
      refine (min_le_min h1 h2).trans ?_
      rw [hμ]
      rcases le_total (expM3 m) (expN3 n) with h | h
      · rw [min_eq_left h, min_eq_left (by linarith)]
      · rw [min_eq_right h, min_eq_right (by linarith)]
    unfold timeMin3
    refine (Nat.floor_le (by positivity)).trans ?_
    calc (2 : ℝ) ^ ((C₁ : ℝ) * min (((m + 4 : ℕ) : ℝ) / Real.sqrt (lg ((m + 4 : ℕ) : ℝ))) ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n')))
        ≤ (2 : ℝ) ^ ((C₁ : ℝ) * (μ + 32)) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hmin (Nat.cast_nonneg C₁))
      _ = (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((C₁ : ℝ) * μ) := by
          rw [← Real.rpow_add two_pos]
          congr 1
          ring
  -- the polynomial part
  have hQ : ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 2) ^ D := by
    have := poly_part_le C₂ a d hL hX
    rw [← hA, ← hD] at this
    exact_mod_cast this
  have hP1 : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ D := one_le_pow₀ (by linarith)
  have hE1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * μ) := Real.one_le_rpow one_le_two (by positivity)
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = (timeMin3 C₁ (m + 4) n' + C₂ * L ^ C₂) + X + 1 := ⟨_, rfl⟩
  rw [← hS]
  have hSb : (S : ℝ) ≤ K * ((n : ℝ) + 2) ^ D * (2 : ℝ) ^ ((C₁ : ℝ) * μ) := by
    have e1 : (S : ℝ) = (timeMin3 C₁ (m + 4) n' : ℝ) + ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) := by
      rw [hS]
      push_cast
      ring
    rw [e1, hK]
    have h2 : (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((C₁ : ℝ) * μ) ≤
        (2 : ℝ) ^ ((C₁ : ℝ) * 32) * ((n : ℝ) + 2) ^ D * (2 : ℝ) ^ ((C₁ : ℝ) * μ) := by
      have : 0 ≤ (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((C₁ : ℝ) * μ) := by positivity
      nlinarith
    have h3 : (A : ℝ) * ((n : ℝ) + 2) ^ D ≤ (A : ℝ) * ((n : ℝ) + 2) ^ D * (2 : ℝ) ^ ((C₁ : ℝ) * μ) := by
      have : 0 ≤ (A : ℝ) * ((n : ℝ) + 2) ^ D := by positivity
      nlinarith
    nlinarith
  have e2 : ((2 : ℝ) ^ ((C₁ : ℝ) * μ)) ^ q = (2 : ℝ) ^ (((q * C₁ : ℕ) : ℝ) * μ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    congr 1
    push_cast
    ring
  have hpow : (S : ℝ) ^ q ≤ K ^ q * ((n : ℝ) + 2) ^ (D * q) * (2 : ℝ) ^ (((q * C₁ : ℕ) : ℝ) * μ) := by
    calc (S : ℝ) ^ q ≤ (K * ((n : ℝ) + 2) ^ D * (2 : ℝ) ^ ((C₁ : ℝ) * μ)) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg S) hSb q
      _ = K ^ q * ((n : ℝ) + 2) ^ (D * q) * (2 : ℝ) ^ (((q * C₁ : ℕ) : ℝ) * μ) := by
          rw [mul_pow, mul_pow, ← pow_mul, e2]
  have hcK : (q : ℝ) * K ^ q ≤ c := by
    rw [hc]
    push_cast
    have : (0 : ℝ) ≤ (D : ℝ) * q + q * C₁ := by positivity
    linarith
  have hP : ((n : ℝ) + 2) ^ (D * q) ≤ ((n : ℝ) + 2) ^ c := pow_le_pow_right₀ (by linarith) (by omega)
  have hcC : ((q * C₁ : ℕ) : ℝ) ≤ c := by exact_mod_cast (by omega : q * C₁ ≤ c)
  have hE : (2 : ℝ) ^ (((q * C₁ : ℕ) : ℝ) * μ) ≤ (2 : ℝ) ^ ((c : ℝ) * μ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hcC hμ0)
  calc ((q * S ^ q : ℕ) : ℝ) = (q : ℝ) * (S : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (K ^ q * ((n : ℝ) + 2) ^ (D * q) * (2 : ℝ) ^ (((q * C₁ : ℕ) : ℝ) * μ)) :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg q)
    _ = ((q : ℝ) * K ^ q) * ((n : ℝ) + 2) ^ (D * q) * (2 : ℝ) ^ (((q * C₁ : ℕ) : ℝ) * μ) := by ring
    _ ≤ (c : ℝ) * ((n : ℝ) + 2) ^ c * (2 : ℝ) ^ ((c : ℝ) * μ) :=
        mul_le_mul (mul_le_mul hcK hP (by positivity) (by positivity)) hE (by positivity) (by positivity)

/-- A wrapper N of a machine M that counts on the compact code within the bound of the Main Theorem,
with «some bit is 1» after it, decides 3-SAT on the plain code within every bound T in n and m that
covers its time with m + 4 clauses: as `Wrap.decidesTM_of_wraps_counter`, without dropping the
bound in m. -/
theorem decidesTMNM_of_wraps_counter {pre : List Bool → List Bool} (hpre : MapsPlainToPaddedCompact pre)
    {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : CountsCompactKCNFWithinMinBound M C)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wraps M pre someBit N q) {a d : ℕ}
    (hL : ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d)
    {T : ℕ → ℕ → ℕ}
    (hT : ∀ (n m n' L X : ℕ), 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((timeMin3 (9 * C) (m + 4) n' + C * L ^ C) + X + 1) ^ q ≤ T n m) :
    DecidesTMNM N T := by
  intro n φ hφ
  obtain ⟨h3, hlen, h4, hle, hsat⟩ := pad4KeepsSatAndMeetsSideConditions n φ hφ
  have hm : 2 ≤ (pad4 φ).length := by omega
  obtain ⟨ev⟩ := hW (Sat3.enc φ) _ _ (by rw [hpre n φ hφ]; exact hM 3 (n + 4) (pad4 φ) (by norm_num) h3 hm h4)
  have e : someBit (SatK.binary (MainTheoremForms.numOcc (pad4 φ)) (MainTheoremForms.numSatOcc (pad4 φ))) = [decide (MainTheoremForms.numSatOcc (pad4 φ) ≠ 0)] :=
    VariableBound.Rename.anyBit_binary (VariableBound.Paper.numSatOcc_lt (pad4 φ))
  rw [e] at ev
  refine ⟨decide (MainTheoremForms.numSatOcc (pad4 φ) ≠ 0), by rw [decide_eq_true_iff, ← VariableBound.Paper.satisfiable_iff, hsat], ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ?_⟩⟩⟩
  have hT' := hT n φ.length _ _ _ h4 hle (hL n φ hφ).1 (hL n φ hφ).2
  rw [← hlen] at hT'
  refine le_trans ?_ hT'
  gcongr
  exact VariableBound.Paper.timeMin_three_le C hm h4

/-! ### From the bound in n to a power of log n -/

/-- lg x ≤ (2/ε)·x^ε for x ≥ 0 and ε > 0, from log x ≤ x^ε/ε and log 2 > 1/2. -/
theorem logb_le_rpow {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) : Real.logb 2 x ≤ 2 / ε * x ^ ε := by
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := half_lt_log_two
  have hY : 0 ≤ x ^ ε / ε := by positivity
  rw [Real.logb, div_le_iff₀ (by linarith)]
  have : x ^ ε / ε ≤ 2 / ε * x ^ ε * Real.log 2 := by
    have e : 2 / ε * x ^ ε * Real.log 2 = (x ^ ε / ε) * (2 * Real.log 2) := by ring
    rw [e]
    nlinarith
  linarith

/-- lg lg(n+4)/√(lg(n+4)) ≤ (2/ε)/(lg(n+2))^α with ε = 1/2 − α, for 0 ≤ α < 1/2. -/
theorem rN_le (n : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα2 : α < 1 / 2) :
    SatK.rN 1 (1 / 2) n ≤ 2 / (1 / 2 - α) / Real.logb 2 ((n : ℝ) + 2) ^ α := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / 2 - α := ⟨_, rfl⟩
  rw [← hε]
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨h2, -⟩ := lg_add_four_facts n
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = lg ((n : ℝ) + 4) := ⟨_, rfl⟩
  rw [rate_eq, ← hΛ]
  rw [← hΛ] at h2
  have hΛ0 : 0 < Λ := by linarith
  have hl1 : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := Sat3.one_le_logb n
  have hlle : Real.logb 2 ((n : ℝ) + 2) ≤ Λ := by
    rw [hΛ]
    exact Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  have hsq : Real.sqrt Λ = Λ ^ ε * Λ ^ α := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hΛ0]
    congr 1
    rw [hε]
    ring
  have hlg : lg Λ ≤ 2 / ε * Λ ^ ε := logb_le_rpow (by linarith) hε0
  have hpa : 0 < Real.logb 2 ((n : ℝ) + 2) ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hpp : Real.logb 2 ((n : ℝ) + 2) ^ α ≤ Λ ^ α := Real.rpow_le_rpow (by linarith) hlle hα
  rw [hsq, div_le_div_iff₀ (by positivity) hpa]
  calc lg Λ * Real.logb 2 ((n : ℝ) + 2) ^ α ≤ (2 / ε * Λ ^ ε) * Λ ^ α :=
        mul_le_mul hlg hpp hpa.le (by positivity)
    _ = 2 / ε * (Λ ^ ε * Λ ^ α) := by ring

/-- For 0 ≤ α < 1/2, the bound in n with the constant c is at most `Sat3.rateBound C α` for some C. -/
theorem boundNK_le_rateBound (c : ℕ) {α : ℝ} (hα : 0 ≤ α) (hα2 : α < 1 / 2) :
    ∃ C : ℕ, ∀ n, SatM.boundNK (SatK.rN 1 (1 / 2)) c 3 n ≤ Sat3.rateBound C α n := by
  have hε0 : 0 < 1 / 2 - α := by linarith
  obtain ⟨C, hC⟩ := exists_nat_ge ((c : ℝ) + 18 * c / (1 / 2 - α))
  refine ⟨C, fun n => ?_⟩
  unfold SatM.boundNK Sat3.rateBound
  refine Nat.floor_le_floor ?_
  have hc0 : (0 : ℝ) ≤ 18 * c / (1 / 2 - α) := by positivity
  have hcC : (c : ℝ) ≤ C := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpa : 0 < Real.logb 2 ((n : ℝ) + 2) ^ α := Real.rpow_pos_of_pos (by linarith [Sat3.one_le_logb n]) α
  have hr := rN_le n hα hα2
  have hr0 := rate_nonneg n
  have hexp : (c : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n ≤ (C : ℝ) * n / Real.logb 2 ((n : ℝ) + 2) ^ α := by
    have e : (C : ℝ) * n / Real.logb 2 ((n : ℝ) + 2) ^ α = (C : ℝ) * n * (1 / Real.logb 2 ((n : ℝ) + 2) ^ α) := by ring
    have e2 : 2 / (1 / 2 - α) / Real.logb 2 ((n : ℝ) + 2) ^ α = 2 / (1 / 2 - α) * (1 / Real.logb 2 ((n : ℝ) + 2) ^ α) := by ring
    rw [e]
    rw [e2] at hr
    have hinv : 0 ≤ 1 / Real.logb 2 ((n : ℝ) + 2) ^ α := by positivity
    have h18 : (c : ℝ) * 9 * (2 / (1 / 2 - α)) = 18 * c / (1 / 2 - α) := by ring
    push_cast
    calc (c : ℝ) * 3 ^ 2 * n * SatK.rN 1 (1 / 2) n
        ≤ (c : ℝ) * 3 ^ 2 * n * (2 / (1 / 2 - α) * (1 / Real.logb 2 ((n : ℝ) + 2) ^ α)) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (c : ℝ) * 9 * (2 / (1 / 2 - α)) * n * (1 / Real.logb 2 ((n : ℝ) + 2) ^ α) := by ring
      _ ≤ (C : ℝ) * n * (1 / Real.logb 2 ((n : ℝ) + 2) ^ α) := by
          rw [h18]
          have : 18 * (c : ℝ) / (1 / 2 - α) ≤ C := by linarith
          have := mul_le_mul_of_nonneg_right this (mul_nonneg hn0 hinv)
          linarith
  exact mul_le_mul hcC (Real.rpow_le_rpow_of_exponent_le one_le_two hexp) (by positivity) (by positivity)

/-! ### Formulas with at most D·n clauses -/

/-- lg(n+2) ≤ 64·n/√(lg(n+2)) + 128: as `Wrap.Arith.lg_le_rate`, with n + 2 in place of n + 4. -/
theorem lg_le_sparse (n : ℕ) :
    Real.logb 2 ((n : ℝ) + 2) ≤ 64 * ((n : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2))) + 128 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hl1 : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := Sat3.one_le_logb n
  have hroot : lg ((n : ℝ) + 2) ≤ 8 * Real.sqrt (Real.sqrt ((n : ℝ) + 2)) := lg_le_fourth_root hN
  unfold MainTheoremForms.lg at hroot
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.logb 2 ((n : ℝ) + 2) := ⟨_, rfl⟩
  rw [← hΛ] at hl1 hroot ⊢
  have hv1 : 1 ≤ Real.sqrt ((n : ℝ) + 2) := Real.one_le_sqrt.2 (by linarith)
  have hvv : Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) = (n : ℝ) + 2 := Real.mul_self_sqrt hN.le
  have hww : Real.sqrt (Real.sqrt ((n : ℝ) + 2)) * Real.sqrt (Real.sqrt ((n : ℝ) + 2)) = Real.sqrt ((n : ℝ) + 2) :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hsq : Λ * Λ ≤ 64 * ((n : ℝ) + 2) := by
    have h3 : Λ * Λ ≤ (8 * Real.sqrt (Real.sqrt ((n : ℝ) + 2))) * (8 * Real.sqrt (Real.sqrt ((n : ℝ) + 2))) :=
      mul_self_le_mul_self (by linarith) hroot
    have h4 : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by nlinarith
    nlinarith
  have hs1 : 1 ≤ Real.sqrt Λ := Real.one_le_sqrt.2 hl1
  have hs0 : 0 < Real.sqrt Λ := by linarith
  have hss : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt (by linarith)
  have a1 : Λ * Real.sqrt Λ ≤ 64 * ((n : ℝ) + 2) := by
    have h5 : Real.sqrt Λ ≤ Λ := by nlinarith
    have h6 : Λ * Real.sqrt Λ ≤ Λ * Λ := mul_le_mul_of_nonneg_left h5 (by linarith)
    linarith
  have a2 : Λ ≤ 64 * ((n : ℝ) + 2) / Real.sqrt Λ := (le_div_iff₀ hs0).2 a1
  have a3 : 64 * ((n : ℝ) + 2) / Real.sqrt Λ = 64 * ((n : ℝ) / Real.sqrt Λ) + 128 / Real.sqrt Λ := by ring
  have a4 : 128 / Real.sqrt Λ ≤ 128 := div_le_self (by norm_num) hs1
  linarith

/-- m/√(lg(m+2)) ≤ (D+1)·n/√(lg(n+2)) + 2 for m ≤ D·n. -/
theorem expM3_le_sparse {D n m : ℕ} (hm : m ≤ D * n) :
    expM3 m ≤ ((D : ℝ) + 1) * ((n : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2))) + 2 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hm' : (m : ℝ) ≤ ((D : ℝ) + 1) * n := by
    have : (m : ℝ) ≤ (D : ℝ) * n := by exact_mod_cast hm
    nlinarith
  have hl1 : 1 ≤ Real.logb 2 ((m : ℝ) + 2) := Sat3.one_le_logb m
  have hln : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := Sat3.one_le_logb n
  have hsm : 0 < Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) := Real.sqrt_pos.2 (by linarith)
  have hs1 : 1 ≤ Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := Real.one_le_sqrt.2 hln
  have hy : (n : ℝ) + 2 ≤ ((D : ℝ) + 1) * n + 2 := by nlinarith
  have hlog : Real.logb 2 ((n : ℝ) + 2) ≤ Real.logb 2 (((D : ℝ) + 1) * n + 2) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) hy
  have hmono := div_sqrt_lg_mono (x := (m : ℝ) + 2) (y := ((D : ℝ) + 1) * n + 2) (by linarith) (by linarith)
  unfold MainTheoremForms.lg at hmono
  unfold expM3
  calc (m : ℝ) / Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) ≤ ((m : ℝ) + 2) / Real.sqrt (Real.logb 2 ((m : ℝ) + 2)) :=
        div_le_div_of_nonneg_right (by linarith) hsm.le
    _ ≤ (((D : ℝ) + 1) * n + 2) / Real.sqrt (Real.logb 2 (((D : ℝ) + 1) * n + 2)) := hmono
    _ ≤ (((D : ℝ) + 1) * n + 2) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) (Real.sqrt_le_sqrt hlog)
    _ = ((D : ℝ) + 1) * ((n : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2))) + 2 / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := by ring
    _ ≤ ((D : ℝ) + 1) * ((n : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2))) + 2 := by
        have := div_le_self (by norm_num : (0 : ℝ) ≤ 2) hs1
        linarith

/-- On formulas with at most D·n clauses, `boundNM c₁` is at most `boundSparse c` for some c. -/
theorem boundNM_le_sparse (c₁ D : ℕ) : ∃ c : ℕ, ∀ n m : ℕ, m ≤ D * n → boundNM c₁ n m ≤ boundSparse c n := by
  obtain ⟨c₀, hc₀⟩ := exists_nat_ge ((c₁ : ℝ) * (2 : ℝ) ^ ((c₁ : ℝ) * 130))
  refine ⟨c₀ + c₁ * (D + 65), fun n m hm => ?_⟩
  unfold boundNM boundSparse
  refine Nat.floor_le_floor ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hc0 : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg c₁
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (n : ℝ) / Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hM := expM3_le_sparse hm
  rw [← hs] at hM
  have hL := lg_le_sparse n
  rw [← hs] at hL
  have hmin : min (expM3 m) (expN3 n) ≤ ((D : ℝ) + 1) * s + 2 := (min_le_left _ _).trans hM
  -- (n+2)^c₁ = 2^{c₁·lg(n+2)}
  have hpow : ((n : ℝ) + 2) ^ c₁ ≤ (2 : ℝ) ^ ((c₁ : ℝ) * (64 * s + 128)) := by
    have e : (2 : ℝ) ^ Real.logb 2 ((n : ℝ) + 2) = (n : ℝ) + 2 := Real.rpow_logb two_pos (by norm_num) (by positivity)
    calc ((n : ℝ) + 2) ^ c₁ = (2 : ℝ) ^ ((c₁ : ℝ) * Real.logb 2 ((n : ℝ) + 2)) := by
          rw [mul_comm, Real.rpow_mul zero_le_two, e, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((c₁ : ℝ) * (64 * s + 128)) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hL hc0)
  have hexp : (2 : ℝ) ^ ((c₁ : ℝ) * min (expM3 m) (expN3 n)) ≤ (2 : ℝ) ^ ((c₁ : ℝ) * (((D : ℝ) + 1) * s + 2)) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hmin hc0)
  have hcomb : (2 : ℝ) ^ ((c₁ : ℝ) * (64 * s + 128)) * (2 : ℝ) ^ ((c₁ : ℝ) * (((D : ℝ) + 1) * s + 2)) =
      (2 : ℝ) ^ ((c₁ : ℝ) * 130) * (2 : ℝ) ^ (((c₁ * (D + 65) : ℕ) : ℝ) * s) := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1
    push_cast
    ring
  have hcs : ((c₁ * (D + 65) : ℕ) : ℝ) ≤ ((c₀ + c₁ * (D + 65) : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hc₀' : (c₁ : ℝ) * (2 : ℝ) ^ ((c₁ : ℝ) * 130) ≤ ((c₀ + c₁ * (D + 65) : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (c₁ : ℝ) * ((D : ℝ) + 65) := by positivity
    linarith
  calc (c₁ : ℝ) * ((n : ℝ) + 2) ^ c₁ * (2 : ℝ) ^ ((c₁ : ℝ) * min (expM3 m) (expN3 n))
      ≤ (c₁ : ℝ) * (2 : ℝ) ^ ((c₁ : ℝ) * (64 * s + 128)) * (2 : ℝ) ^ ((c₁ : ℝ) * (((D : ℝ) + 1) * s + 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hc0) hexp (by positivity) (by positivity)
    _ = ((c₁ : ℝ) * (2 : ℝ) ^ ((c₁ : ℝ) * 130)) * (2 : ℝ) ^ (((c₁ * (D + 65) : ℕ) : ℝ) * s) := by
        rw [mul_assoc, hcomb]
        ring
    _ ≤ ((c₀ + c₁ * (D + 65) : ℕ) : ℝ) * (2 : ℝ) ^ (((c₀ + c₁ * (D + 65) : ℕ) : ℝ) * s) :=
        mul_le_mul hc₀' (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hcs hs0))
          (by positivity) (by positivity)

/-! ### The bound in n, written with a square root -/

/-- The bound in n of proof/machines/Wrap, with the constant 9c in place of c in front, is the bound
c'·2^{c'·n·lg lg(n+4)/√(lg(n+4))} with c' = 9c. -/
theorem boundNK_le_expN3 (c n : ℕ) :
    SatM.boundNK (SatK.rN 1 (1 / 2)) c 3 n ≤ ⌊((9 * c : ℕ) : ℝ) * (2 : ℝ) ^ (((9 * c : ℕ) : ℝ) * expN3 n)⌋₊ := by
  unfold SatM.boundNK
  refine Nat.floor_le_floor ?_
  rw [expN3_eq]
  push_cast
  have hc : (c : ℝ) ≤ 9 * c := by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have e : (c : ℝ) * 3 ^ 2 * n * SatK.rN 1 (1 / 2) n = 9 * c * (n * SatK.rN 1 (1 / 2) n) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-! ### One machine for all the bounds -/

/-- **The sharpest bounds for 3-SAT that the formalization gives, for one machine.** -/
theorem oneMachineBest : OneMachineBest := by
  obtain ⟨M, C, hfin, hM⟩ := NamesInOrder.generalFormFollowsAsPropositions CountedRoute.mainTheoremHolds
  obtain ⟨⟨pre, N, q, hpre, hN, hW⟩, hall⟩ := counterCanBeWrappedAndEveryWrapperDecides M C hfin hM
  obtain ⟨hδ, hrate⟩ := hall pre hpre.2 N q hW
  obtain ⟨a, d, hL⟩ := length_encC_pad4_le
  obtain ⟨c, hc⟩ := wrapped_time_le_nm q (9 * C) C a d
  have hNM : DecidesTMNM N (boundNM c) := decidesTMNM_of_wraps_counter hpre.2 hM hW hL hc
  obtain ⟨c', hc'⟩ := hrate
  refine ⟨N, hN, ⟨c, hNM⟩, ⟨9 * c', hc'.mono (boundNK_le_expN3 c')⟩, ?_, ?_, hδ⟩
  · intro α hα
    rcases le_or_gt 0 α with h0 | h0
    · obtain ⟨C', hC'⟩ := boundNK_le_rateBound c' h0 hα
      exact ⟨C', hc'.mono hC'⟩
    · obtain ⟨C', hC'⟩ := boundNK_le_rateBound c' le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
      exact ⟨C', hc'.mono fun n => (hC' n).trans (Sat3.rateBound_anti C' h0.le n)⟩
  · intro D
    obtain ⟨c'', hc''⟩ := boundNM_le_sparse c D
    exact ⟨c'', fun n φ hφ hm =>
      let ⟨b, hb, ⟨ev⟩⟩ := hNM n φ hφ
      ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (hc'' n φ.length hm)⟩⟩⟩⟩

end BestRate
