import Architect
import PrimeNumberTheoremAnd.primegaps

namespace Lcm_gk



open ArithmeticFunction hiding log
open Finset Nat Real

-- Define the new prime gap result
noncomputable def dusart_2018_5000 : PrimeGaps.PrimeIntervalResult True :=
{ X0 := 468991632
  lower := fun x => x
  upper := fun x => x / (5000 * (Real.log x) ^ (2 : ℝ))
  thm := by
    intro _ x hx
    sorry }

noncomputable abbrev prime_gap_pkg := dusart_2018_5000
noncomputable abbrev X₀ : ℕ := Nat.ceil prime_gap_pkg.X0

lemma X₀_ge_pkg : (prime_gap_pkg.X0 : ℝ) ≤ (X₀ : ℝ) := by
  simpa [X₀] using (Nat.le_ceil prime_gap_pkg.X0)

lemma X₀_eq : X₀ = 468991632 := by
  simp [X₀, prime_gap_pkg, dusart_2018_5000]

lemma prime_gap_bound {x : ℝ} (hx : x ≥ X₀) :
    PrimeGaps.HasPrimeInInterval (prime_gap_pkg.lower x) (prime_gap_pkg.upper x) := by
  have hx' : x ≥ prime_gap_pkg.X0 := le_trans X₀_ge_pkg hx
  simpa [prime_gap_pkg, dusart_2018_5000] using (prime_gap_pkg.thm trivial hx')

structure Gatekeeper where
  n : ℕ
  hn : n ≥ 1
  p : Fin 3 → ℕ
  hp : ∀ i, Nat.Prime (p i)
  hp_mono : StrictMono p
  q : Fin 3 → ℕ
  hq : ∀ i, Nat.Prime (q i)
  hq_mono : StrictMono q
  h_ord_1 : √(n : ℝ) < p 0
  h_ord_2 : p 2 < q 0
  h_ord_3 : q 2 < n
  hsqrt_ge : √(n : ℝ) ≥ X₀
  log_X₀_gt : Real.log X₀ > 19.9
  hlog : log √(n : ℝ) ≥ 19.9
  ratio_def : ∀ x : ℝ, prime_gap_pkg.upper x / prime_gap_pkg.lower x = 1 / (5000 * (log x) ^ (2 : ℝ))
  hε_pos : 0 < 1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))
  log_X₀_pos : 0 < Real.log X₀
  exists_p_primes_hsqrt_ge : √(n : ℝ) ≥ X₀
  exists_p_primes_hx_pos : 0 < √(n : ℝ)
  exists_p_primes_hlog_pos : 0 < log ( √(n : ℝ) )
  exists_p_primes_hx1_ge :
    ∀ {ε : ℝ} (hε_pos : 0 < ε), √(n : ℝ) * (1 + ε) ≥ X₀
  exists_p_primes_hx2_ge :
    ∀ {ε : ℝ} (hε_pos : 0 < ε), √(n : ℝ) * (1 + ε) ^ 2 ≥ X₀
  exists_q_primes_hε_small :
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤ 1 / (5000 * 19.9 ^ 2)
  exists_q_primes_hx_ge_2 : √(n : ℝ) ≥ 2
  exists_q_primes_hy₀_ge :
    (n : ℝ) /
        (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ 3 ≥ X₀
  exists_q_primes_hy₁_hy₂ :
    ∀ {ε : ℝ} (hn_sq_pos : 0 < (n : ℝ)) (hε_nonneg : 0 ≤ ε)
      (h1ε_pos : 0 < 1 + ε) (h1ε2_pos : 0 < (1 + ε) ^ 2)
      (hy₀_ge : (n : ℝ) / (1 + ε) ^ 3 ≥ X₀),
      (n : ℝ) / (1 + ε) ^ 2 ≥ X₀ ∧ (n : ℝ) / (1 + ε) ≥ X₀
  exists_q_primes_hy_bounds :
    ∀ {ε : ℝ} (hε_def : ε =
        prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)))
      (hn_sq_pos : 0 < (n : ℝ))
      (hε_nonneg : 0 ≤ ε) (h1ε_pos : 0 < 1 + ε)
      (h1ε2_pos : 0 < (1 + ε) ^ 2),
      (n : ℝ) / (1 + ε) ^ 3 ≥ X₀ ∧
        (n : ℝ) / (1 + ε) ^ 2 ≥ X₀ ∧ (n : ℝ) / (1 + ε) ≥ X₀
  exists_p_primes :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i,
        p i ≤ √(n : ℝ) *
          (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^
            (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0
  exists_q_primes :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3,
        n *
            (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^
              (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧
      q 2 < n
  p_eq : (exists_p_primes).choose = p
  q_eq : (exists_q_primes).choose = q
  prod_q_ge :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes).choose i) ≤
      ∏ i : Fin 3,
        (1 + (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^
          ((i : ℕ) + 1 : ℝ) / n)
  prod_p_ge :
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes).choose i * ((exists_p_primes).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 /
          ((1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^
            (2 * (i : ℕ) + 2 : ℝ) * (n + √n)))
  pq_ratio_ge :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes).choose i : ℝ))
    / ∏ i, ((exists_q_primes).choose i : ℝ) ≥
    1 - 4 *
      (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ 12 /
        n ^ (3 / 2 : ℝ)
  inv_cube_log_sqrt_le_aux :
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤ 0.0000051
  inv_cube_log_sqrt_le :
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤ 0.0000051
  inv_n_pow_3_div_2_le :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / (n : ℝ))
  inv_n_add_sqrt_ge_aux :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
  inv_n_add_sqrt_ge :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
  prod_epsilon_le :
    ∀ {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)),
      ∏ i : Fin 3, (1 + (1.0000051 : ℝ) ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
        1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3
  prod_epsilon_ge :
    ∀ {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)),
      (∏ i : Fin 3,
        (1 + ε / ((1.0000051 : ℝ) ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
          (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * (1.0000051 : ℝ) ^ 12 / X₀ * ε) ≥
        1 + 3.36683 * ε - 0.01 * ε ^ 2
  final_comparison :
    ∀ {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)),
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2
  criterion_mk_hn_sq : n ≥ 1
  criterion_mk_h_ord_2 :
    (exists_p_primes).choose 2 < (exists_q_primes).choose 0
  criterion_mk_h_crit_h₁ :
    1 - (4 : ℝ) * (∏ i, (exists_p_primes).choose i : ℝ) /
      ∏ i, ((exists_q_primes).choose i : ℝ) ≥
      1 - 4 * (1 + 0.0000051) ^ 12 * ((1 / X₀) * (1 / n))
  criterion_mk_h_crit_h₁_nonneg :
    0 ≤ 1 - 4 * (1 + 0.0000051 : ℝ) ^ 12 * ((1 / X₀) * (1 / n))
  criterion_mk_h_crit_hn_sq' :
    (0 : ℝ) ≤ 1 / ↑n ∧ (1 : ℝ) / ↑n ≤ 1 / X₀ ^ 2




-- The ratio for the new gap bound: 1 / (5000 * (log x)^2)
@[simp] lemma ratio_def (x : ℝ) :
    prime_gap_pkg.upper x / prime_gap_pkg.lower x = 1 / (5000 * (log x) ^ (2 : ℝ)) := by
  by_cases hx : x = 0
  · simp [prime_gap_pkg, dusart_2018_5000, hx]
  · calc
      prime_gap_pkg.upper x / prime_gap_pkg.lower x =
          (x / (5000 * (log x) ^ (2 : ℝ))) / x := by
        simp [prime_gap_pkg, dusart_2018_5000]
      _ = (x * (1 / (5000 * (log x) ^ (2 : ℝ)))) / x := by
        simp [div_eq_mul_inv]
      _ = 1 / (5000 * (log x) ^ (2 : ℝ)) := by
        simpa [mul_comm] using (mul_div_cancel_left₀ (1 / (5000 * (log x) ^ (2 : ℝ))) hx)

lemma ratio_pos {x : ℝ} (hx : 0 < log x) :
    0 < prime_gap_pkg.upper x / prime_gap_pkg.lower x := by
  have : 0 < 1 / (5000 * (log x) ^ (2 : ℝ)) := by positivity [hx]
  simpa [ratio_def] using this

lemma hsqrt_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn_sq : (n : ℝ) ≥ X₀ ^ 2)

-- log(468991632) ≈ 19.966, so log X₀ > 19.9
lemma log_468991632_gt : Real.log (468991632 : ℝ) > 19.9 := by
  rw [gt_iff_lt, show (19.9 : ℝ) = 199 / (10 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

lemma log_X₀_gt : Real.log X₀ > 19.9 := by
  have hX0 : (468991632 : ℝ) ≤ X₀ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using X₀_ge_pkg
  have hlog_468991632 : (19.9 : ℝ) < Real.log (468991632 : ℝ) := by
    simpa [gt_iff_lt] using log_468991632_gt
  have hlog_le : Real.log (468991632 : ℝ) ≤ Real.log X₀ := by
    have hpos : (0 : ℝ) < (468991632 : ℝ) := by norm_num
    exact log_le_log hpos hX0
  have hlog := lt_of_lt_of_le hlog_468991632 hlog_le
  simpa [gt_iff_lt] using hlog

lemma X₀_ge_2 : (2 : ℝ) ≤ X₀ := by
  have hX0 : (468991632 : ℝ) ≤ X₀ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using X₀_ge_pkg
  linarith

lemma X₀_pos : (0 : ℝ) < X₀ := by
  linarith [X₀_ge_2]

lemma n_pos_of_hn_sq {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : (0 : ℝ) < n := by
  have hn_sq' : (X₀ : ℝ) ^ 2 ≤ n := by exact_mod_cast hn_sq
  exact (pow_pos X₀_pos 2).trans_le hn_sq'

lemma hlog {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : log √(n : ℝ) ≥ 19.9 := by
  calc log √(n : ℝ) ≥ log (X₀ : ℝ) :=
        log_le_log X₀_pos (hsqrt_ge hn_sq)
    _ ≥ 19.9 := log_X₀_gt.le

lemma hε_pos {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    0 < 1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) := by
  have hlog_pos : 0 < log √(n : ℝ) := by linarith [hlog hn_sq]
  have hl_pos :
      0 < prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) := ratio_pos hlog_pos
  linarith

lemma log_X₀_pos : 0 < Real.log X₀ := by linear_combination log_X₀_gt

lemma exists_p_primes_hsqrt_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ :=
  hsqrt_ge hn_sq

lemma exists_p_primes_hx_pos {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : 0 < √(n : ℝ) :=
  X₀_pos.trans_le (exists_p_primes_hsqrt_ge hn_sq)

lemma exists_p_primes_hlog_pos {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : 0 < log ( √(n : ℝ) ) := by
  positivity [hlog hn_sq]

lemma exists_p_primes_hx1_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) {ε : ℝ} (hε_pos : 0 < ε) :
    √(n : ℝ) * (1 + ε) ≥ X₀ := by
  have hx_pos := exists_p_primes_hx_pos hn_sq
  exact (hsqrt_ge hn_sq).trans (le_mul_of_one_le_right hx_pos.le (by linarith [hε_pos]))

lemma exists_p_primes_hx2_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) {ε : ℝ} (hε_pos : 0 < ε) :
    √(n : ℝ) * (1 + ε) ^ 2 ≥ X₀ := by
  have hx_pos := exists_p_primes_hx_pos hn_sq
  exact (hsqrt_ge hn_sq).trans
    (le_mul_of_one_le_right hx_pos.le (by nlinarith [hε_pos, sq_nonneg ε]))

-- The bound 1/(5000 * 19.9^2) ≈ 0.0000050377
lemma exists_q_primes_hε_small {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤ 1 / (5000 * 19.9 ^ 2) := by
  have hlog_ge : log √(n : ℝ) ≥ 19.9 := hlog hn_sq
  have hpos : 0 < log √(n : ℝ) := by positivity [hlog hn_sq]
  have hpow : (19.9 : ℝ) ^ (2 : ℝ) ≤ (log √(n : ℝ)) ^ (2 : ℝ) :=
    rpow_le_rpow (by nlinarith) hlog_ge (by grind)
  have hmul : 5000 * (19.9 : ℝ) ^ (2 : ℝ) ≤ 5000 * (log √(n : ℝ)) ^ (2 : ℝ) := by
    apply mul_le_mul_of_nonneg_left hpow
    norm_num
  have hpow_pos : 0 < 5000 * (19.9 : ℝ) ^ (2 : ℝ) := by positivity
  have hdiv : 1 / (5000 * (log √(n : ℝ)) ^ (2 : ℝ)) ≤ 1 / (5000 * (19.9 : ℝ) ^ (2 : ℝ)) :=
    one_div_le_one_div_of_le hpow_pos hmul
  simpa [ratio_def] using hdiv

lemma exists_q_primes_hx_ge_2 {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ 2 := by
  have h2 : (2 : ℝ) ≤ X₀ := X₀_ge_2
  exact h2.trans (hsqrt_ge hn_sq)

lemma exists_q_primes_hy₀_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    (n : ℝ) /
        (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ 3 ≥ X₀ := by
  let x := √(n : ℝ)
  let ε := prime_gap_pkg.upper x / prime_gap_pkg.lower x
  have hn_sq_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  have hx_ge : x ≥ X₀ := hsqrt_ge hn_sq
  have hlog_pos : 0 < log x := by linarith [hlog hn_sq]
  have hε_pos : 0 < ε := by
    simpa [ε] using (ratio_pos hlog_pos)
  have hε_small : ε ≤ 1 / (5000 * 19.9 ^ 2) := by
    simpa [x, ε] using exists_q_primes_hε_small hn_sq
  have h1ε3_pos : 0 < (1 + ε) ^ 3 := by
    have h1ε_pos : 0 < 1 + ε := by linarith [hε_pos]
    exact pow_pos h1ε_pos 3
  have h1ε_nonneg : 0 ≤ 1 + ε := by linarith [hε_pos]
  have h1ε3_le_2 : (1 + ε) ^ 3 ≤ 2 := by
    have h1 : (1 + ε) ^ 3 ≤ (1 + 1 / (5000 * 19.9 ^ 2)) ^ 3 := by
      apply pow_le_pow_left₀ h1ε_nonneg (by linarith [hε_small])
    calc (1 + ε) ^ 3 ≤ (1 + 1 / (5000 * 19.9 ^ 2)) ^ 3 := h1
      _ ≤ 2 := by norm_num
  have hn_sq_eq_x2 : (n : ℝ) = x ^ 2 := (sq_sqrt hn_sq_pos.le).symm
  calc (n : ℝ) / (1 + ε) ^ 3 = x ^ 2 / (1 + ε) ^ 3 := by rw [hn_sq_eq_x2]
    _ ≥ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) h1ε3_pos h1ε3_le_2
    _ ≥ X₀ ^ 2 / 2 := by
      apply div_le_div_of_nonneg_right (sq_le_sq' (by linarith) hx_ge)
      norm_num
    _ ≥ X₀ := by nlinarith [X₀_ge_2]


lemma exists_q_primes_hy₁_hy₂ {n : ℕ} {ε : ℝ} (hn_sq_pos : 0 < (n : ℝ))
    (hε_nonneg : 0 ≤ ε) (h1ε_pos : 0 < 1 + ε) (h1ε2_pos : 0 < (1 + ε) ^ 2)
    (hy₀_ge : (n : ℝ) / (1 + ε) ^ 3 ≥ X₀) :
    (n : ℝ) / (1 + ε) ^ 2 ≥ X₀ ∧ (n : ℝ) / (1 + ε) ≥ X₀ := by
  have h1ε2_le_1ε3 : (1 + ε) ^ 2 ≤ (1 + ε) ^ 3 :=
    by nlinarith [hε_nonneg]
  have h1ε_le_1ε2 : 1 + ε ≤ (1 + ε) ^ 2 :=
    by nlinarith [hε_nonneg]
  have hy₁_ge : (n : ℝ) / (1 + ε) ^ 2 ≥ X₀ := le_trans hy₀_ge
    (div_le_div_of_nonneg_left hn_sq_pos.le h1ε2_pos h1ε2_le_1ε3)
  have hy₂_ge : (n : ℝ) / (1 + ε) ≥ X₀ := le_trans hy₁_ge
    (div_le_div_of_nonneg_left hn_sq_pos.le h1ε_pos h1ε_le_1ε2)
  exact ⟨hy₁_ge, hy₂_ge⟩

lemma exists_q_primes_hy_bounds {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) {ε : ℝ}
    (hε_def : ε =
      prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)))
    (hn_sq_pos : 0 < (n : ℝ)) (hε_nonneg : 0 ≤ ε) (h1ε_pos : 0 < 1 + ε)
    (h1ε2_pos : 0 < (1 + ε) ^ 2) :
    (n : ℝ) / (1 + ε) ^ 3 ≥ X₀ ∧ (n : ℝ) / (1 + ε) ^ 2 ≥ X₀ ∧ (n : ℝ) / (1 + ε) ≥ X₀ := by
  have hy₀_ge : (n : ℝ) / (1 + ε) ^ 3 ≥ X₀ := by
    simpa [hε_def] using exists_q_primes_hy₀_ge hn_sq
  have hy₁₂ := exists_q_primes_hy₁_hy₂ (hn_sq_pos := hn_sq_pos) (hε_nonneg := hε_nonneg)
    (h1ε_pos := h1ε_pos) (h1ε2_pos := h1ε2_pos) hy₀_ge
  exact ⟨hy₀_ge, hy₁₂.1, hy₁₂.2⟩


lemma exists_p_primes {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i,
        p i ≤ √(n : ℝ) *
          (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^
            (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  let x := √(n : ℝ)
  have hx_pos : 0 < x := exists_p_primes_hx_pos hn_sq
  have hlog_pos : 0 < log x := exists_p_primes_hlog_pos hn_sq
  set ε := prime_gap_pkg.upper x / prime_gap_pkg.lower x with hε_def
  have upper {y : ℝ} (hy : 0 < y) (hlog_ge : log y ≥ log x) {p : ℕ}
      (hp : (p : ℝ) ≤ y + y * (prime_gap_pkg.upper y / prime_gap_pkg.lower y)) :
        (p : ℝ) ≤ y * (1 + ε) := by
    have h :
        y * (prime_gap_pkg.upper y / prime_gap_pkg.lower y) ≤
          y * (prime_gap_pkg.upper x / prime_gap_pkg.lower x) := by
      have hpow : (log x) ^ (2 : ℝ) ≤ (log y) ^ (2 : ℝ) :=
        rpow_le_rpow hlog_pos.le hlog_ge (by grind)
      have hmul : 5000 * (log x) ^ (2 : ℝ) ≤ 5000 * (log y) ^ (2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hpow
        norm_num
      have hpos : 0 < 5000 * (log x) ^ (2 : ℝ) := by positivity [hlog_pos]
      have h' :
          prime_gap_pkg.upper y / prime_gap_pkg.lower y ≤
            prime_gap_pkg.upper x / prime_gap_pkg.lower x := by
        simpa [ratio_def] using (one_div_le_one_div_of_le hpos hmul)
      exact mul_le_mul_of_nonneg_left h' hy.le
    calc (p : ℝ) ≤ y + y * (prime_gap_pkg.upper y / prime_gap_pkg.lower y) := hp
      _ ≤ y + y * (prime_gap_pkg.upper x / prime_gap_pkg.lower x) := add_le_add_right h y
      _ = y * (1 + ε) := by simp [hε_def, mul_add]
  have hε_pos : 0 < ε := by
    simpa [hε_def] using (ratio_pos hlog_pos)
  have hx1_ge := exists_p_primes_hx1_ge hn_sq hε_pos
  have hx2_ge := exists_p_primes_hx2_ge hn_sq hε_pos
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ :=
    prime_gap_bound (x := x) (exists_p_primes_hsqrt_ge hn_sq)
  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ :=
    prime_gap_bound (x := x * (1 + ε)) hx1_ge
  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ :=
    prime_gap_bound (x := x * (1 + ε) ^ 2) hx2_ge
  have hp₀_lb' : (x : ℝ) < p₀ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hp₀_lb
  have hp₁_lb' : (x * (1 + ε) : ℝ) < p₁ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hp₁_lb
  have hp₂_lb' : (x * (1 + ε) ^ 2 : ℝ) < p₂ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hp₂_lb
  have hp₀_ub_log : (p₀ : ℝ) ≤ x + x / (5000 * (log x) ^ (2 : ℝ)) := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hp₀_ub
  have hp₁_ub_log :
      (p₁ : ℝ) ≤ x * (1 + ε) + x * (1 + ε) / (5000 * (log (x * (1 + ε))) ^ (2 : ℝ)) := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hp₁_ub
  have hp₂_ub_log :
      (p₂ : ℝ) ≤ x * (1 + ε) ^ 2 +
        x * (1 + ε) ^ 2 / (5000 * (log (x * (1 + ε) ^ (2 : ℕ))) ^ (2 : ℝ)) := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hp₂_ub
  have hp₀_ub_raw : (p₀ : ℝ) ≤ x + x * (prime_gap_pkg.upper x / prime_gap_pkg.lower x) := by
    simpa [ratio_def] using hp₀_ub_log
  have hp₁_ub_raw :
      (p₁ : ℝ) ≤ x * (1 + ε) +
        x * (1 + ε) * (prime_gap_pkg.upper (x * (1 + ε)) / prime_gap_pkg.lower (x * (1 + ε))) := by
    simpa [ratio_def] using hp₁_ub_log
  have hp₂_ub_raw :
      (p₂ : ℝ) ≤ x * (1 + ε) ^ 2 +
        x * (1 + ε) ^ 2 *
          (prime_gap_pkg.upper (x * (1 + ε) ^ 2) / prime_gap_pkg.lower (x * (1 + ε) ^ 2)) := by
    simpa [ratio_def] using hp₂_ub_log
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := by
    refine upper hx_pos le_rfl ?_
    exact hp₀_ub_raw
  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    have hy : 0 < x * (1 + ε) := by positivity [hx_pos, hε_pos]
    have hlog_ge : log (x * (1 + ε)) ≥ log x := by
      have hx_le : x ≤ x * (1 + ε) := by
        have h1 : (1 : ℝ) ≤ 1 + ε := by linarith [hε_pos]
        exact (le_mul_of_one_le_right hx_pos.le h1)
      exact log_le_log hx_pos hx_le
    have := upper hy hlog_ge hp₁_ub_raw
    linarith [sq (1 + ε), this]
  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    have hy : 0 < x * (1 + ε) ^ 2 := by positivity [hx_pos, hε_pos]
    have hlog_ge : Real.log (x * (1 + ε) ^ (2 : ℕ)) ≥ Real.log x := by
      have hx_le : x ≤ x * (1 + ε) ^ (2 : ℕ) := by
        have h1 : (1 : ℝ) ≤ (1 + ε) ^ (2 : ℕ) := by nlinarith [sq_nonneg ε, hε_pos.le]
        exact (le_mul_of_one_le_right hx_pos.le h1)
      exact log_le_log hx_pos hx_le
    have := upper hy hlog_ge hp₂_ub_raw
    linarith [pow_succ (1 + ε) 2, this]
  refine ⟨![p₀, p₁, p₂], fun i ↦ by fin_cases i <;> assumption,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
      fin_cases i
      · exact cast_lt.mp (hp₀_ub'.trans_lt hp₁_lb')
      · exact cast_lt.mp (hp₁_ub'.trans_lt hp₂_lb'), fun i ↦ ?_, hp₀_lb'⟩
  fin_cases i <;> norm_num
  · convert hp₀_ub' using 2
  · convert hp₁_ub' using 2
  · convert hp₂_ub' using 2



lemma exists_q_primes {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3,
        n *
            (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^
              (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧
      q 2 < n := by
  let x := √(n : ℝ)
  have hx_pos : 0 < x := exists_p_primes_hx_pos hn_sq
  have hlog_pos : 0 < log x := exists_p_primes_hlog_pos hn_sq
  set ε := prime_gap_pkg.upper x / prime_gap_pkg.lower x with hε_def
  have hε_pos : 0 < ε := by
    simpa [hε_def] using (ratio_pos hlog_pos)
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  have h1ε_pos : 0 < 1 + ε := by linarith
  have hn_sq_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  have hn_sq_eq_x2 : (n : ℝ) = x ^ 2 := (sq_sqrt hn_sq_pos.le).symm
  -- Show that ε is small (ε ≤ 1/(5000 * 19.9²))
  have hε_small : ε ≤ 1 / (5000 * 19.9 ^ 2) := by
    simpa [hε_def] using exists_q_primes_hε_small hn_sq
  have h1ε3_pos : 0 < (1 + ε) ^ 3 := by
    exact pow_pos h1ε_pos 3
  have h1ε2_pos : 0 < (1 + ε) ^ 2 := by
    exact pow_pos h1ε_pos 2
  have h1ε3_le_2 : (1 + ε) ^ 3 ≤ 2 := by
    have h1 : (1 + ε) ^ 3 ≤ (1 + 1 / (5000 * 19.9 ^ 2)) ^ 3 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    calc (1 + ε) ^ 3 ≤ (1 + 1 / (5000 * 19.9 ^ 2)) ^ 3 := h1
      _ ≤ 2 := by norm_num
  have h1ε2_le_1ε3 : (1 + ε) ^ 2 ≤ (1 + ε) ^ 3 := by
      nlinarith [hε_nonneg]
  have h1ε_le_1ε2 : 1 + ε ≤ (1 + ε) ^ 2 :=
    by nlinarith [hε_nonneg]
  -- Define y_i = n / (1 + ε)^(3-i), and record lower bounds.
  have hy_bounds :=
    exists_q_primes_hy_bounds (hn_sq := hn_sq) (hε_def := hε_def) (hn_sq_pos := hn_sq_pos)
      (hε_nonneg := hε_nonneg) (h1ε_pos := h1ε_pos) (h1ε2_pos := h1ε2_pos)
  have hy₀_ge := hy_bounds.1
  have hy₁_ge := hy_bounds.2.1
  have hy₂_ge := hy_bounds.2.2
  -- Apply Dusart to get primes
  obtain ⟨q₀, hq₀_prime, hq₀_lb, hq₀_ub⟩ :=
    prime_gap_bound (x := n / (1 + ε) ^ 3) hy₀_ge
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ :=
    prime_gap_bound (x := n / (1 + ε) ^ 2) hy₁_ge
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ :=
    prime_gap_bound (x := n / (1 + ε)) hy₂_ge
  have hq₀_lb' : (n / (1 + ε) ^ 3 : ℝ) < q₀ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hq₀_lb
  have hq₁_lb' : (n / (1 + ε) ^ 2 : ℝ) < q₁ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hq₁_lb
  have hq₂_lb' : (n / (1 + ε) : ℝ) < q₂ := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hq₂_lb
  have hq₀_ub_log :
      (q₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 +
        ((n : ℝ) / (1 + ε) ^ 3) / (5000 * (Real.log ((n : ℝ) / (1 + ε) ^ 3)) ^ (2 : ℝ)) := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hq₀_ub
  have hq₁_ub_log :
      (q₁ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 +
        ((n : ℝ) / (1 + ε) ^ 2) / (5000 * (Real.log ((n : ℝ) / (1 + ε) ^ 2)) ^ (2 : ℝ)) := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hq₁_ub
  have hq₂_ub_log :
      (q₂ : ℝ) ≤ (n : ℝ) / (1 + ε) +
        ((n : ℝ) / (1 + ε)) / (5000 * (Real.log ((n : ℝ) / (1 + ε))) ^ (2 : ℝ)) := by
    simpa [prime_gap_pkg, dusart_2018_5000] using hq₂_ub
  have hq₀_ub_raw :
      (q₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 +
        ((n : ℝ) / (1 + ε) ^ 3) *
          (prime_gap_pkg.upper ((n : ℝ) / (1 + ε) ^ 3) /
            prime_gap_pkg.lower ((n : ℝ) / (1 + ε) ^ 3)) := by
    have hq₀_ub_log_mul :
        (q₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 +
          ((n : ℝ) / (1 + ε) ^ 3) *
            (1 / (5000 * (Real.log ((n : ℝ) / (1 + ε) ^ 3)) ^ (2 : ℝ))) := by
      simpa [div_eq_mul_inv] using hq₀_ub_log
    simpa [ratio_def] using hq₀_ub_log_mul
  have hq₁_ub_raw :
      (q₁ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 +
        ((n : ℝ) / (1 + ε) ^ 2) *
          (prime_gap_pkg.upper ((n : ℝ) / (1 + ε) ^ 2) /
            prime_gap_pkg.lower ((n : ℝ) / (1 + ε) ^ 2)) := by
    have hq₁_ub_log_mul :
        (q₁ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 +
          ((n : ℝ) / (1 + ε) ^ 2) *
            (1 / (5000 * (Real.log ((n : ℝ) / (1 + ε) ^ 2)) ^ (2 : ℝ))) := by
      simpa [div_eq_mul_inv] using hq₁_ub_log
    simpa [ratio_def] using hq₁_ub_log_mul
  have hq₂_ub_raw :
      (q₂ : ℝ) ≤ (n : ℝ) / (1 + ε) +
        ((n : ℝ) / (1 + ε)) *
          (prime_gap_pkg.upper ((n : ℝ) / (1 + ε)) /
            prime_gap_pkg.lower ((n : ℝ) / (1 + ε))) := by
    have hq₂_ub_log_mul :
        (q₂ : ℝ) ≤ (n : ℝ) / (1 + ε) +
          ((n : ℝ) / (1 + ε)) *
            (1 / (5000 * (Real.log ((n : ℝ) / (1 + ε))) ^ (2 : ℝ))) := by
      simpa [div_eq_mul_inv] using hq₂_ub_log
    simpa [ratio_def] using hq₂_ub_log_mul
  -- Show y_i ≥ x (needed for upper bound helper)
  have hx_ge_2 : x ≥ 2 := by simpa using exists_q_primes_hx_ge_2 hn_sq
  have hy₀_ge_x : n / (1 + ε) ^ 3 ≥ x := by
    calc n / (1 + ε) ^ 3 = x ^ 2 / (1 + ε) ^ 3 := by rw [hn_sq_eq_x2]
      _ ≥ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by grind) h1ε3_le_2
      _ ≥ x := by rw [ge_iff_le, le_div_iff₀' (by norm_num : (0 : ℝ) < 2)]; nlinarith
  have hy₁_ge_x : n / (1 + ε) ^ 2 ≥ x := le_trans hy₀_ge_x
    (div_le_div_of_nonneg_left hn_sq_pos.le h1ε2_pos h1ε2_le_1ε3)
  have hy₂_ge_x : n / (1 + ε) ≥ x := le_trans hy₁_ge_x
    (div_le_div_of_nonneg_left hn_sq_pos.le h1ε_pos h1ε_le_1ε2)
  -- Upper bound helper: show q_i upper bound implies q_i ≤ next threshold
  have upper {y : ℝ} (hy_pos : 0 < y) (hy_ge : y ≥ x) {q : ℕ}
      (hq : (q : ℝ) ≤ y + y * (prime_gap_pkg.upper y / prime_gap_pkg.lower y)) :
        (q : ℝ) ≤ y * (1 + ε) := by
    have hlog_ge : log y ≥ log x := log_le_log hx_pos hy_ge
    have h :
        y * (prime_gap_pkg.upper y / prime_gap_pkg.lower y) ≤
          y * (prime_gap_pkg.upper x / prime_gap_pkg.lower x) := by
      have hpow : (log x) ^ (2 : ℝ) ≤ (log y) ^ (2 : ℝ) :=
        rpow_le_rpow hlog_pos.le hlog_ge (by grind)
      have hmul : 5000 * (log x) ^ (2 : ℝ) ≤ 5000 * (log y) ^ (2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hpow
        norm_num
      have hpos : 0 < 5000 * (log x) ^ (2 : ℝ) := by positivity [hlog_pos]
      have h' :
          prime_gap_pkg.upper y / prime_gap_pkg.lower y ≤
            prime_gap_pkg.upper x / prime_gap_pkg.lower x := by
        simpa [ratio_def] using (one_div_le_one_div_of_le hpos hmul)
      exact mul_le_mul_of_nonneg_left h' hy_pos.le
    calc (q : ℝ) ≤ y + y * (prime_gap_pkg.upper y / prime_gap_pkg.lower y) := hq
      _ ≤ y + y * (prime_gap_pkg.upper x / prime_gap_pkg.lower x) := add_le_add_right h y
      _ = y * (1 + ε) := by simp [hε_def, mul_add]
  -- Get upper bounds
  have hq₀_ub' : (q₀ : ℝ) ≤ n / (1 + ε) ^ 2 := by
    have := upper (by positivity) hy₀_ge_x (by
      exact hq₀_ub_raw)
    calc (q₀ : ℝ) ≤ (n / (1 + ε) ^ 3) * (1 + ε) := this
      _ = n / (1 + ε) ^ 2 := by field_simp
  have hq₁_ub' : (q₁ : ℝ) ≤ n / (1 + ε) := by
    have := upper (by positivity) hy₁_ge_x (by
      exact hq₁_ub_raw)
    calc (q₁ : ℝ) ≤ (n / (1 + ε) ^ 2) * (1 + ε) := this
      _ = n / (1 + ε) := by field_simp
  have hq₂_ub' : (q₂ : ℝ) ≤ n := by
    have := upper (by positivity) hy₂_ge_x (by
      exact hq₂_ub_raw)
    calc (q₂ : ℝ) ≤ (n / (1 + ε)) * (1 + ε) := this
      _ = n := by field_simp
  -- StrictMono: q₀ < q₁ < q₂
  have hq₀_lt_q₁ : q₀ < q₁ := Nat.cast_lt.mp (hq₀_ub'.trans_lt hq₁_lb')
  have hq₁_lt_q₂ : q₁ < q₂ := Nat.cast_lt.mp (hq₁_ub'.trans_lt hq₂_lb')
  -- q₂ < n: the Dusart interval has upper bound y₂ * (1 + 1/(5000*(log y₂)²)) < y₂ * (1 + ε) = n
  have hq₂_lt_n : q₂ < n := by
    have hy₂_pos : 0 < (n : ℝ) / (1 + ε) := by positivity
    have hy₂_lt_n : n / (1 + ε) < n := div_lt_self hn_sq_pos (by linarith)
    have hlog_y₂_pos : 0 < log (n / (1 + ε)) := log_pos (by linarith : 1 < (n : ℝ) / (1 + ε))
    have hx_lt_y₂ : x < n / (1 + ε) := by
      have h1ε_gt_one : (1 : ℝ) < 1 + ε := by linarith [hε_pos]
      have h1ε_pos' : 0 < 1 + ε := by linarith [hε_pos]
      have h1ε_sq_gt_one : (1 : ℝ) < (1 + ε) ^ 2 :=
        one_lt_pow₀ h1ε_gt_one (by decide : (2 : ℕ) ≠ 0)
      have h1ε_lt_1ε3 : (1 + ε) < (1 + ε) ^ 3 := by
        have := mul_lt_mul_of_pos_left h1ε_sq_gt_one h1ε_pos'
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
      have h1 : n / (1 + ε) ^ 3 < n / (1 + ε) :=
        div_lt_div_of_pos_left hn_sq_pos h1ε_pos h1ε_lt_1ε3
      calc x ≤ n / (1 + ε) ^ 3 := hy₀_ge_x
        _ < n / (1 + ε) := h1
    have hlog_y₂_gt : log (n / (1 + ε)) > log x := log_lt_log hx_pos hx_lt_y₂
    have hq₂_strict : (q₂ : ℝ) < n := by
      have hq₂_ub_log :
          (q₂ : ℝ) ≤ (n : ℝ) / (1 + ε) +
            ((n : ℝ) / (1 + ε)) / (5000 * (Real.log ((n : ℝ) / (1 + ε))) ^ (2 : ℝ)) := by
        simpa [prime_gap_pkg, dusart_2018_5000] using hq₂_ub
      calc (q₂ : ℝ) ≤ n / (1 + ε) + (n / (1 + ε)) / (5000 * (log (n / (1 + ε))) ^ 2) :=
            by
              simpa using hq₂_ub_log
        _ = (n / (1 + ε)) * (1 + 1 / (5000 * (log (n / (1 + ε))) ^ 2)) := by
            have hpos : (0 : ℝ) < log (n / (1 + ε)) := hlog_y₂_pos
            field_simp [hpos.ne']
        _ < (n / (1 + ε)) * (1 + 1 / (5000 * (log x) ^ 2)) := by
          apply mul_lt_mul_of_pos_left _ hy₂_pos
          gcongr
        _ = (n / (1 + ε)) * (1 + ε) := by simp [hε_def, ratio_def]
        _ = n := by field_simp
    exact Nat.cast_lt.mp hq₂_strict
  refine ⟨![q₀, q₁, q₂], fun i ↦ by fin_cases i <;> assumption,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
      fin_cases i
      · exact hq₀_lt_q₁
      · exact hq₁_lt_q₂,
    fun i ↦ ?_, hq₂_lt_n⟩
  fin_cases i <;> simp only [hε_def]
  · -- Case i = 0: n * (1 + ε)^(-3) ≤ q₀
    simp only [CharP.cast_eq_zero, sub_zero]
    have heq :
        (n : ℝ) * (1 + prime_gap_pkg.upper x / prime_gap_pkg.lower x) ^ (-(3 : ℝ)) =
          n / (1 + ε) ^ 3 := by
      rw [rpow_neg h1ε_pos.le, div_eq_mul_inv]
      simp [hε_def]
    rw [heq]
    exact hq₀_lb'.le
  · -- Case i = 1: show n * (1 + ε)^(-2) ≤ q₁
    simp only [Nat.cast_one]
    have heq :
        (n : ℝ) * (1 + prime_gap_pkg.upper x / prime_gap_pkg.lower x) ^ (-(3 - 1 : ℝ)) =
          n / (1 + ε) ^ 2 := by
      have h1 : -(3 - 1 : ℝ) = -2 := by ring
      rw [h1, rpow_neg h1ε_pos.le, div_eq_mul_inv]
      simp [hε_def]
    rw [heq]
    exact hq₁_lb'.le
  · -- Case i = 2: show n * (1 + ε)^(-1) ≤ q₂
    simp only [Nat.cast_ofNat]
    have heq :
        (n : ℝ) * (1 + prime_gap_pkg.upper x / prime_gap_pkg.lower x) ^ (-(3 - 2 : ℝ)) =
          n / (1 + ε) := by
      have h1 : -(3 - 2 : ℝ) = -1 := by ring
      rw [h1, rpow_neg h1ε_pos.le, rpow_one, div_eq_mul_inv]
    rw [heq]
    exact hq₂_lb'.le

lemma prod_q_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes hn_sq).choose i) ≤
      ∏ i : Fin 3, (1 + (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / n) := by
  rw [show ∏ i : Fin 3, (1 + (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / n) =
      ∏ i : Fin 3, (1 + (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((3 : ℝ) - (i : ℕ)) / n) by
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    conv =>
      enter [1, 1, 1, 2, 1, 2]
      equals 1 => simp
    conv =>
      enter [1, 1, 2, 2, 1, 2]
      equals 2 => norm_cast
    conv =>
      enter [2, 1, 1, 2, 1, 2]
      equals 3 => norm_cast
    conv =>
      enter [1, 2, 2, 1, 2]
      equals 3 => norm_cast
    conv =>
      enter [2, 2, 2, 1, 2]
      equals 1 => norm_cast
    conv =>
      enter [2, 1, 2, 2, 1, 2]
      equals 2 => norm_cast
    ring]
  apply Finset.prod_le_prod (fun i _ => by
    have hq_pos : 0 < (exists_q_primes hn_sq).choose i := by
      exact (exists_q_primes hn_sq).choose_spec.1 i |>.pos
    have hq_nonneg : (0 : ℝ) ≤ (exists_q_primes hn_sq).choose i := by
      exact_mod_cast hq_pos.le
    have hdiv_nonneg : 0 ≤ (1 : ℝ) / (exists_q_primes hn_sq).choose i := by
      exact one_div_nonneg.mpr hq_nonneg
    linarith)
  intro i _
  suffices h : (1 : ℝ) / (exists_q_primes hn_sq).choose i ≤
      (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((3 : ℝ) - (i : ℕ)) / n from (by linarith)
  have h0 : 0 < 1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) := hε_pos hn_sq
  have hn_pos : 0 < (n : ℝ) := n_pos_of_hn_sq hn_sq
  have hpow_pos :
      0 < (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((3 : ℝ) - (i : ℕ)) := by
    exact Real.rpow_pos_of_pos h0 _
  have hden_pos :
      0 < (n : ℝ) / (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((3 : ℝ) - (i : ℕ)) := by
    exact div_pos hn_pos hpow_pos
  have hq' := (exists_q_primes hn_sq).choose_spec.2.2.1 i
  have hq'' := hq'
  rw [rpow_neg h0.le] at hq''
  have hq :
      (n : ℝ) / (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ ((3 : ℝ) - (i : ℕ)) ≤
        (exists_q_primes hn_sq).choose i := by
    rw [div_eq_mul_inv]
    exact hq''
  have hq' := one_div_le_one_div_of_le hden_pos hq
  have hq'' := hq'
  rw [one_div_div] at hq''
  exact hq''

lemma prod_p_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes hn_sq).choose i * ((exists_p_primes hn_sq).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 / ((1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  refine Finset.prod_le_prod (fun i _ => by
    have hn_pos : 0 < (n : ℝ) := n_pos_of_hn_sq hn_sq
    have hsqrt_nonneg : 0 ≤ √(n : ℝ) := by positivity
    have hden2_pos : 0 < (n : ℝ) + √(n : ℝ) := by linarith
    have h0 : 0 < 1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) := hε_pos hn_sq
    have hpow_pos :
        0 < (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) := by
      exact Real.rpow_pos_of_pos h0 _
    have hden_pos :
        0 < (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
      exact mul_pos hpow_pos hden2_pos
    have hdiv_nonneg :
        0 ≤ (1 : ℝ) /
          ((1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n)) := by
      exact one_div_nonneg.mpr hden_pos.le
    exact add_nonneg (by norm_num) hdiv_nonneg) fun i _ => ?_
  set p := (exists_p_primes hn_sq).choose
  have h₀ (i) : √n < p i := by
    have : p 0 ≤ p i := by
      apply (exists_p_primes hn_sq).choose_spec.2.1.monotone
      simp
    grw [← this]
    exact (exists_p_primes hn_sq).choose_spec.2.2.2
  gcongr 1 + 1 / ?_
  · have := ((exists_p_primes hn_sq).choose_spec.1 i).pos
    positivity
  have : p i ≤ √n * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ (i + 1 : ℝ) := by
    simpa [ratio_def] using (exists_p_primes hn_sq).choose_spec.2.2.1 i
  have h₁ : p i ^ 2 ≤ n * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ (2 * i + 2 : ℝ) := by
    grw [this, mul_pow, sq_sqrt (by simp)]
    norm_cast
    rw [← pow_mul]
    grind
  have hn_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  have h₂ : p i + 1 ≤ p i * (1 / n * (n + √n)) := by
    field_simp [this, hn_pos.ne']
    linear_combination √n * h₀ i - sq_sqrt (cast_nonneg n)
  grw [h₂, ← mul_assoc, ← sq, h₁]
  field_simp
  simp

lemma pq_ratio_ge {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn_sq).choose i : ℝ))
    / ∏ i, ((exists_q_primes hn_sq).choose i : ℝ) ≥
    1 - 4 * (1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ))) ^ 12 / n ^ (3 / 2 : ℝ) := by
  have hn_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  have l1 : ((1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ 12 / n ^ (3 / 2 : ℝ)) =
    (n ^ (3 / 2 : ℝ) * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ 6) /
    (n ^ (3 : ℝ) * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ (- 6 : ℝ)) := by
    rw [rpow_neg (hε_pos hn_sq).le, ← div_eq_mul_inv, div_div_eq_mul_div, mul_assoc,
      mul_comm, ← rpow_natCast, ← rpow_natCast (n := 6), ← rpow_add (hε_pos hn_sq),
      ← div_div_eq_mul_div]
    · congr
      · norm_num
      · rw [← rpow_sub hn_pos]
        norm_num
  have l2 : n ^ (3 / 2 : ℝ) * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ 6 = ∏ i : Fin 3,
    √n * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ ((i : ℝ) + 1) := by
    rw [← Finset.pow_card_mul_prod, Fin.prod_univ_three, ← rpow_add (hε_pos hn_sq),
      ← rpow_add (hε_pos hn_sq), rpow_div_two_eq_sqrt _ hn_pos.le]
    norm_num
  have l3 : n ^ (3 : ℝ) * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ (- 6 : ℝ) =
    ∏ i : Fin 3, n * (1 + prime_gap_pkg.upper (√n) / prime_gap_pkg.lower (√n)) ^ (-((3 : ℝ) - i.1))  := by
    rw [← Finset.pow_card_mul_prod, Fin.prod_univ_three, ← rpow_add (hε_pos hn_sq),
      ← rpow_add (hε_pos hn_sq)]
    norm_num
  rw [← mul_div_assoc', ← mul_div_assoc', l1, l2, l3]
  gcongr
  · have := hε_pos hn_sq
    exact Finset.prod_nonneg fun _ _ => by positivity
  · exact Finset.prod_pos fun _ _ => by positivity [hε_pos hn_sq]
  · exact (exists_p_primes hn_sq).choose_spec.2.2.1 _
  · exact fun _ _ => by positivity [hε_pos hn_sq]
  · exact (exists_q_primes hn_sq).choose_spec.2.2.1 _

-- The bound 1/(5000 * 19.9^2) ≈ 0.0000050377 ≤ 0.0000051
lemma inv_cube_log_sqrt_le_aux {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤ 0.0000051 := by
  have hlog :
      prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤
        prime_gap_pkg.upper (X₀ : ℝ) / prime_gap_pkg.lower (X₀ : ℝ) := by
    have hlog' :
        (1 / (5000 * (log √(n : ℝ)) ^ (2 : ℝ))) ≤ 1 / (5000 * (log (X₀ : ℝ)) ^ (2 : ℝ)) := by
      have hlog_ge : log √(n : ℝ) ≥ log (X₀ : ℝ) :=
        log_le_log X₀_pos (hsqrt_ge hn_sq)
      have hlog_pos : 0 < log (X₀ : ℝ) := log_X₀_pos
      have hpow : (log (X₀ : ℝ)) ^ (2 : ℝ) ≤ (log √(n : ℝ)) ^ (2 : ℝ) :=
        rpow_le_rpow hlog_pos.le hlog_ge (by positivity)
      have hmul : 5000 * (log (X₀ : ℝ)) ^ (2 : ℝ) ≤ 5000 * (log √(n : ℝ)) ^ (2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left hpow
        norm_num
      have hpow_pos : 0 < 5000 * (log (X₀ : ℝ)) ^ (2 : ℝ) := by positivity [hlog_pos]
      exact one_div_le_one_div_of_le hpow_pos hmul
    simpa [ratio_def] using hlog'
  calc
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤
        prime_gap_pkg.upper (X₀ : ℝ) / prime_gap_pkg.lower (X₀ : ℝ) := hlog
    _ ≤ 0.0000051 := by
      have : 1 / (5000 * (log (X₀ : ℝ)) ^ (2 : ℝ)) ≤ 0.0000051 := by
        grw [← log_X₀_gt.le]
        norm_num
      simpa [ratio_def] using this

lemma inv_cube_log_sqrt_le {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) ≤ 0.0000051 := by
  simpa using inv_cube_log_sqrt_le_aux hn_sq

lemma inv_n_pow_3_div_2_le {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / (n : ℝ)) := by
  have hn_sq_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  rw [one_div_mul_one_div, one_div_le_one_div (rpow_pos_of_pos hn_sq_pos _)
    (mul_pos X₀_pos hn_sq_pos), show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      rpow_add hn_sq_pos, rpow_one, mul_comm, ← sqrt_eq_rpow]
  refine mul_le_mul_of_nonneg_left ?_ hn_sq_pos.le
  have := Real.sqrt_le_sqrt (cast_le.mpr hn_sq)
  simp_all

lemma inv_n_add_sqrt_ge_aux {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  have hsqrt_pos : (0 : ℝ) < √(n : ℝ) := by positivity [hn_pos]
  have hX0_le : (X₀ : ℝ) ≤ √(n : ℝ) := hsqrt_ge hn_sq
  have hdiv_le : (1 : ℝ) / √(n : ℝ) ≤ 1 / (X₀ : ℝ) :=
    one_div_le_one_div_of_le X₀_pos hX0_le
  have hden_le : 1 + (1 : ℝ) / √(n : ℝ) ≤ 1 + 1 / (X₀ : ℝ) := by
    linarith [hdiv_le]
  have hden_pos : 0 < 1 + (1 : ℝ) / √(n : ℝ) := by
    have : 0 < (1 : ℝ) / √(n : ℝ) := by positivity [hsqrt_pos]
    linarith
  have hrecip :
      1 / (1 + 1 / (X₀ : ℝ)) ≤ 1 / (1 + (1 : ℝ) / √(n : ℝ)) :=
    one_div_le_one_div_of_le hden_pos hden_le
  have hmul :
      (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) ≤
        (1 / (1 + (1 : ℝ) / √(n : ℝ))) * (1 / (n : ℝ)) := by
    have hn_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity [hn_pos]
    exact mul_le_mul_of_nonneg_right hrecip hn_nonneg
  have hdiv : (n : ℝ) / √(n : ℝ) = √(n : ℝ) := by
    have hsqrt_ne : (√(n : ℝ)) ≠ 0 := by exact ne_of_gt hsqrt_pos
    field_simp [hsqrt_ne]
    simpa [mul_comm] using (mul_self_sqrt (Nat.cast_nonneg n))
  have hmul_eq : (n : ℝ) * (1 + (1 : ℝ) / √(n : ℝ)) = n + √(n : ℝ) := by
    calc
      (n : ℝ) * (1 + (1 : ℝ) / √(n : ℝ)) = n + n / √(n : ℝ) := by
        simp [mul_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = n + √(n : ℝ) := by simp [hdiv]
  have hrewrite :
      (1 / (1 + (1 : ℝ) / √(n : ℝ))) * (1 / (n : ℝ)) =
        1 / (n + √(n : ℝ)) := by
    have hn_ne : (n : ℝ) ≠ 0 := by exact ne_of_gt hn_pos
    have hsqrt_ne : (√(n : ℝ)) ≠ 0 := by exact ne_of_gt hsqrt_pos
    field_simp [hn_ne, hsqrt_ne]
    simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, mul_self_sqrt (Nat.cast_nonneg n)]
  have hmul' :
      (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) ≤ 1 / (n + √(n : ℝ)) := by
    calc
      (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
          ≤ (1 / (1 + (1 : ℝ) / √(n : ℝ))) * (1 / (n : ℝ)) := hmul
      _ = 1 / (n + √(n : ℝ)) := hrewrite
  exact hmul'


theorem inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  simpa using inv_n_add_sqrt_ge_aux hn


lemma prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + (1.0000051 : ℝ) ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith

lemma prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / ((1.0000051 : ℝ) ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * (1.0000051 : ℝ) ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / (468991632 ^ 2 : ℝ) := by
    simpa [X₀_eq] using hε
  simpa [X₀_eq] using (by
    norm_cast; norm_num [Fin.prod_univ_three]
    nlinarith [pow_nonneg hε'.left 3, pow_nonneg hε'.left 4])

lemma final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / (468991632 ^ 2 : ℝ) := by
    simpa [X₀_eq] using hε
  nlinarith [hε']

lemma criterion_mk_hn_sq {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) : n ≥ 1 := by
  have hX0 : 1 ≤ X₀ ^ 2 := by
    simpa [X₀_eq] using (by decide : 1 ≤ (468991632 : ℕ) ^ 2)
  exact le_trans hX0 hn_sq

lemma criterion_mk_h_ord_2 {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    (exists_p_primes hn_sq).choose 2 < (exists_q_primes hn_sq).choose 0 := by
  have hn_sq_pos : (0 : ℝ) < n := n_pos_of_hn_sq hn_sq
  have hp' : ((exists_p_primes hn_sq).choose 2 : ℝ) ≤ √n * (1 + 1 / (5000 * (log √n) ^ 2)) ^ 3 := by
    simpa [show ((2 : ℝ) + 1) = 3 by norm_num] using
      (exists_p_primes hn_sq).choose_spec.2.2.1 2
  have hq' : n * (1 + 1 / (5000 * (log √n) ^ 2)) ^ (-3 : ℝ) ≤ (exists_q_primes hn_sq).choose 0 := by
    convert (exists_q_primes hn_sq).choose_spec.2.2.1 0 using 2
    norm_num
  have hε_pos := hε_pos hn_sq
  have hmid :
      √n * (1 + 1 / (5000 * (log √n) ^ 2)) ^ 3 < n * (1 + 1 / (5000 * (log √n) ^ 2)) ^ (-3 : ℝ) := by
    norm_cast
    norm_num [rpow_neg_one] at *
    rw [← div_eq_mul_inv, lt_div_iff₀ <| pow_pos hε_pos 3]
    have : (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 6 < 2 :=
      calc (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 6 < (1 + (5000 * 19 ^ 2 : ℝ)⁻¹) ^ 6 := by
            gcongr
            linarith [hlog hn_sq]
        _ ≤ 2 := by norm_num
    have h2 : (2 : ℝ) ≤ √n := by
      have : (2 : ℝ) ≤ X₀ := X₀_ge_2
      exact this.trans (hsqrt_ge hn_sq)
    have hA : (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 6 < √n := lt_of_lt_of_le this h2
    have hsqrt_pos : (0 : ℝ) < √n := by positivity
    have hpow :
        (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 3 * (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 3 =
          (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 6 := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using
        (pow_add (1 + (5000 * (log √n) ^ 2)⁻¹) 3 3).symm
    calc
      √n * (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 3 * (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 3
          = √n * (1 + (5000 * (log √n) ^ 2)⁻¹) ^ 6 := by
            simpa [hpow, mul_assoc]
      _ < √n * √n := by
        exact mul_lt_mul_of_pos_left hA hsqrt_pos
      _ = n := by
        simpa [mul_comm] using (mul_self_sqrt (Nat.cast_nonneg n))
  exact_mod_cast hp'.trans_lt <| hmid.trans_le hq'



lemma criterion_mk_h_crit_h₁ {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    1 - (4 : ℝ) * (∏ i, (exists_p_primes hn_sq).choose i : ℝ) /
      ∏ i, ((exists_q_primes hn_sq).choose i : ℝ) ≥
      1 - 4 * (1 + 0.0000051) ^ 12 * ((1 / X₀) * (1 / n)) := by
  have hε_nonneg : 0 ≤ 1 + prime_gap_pkg.upper (√(n : ℝ)) / prime_gap_pkg.lower (√(n : ℝ)) := (hε_pos hn_sq).le
  grw [pq_ratio_ge hn_sq, inv_cube_log_sqrt_le hn_sq, ← inv_n_pow_3_div_2_le hn_sq] <;>
    simp [field, hε_nonneg]

lemma criterion_mk_h_crit_h₁_nonneg {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + 0.0000051 : ℝ) ^ 12 * ((1 / X₀) * (1 / n)) := by
  have hn_sq' : n ≥ (468991632 : ℕ) ^ 2 := by
    simpa [X₀_eq] using hn_sq
  simpa [X₀_eq] using (by
    grw [hn_sq']
    norm_num)

lemma criterion_mk_h_crit_hn_sq' {n : ℕ} (hn_sq : n ≥ X₀ ^ 2) :
    (0 : ℝ) ≤ 1 / ↑n ∧ (1 : ℝ) / ↑n ≤ 1 / X₀ ^ 2 := by
  have hn_sq' : (X₀ : ℝ) ^ 2 ≤ n := by exact_mod_cast hn_sq
  have hpos : 0 < (X₀ : ℝ) ^ 2 := by positivity [X₀_pos]
  refine ⟨by simp, ?_⟩
  exact one_div_le_one_div_of_le hpos hn_sq'




noncomputable def Dusart_gatekeeper (n : ℕ) (hn_sq : n ≥ X₀ ^ 2) : Gatekeeper where
  n := n
  hn := criterion_mk_hn_sq hn_sq
  p := (exists_p_primes hn_sq).choose
  hp := (exists_p_primes hn_sq).choose_spec.1
  hp_mono := (exists_p_primes hn_sq).choose_spec.2.1
  q := (exists_q_primes hn_sq).choose
  hq := (exists_q_primes hn_sq).choose_spec.1
  hq_mono := (exists_q_primes hn_sq).choose_spec.2.1
  h_ord_1 := (exists_p_primes hn_sq).choose_spec.2.2.2
  h_ord_2 := criterion_mk_h_ord_2 hn_sq
  h_ord_3 := (exists_q_primes hn_sq).choose_spec.2.2.2
  hsqrt_ge := hsqrt_ge hn_sq
  log_X₀_gt := log_X₀_gt
  hlog := hlog hn_sq
  ratio_def := ratio_def
  hε_pos := hε_pos hn_sq
  log_X₀_pos := log_X₀_pos
  exists_p_primes_hsqrt_ge := exists_p_primes_hsqrt_ge hn_sq
  exists_p_primes_hx_pos := exists_p_primes_hx_pos hn_sq
  exists_p_primes_hlog_pos := exists_p_primes_hlog_pos hn_sq
  exists_p_primes_hx1_ge := @exists_p_primes_hx1_ge _ hn_sq
  exists_p_primes_hx2_ge := @exists_p_primes_hx2_ge _ hn_sq
  exists_q_primes_hε_small := exists_q_primes_hε_small hn_sq
  exists_q_primes_hx_ge_2 := exists_q_primes_hx_ge_2 hn_sq
  exists_q_primes_hy₀_ge := exists_q_primes_hy₀_ge hn_sq
  exists_q_primes_hy₁_hy₂ := @exists_q_primes_hy₁_hy₂ _
  exists_q_primes_hy_bounds := @exists_q_primes_hy_bounds _ hn_sq
  exists_p_primes := exists_p_primes hn_sq
  exists_q_primes := exists_q_primes hn_sq
  p_eq := rfl
  q_eq := rfl
  prod_q_ge := prod_q_ge hn_sq
  prod_p_ge := prod_p_ge hn_sq
  pq_ratio_ge := pq_ratio_ge hn_sq
  inv_cube_log_sqrt_le_aux := inv_cube_log_sqrt_le_aux hn_sq
  inv_cube_log_sqrt_le := inv_cube_log_sqrt_le hn_sq
  inv_n_pow_3_div_2_le := inv_n_pow_3_div_2_le hn_sq
  inv_n_add_sqrt_ge_aux := inv_n_add_sqrt_ge_aux hn_sq
  inv_n_add_sqrt_ge := inv_n_add_sqrt_ge hn_sq
  prod_epsilon_le := @prod_epsilon_le
  prod_epsilon_ge := @prod_epsilon_ge
  final_comparison := @final_comparison
  criterion_mk_hn_sq := criterion_mk_hn_sq hn_sq
  criterion_mk_h_ord_2 := criterion_mk_h_ord_2 hn_sq
  criterion_mk_h_crit_h₁ := criterion_mk_h_crit_h₁ hn_sq
  criterion_mk_h_crit_h₁_nonneg := criterion_mk_h_crit_h₁_nonneg hn_sq
  criterion_mk_h_crit_hn_sq' := criterion_mk_h_crit_hn_sq' hn_sq



end Lcm_gk
