import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.ZMod.Basic

/-!
# Primality of 2^255 - 19

A Pratt certificate for the Curve25519 base field prime, checked entirely by the kernel.

`Nat.Prime` is not decidable in practice at this size (trial division would need ~2^127 steps),
so each prime is established with `lucas_primality`: exhibit a witness `a` of multiplicative
order `P - 1`, which requires the full factorisation of `P - 1` and a primality proof for each
of its factors. That recursion bottoms out at primes small enough for `norm_num`.

The one obstacle is that `ZMod`'s `Monoid.npow` is `npowRecAuto`, i.e. *unary* recursion, so
`decide` cannot evaluate `a ^ (P - 1)` — it exhausts the recursion depth well before 2^255.
`pow_eq_binRec` rewrites to Mathlib's repeated-squaring `npowBinRec`, which the kernel reduces
in ~256 steps of GMP-accelerated `Fin` arithmetic.
-/

set_option maxRecDepth 4000

/-- Restate `a ^ n` via repeated squaring, so the kernel can evaluate it. -/
theorem pow_eq_binRec {M : Type*} [Monoid M] (n : ℕ) (a : M) : a ^ n = npowBinRec n a := by
  induction n with
  | zero => rw [pow_zero, npowBinRec_zero]
  | succ k ih => rw [pow_succ, ih, npowBinRec_succ]

/-- A prime dividing a prime power is that prime; used to turn `q ∣ P - 1` into a case split. -/
private theorem eq_of_dvd_pow {q r e: ℕ} (hq: q.Prime) (hr: r.Prime) (h: q ∣ r ^ e): q = r :=
  (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h)

private theorem prime_2773320623: Nat.Prime 2773320623 := by
  refine lucas_primality 2773320623 5 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 2437 ∨ q = 569003 := by
    rw [show 2773320623 - 1 = 2 ^ 1 * (2437 ^ 1 * (569003 ^ 1)) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · exact Or.inr (Or.inr (eq_of_dvd_pow hq (by norm_num) hdvd))
  rcases hc with rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_72106336199: Nat.Prime 72106336199 := by
  refine lucas_primality 72106336199 7 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 13 ∨ q = 2773320623 := by
    rw [show 72106336199 - 1 = 2 ^ 1 * (13 ^ 1 * (2773320623 ^ 1)) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · exact Or.inr (Or.inr (eq_of_dvd_pow hq prime_2773320623 hdvd))
  rcases hc with rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_1919519569386763: Nat.Prime 1919519569386763 := by
  refine lucas_primality 1919519569386763 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 19 ∨ q = 47 ∨ q = 127 ∨ q = 8574133 := by
    rw [show 1919519569386763 - 1 = 2 ^ 1 * (3 ^ 1 * (7 ^ 1 * (19 ^ 1 * (47 ^ 2 * (127 ^ 1 * (8574133 ^ 1)))))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))
          · rcases hq.dvd_mul.mp hdvd with h | hdvd
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))))
            · rcases hq.dvd_mul.mp hdvd with h | hdvd
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq (by norm_num) hdvd))))))
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_31757755568855353: Nat.Prime 31757755568855353 := by
  refine lucas_primality 31757755568855353 10 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 31 ∨ q = 107 ∨ q = 223 ∨ q = 4153 ∨ q = 430751 := by
    rw [show 31757755568855353 - 1 = 2 ^ 3 * (3 ^ 1 * (31 ^ 1 * (107 ^ 1 * (223 ^ 1 * (4153 ^ 1 * (430751 ^ 1)))))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))
          · rcases hq.dvd_mul.mp hdvd with h | hdvd
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))))
            · rcases hq.dvd_mul.mp hdvd with h | hdvd
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq (by norm_num) hdvd))))))
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_75445702479781427272750846543864801: Nat.Prime 75445702479781427272750846543864801 := by
  refine lucas_primality 75445702479781427272750846543864801 7 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 75707 ∨ q = 72106336199 ∨ q = 1919519569386763 := by
    rw [show 75445702479781427272750846543864801 - 1 = 2 ^ 5 * (3 ^ 2 * (5 ^ 2 * (75707 ^ 1 * (72106336199 ^ 1 * (1919519569386763 ^ 1))))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))
          · rcases hq.dvd_mul.mp hdvd with h | hdvd
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq prime_72106336199 h)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_1919519569386763 hdvd)))))
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907: Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 := by
  refine lucas_primality 74058212732561358302231226437062788676166966415465897661863160754340907 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 353 ∨ q = 57467 ∨ q = 132049 ∨ q = 1923133 ∨ q = 31757755568855353 ∨ q = 75445702479781427272750846543864801 := by
    rw [show 74058212732561358302231226437062788676166966415465897661863160754340907 - 1 = 2 ^ 1 * (3 ^ 1 * (353 ^ 1 * (57467 ^ 1 * (132049 ^ 1 * (1923133 ^ 1 * (31757755568855353 ^ 1 * (75445702479781427272750846543864801 ^ 1))))))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))
          · rcases hq.dvd_mul.mp hdvd with h | hdvd
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))))
            · rcases hq.dvd_mul.mp hdvd with h | hdvd
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))))
              · rcases hq.dvd_mul.mp hdvd with h | hdvd
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq prime_31757755568855353 h)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_75445702479781427272750846543864801 hdvd)))))))
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949: Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  refine lucas_primality 57896044618658097711785492504343953926634992332820282019728792003956564819949 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 65147 ∨ q = 74058212732561358302231226437062788676166966415465897661863160754340907 := by
    rw [show 57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1 = 2 ^ 2 * (3 ^ 1 * (65147 ^ 1 * (74058212732561358302231226437062788676166966415465897661863160754340907 ^ 1))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_74058212732561358302231226437062788676166966415465897661863160754340907 hdvd)))
  rcases hc with rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide
theorem prime_two_pow_255_sub_19: Nat.Prime (2 ^ 255 - 19) := by
  have h: (2 : ℕ) ^ 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
    norm_num
  rw [h]
  exact prime_57896044618658097711785492504343953926634992332820282019728792003956564819949

instance fact_prime_two_pow_255_sub_19: Fact (Nat.Prime (2 ^ 255 - 19)) :=
  ⟨prime_two_pow_255_sub_19⟩
