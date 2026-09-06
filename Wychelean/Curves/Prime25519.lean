import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.ZMod.Basic

/-!
# Primality of 2^255 - 19 and of the Curve25519 basepoint order

Pratt certificates for the Curve25519 base field prime and for the order of its basepoint,
both checked entirely by the kernel.

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

/-! ## The basepoint order, 2^252 + 0x14def9dea2f79cd65812631a5cf5d3ed -/

private theorem prime_14741173: Nat.Prime 14741173 := by
  refine lucas_primality 14741173 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 409477 := by
    rw [show 14741173 - 1 = 2 ^ 2 * (3 ^ 2 * (409477 ^ 1)) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · exact Or.inr (Or.inr (eq_of_dvd_pow hq (by norm_num) hdvd))
  rcases hc with rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_58964693: Nat.Prime 58964693 := by
  refine lucas_primality 58964693 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 14741173 := by
    rw [show 58964693 - 1 = 2 ^ 2 * (14741173 ^ 1) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · exact Or.inr (eq_of_dvd_pow hq prime_14741173 hdvd)
  rcases hc with rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_292386187: Nat.Prime 292386187 := by
  refine lucas_primality 292386187 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 307 ∨ q = 5879 := by
    rw [show 292386187 - 1 = 2 ^ 1 * (3 ^ 4 * (307 ^ 1 * (5879 ^ 1))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq (by norm_num) hdvd)))
  rcases hc with rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_213441916511: Nat.Prime 213441916511 := by
  refine lucas_primality 213441916511 13 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 5 ∨ q = 73 ∨ q = 292386187 := by
    rw [show 213441916511 - 1 = 2 ^ 1 * (5 ^ 1 * (73 ^ 1 * (292386187 ^ 1))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_292386187 hdvd)))
  rcases hc with rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_1257559732178653: Nat.Prime 1257559732178653 := by
  refine lucas_primality 1257559732178653 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 23 ∨ q = 531581 ∨ q = 1224481 := by
    rw [show 1257559732178653 - 1 = 2 ^ 2 * (3 ^ 1 * (7 ^ 1 * (23 ^ 1 * (531581 ^ 1 * (1224481 ^ 1))))) from by norm_num] at hdvd
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
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq (by norm_num) hdvd)))))
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_4434155615661930479: Nat.Prime 4434155615661930479 := by
  refine lucas_primality 4434155615661930479 17 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 41 ∨ q = 43 ∨ q = 1257559732178653 := by
    rw [show 4434155615661930479 - 1 = 2 ^ 1 * (41 ^ 1 * (43 ^ 1 * (1257559732178653 ^ 1))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_1257559732178653 hdvd)))
  rcases hc with rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_3044861653679985063343: Nat.Prime 3044861653679985063343 := by
  refine lucas_primality 3044861653679985063343 5 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 30703 ∨ q = 82163 ∨ q = 132667 ∨ q = 137849 := by
    rw [show 3044861653679985063343 - 1 = 2 ^ 1 * (3 ^ 1 * (11 ^ 1 * (30703 ^ 1 * (82163 ^ 1 * (132667 ^ 1 * (137849 ^ 1)))))) from by norm_num] at hdvd
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

private theorem prime_172054593956031949258510691: Nat.Prime 172054593956031949258510691 := by
  refine lucas_primality 172054593956031949258510691 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 5 ∨ q = 1361 ∨ q = 2851 ∨ q = 4434155615661930479 := by
    rw [show 172054593956031949258510691 - 1 = 2 ^ 1 * (5 ^ 1 * (1361 ^ 1 * (2851 ^ 1 * (4434155615661930479 ^ 1)))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_4434155615661930479 hdvd))))
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_198211423230930754013084525763697: Nat.Prime 198211423230930754013084525763697 := by
  refine lucas_primality 198211423230930754013084525763697 5 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 23 ∨ q = 58964693 ∨ q = 3044861653679985063343 := by
    rw [show 198211423230930754013084525763697 - 1 = 2 ^ 4 * (3 ^ 1 * (23 ^ 1 * (58964693 ^ 1 * (3044861653679985063343 ^ 1)))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq prime_58964693 h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_3044861653679985063343 hdvd))))
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_19757330305831588566944191468367130476339: Nat.Prime 19757330305831588566944191468367130476339 := by
  refine lucas_primality 19757330305831588566944191468367130476339 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 269 ∨ q = 213441916511 ∨ q = 172054593956031949258510691 := by
    rw [show 19757330305831588566944191468367130476339 - 1 = 2 ^ 1 * (269 ^ 1 * (213441916511 ^ 1 * (172054593956031949258510691 ^ 1))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq prime_213441916511 h)))
        · exact Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_172054593956031949258510691 hdvd)))
  rcases hc with rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_276602624281642239937218680557139826668747: Nat.Prime 276602624281642239937218680557139826668747 := by
  refine lucas_primality 276602624281642239937218680557139826668747 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 7 ∨ q = 19757330305831588566944191468367130476339 := by
    rw [show 276602624281642239937218680557139826668747 - 1 = 2 ^ 1 * (7 ^ 1 * (19757330305831588566944191468367130476339 ^ 1)) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · exact Or.inr (Or.inr (eq_of_dvd_pow hq prime_19757330305831588566944191468367130476339 hdvd))
  rcases hc with rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

private theorem prime_7237005577332262213973186563042994240857116359379907606001950938285454250989: Nat.Prime 7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
  refine lucas_primality 7237005577332262213973186563042994240857116359379907606001950938285454250989 2 (by rw [pow_eq_binRec]; decide) ?_
  intro q hq hdvd
  have hc: q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 198211423230930754013084525763697 ∨ q = 276602624281642239937218680557139826668747 := by
    rw [show 7237005577332262213973186563042994240857116359379907606001950938285454250989 - 1 = 2 ^ 2 * (3 ^ 1 * (11 ^ 1 * (198211423230930754013084525763697 ^ 1 * (276602624281642239937218680557139826668747 ^ 1)))) from by norm_num] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | hdvd
    · exact Or.inl (eq_of_dvd_pow hq (by norm_num) h)
    · rcases hq.dvd_mul.mp hdvd with h | hdvd
      · exact Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h))
      · rcases hq.dvd_mul.mp hdvd with h | hdvd
        · exact Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq (by norm_num) h)))
        · rcases hq.dvd_mul.mp hdvd with h | hdvd
          · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_dvd_pow hq prime_198211423230930754013084525763697 h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (eq_of_dvd_pow hq prime_276602624281642239937218680557139826668747 hdvd))))
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> rw [pow_eq_binRec] <;> decide

theorem prime_basepointOrder: Nat.Prime (2 ^ 252 + 0x14def9dea2f79cd65812631a5cf5d3ed) := by
  have h: 2 ^ 252 + 0x14def9dea2f79cd65812631a5cf5d3ed =
      7237005577332262213973186563042994240857116359379907606001950938285454250989 := by
    norm_num
  rw [h]
  exact prime_7237005577332262213973186563042994240857116359379907606001950938285454250989
