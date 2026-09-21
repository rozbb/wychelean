import Wychelean.KEM.MLKEM.NTTRepresentation

namespace Wychelean.KEM.MLKEM.NTT

/-- A bounded traversal invariant, indexed by the number of completed iterations. -/
theorem foldl_invariant {α : Type*} {n : ℕ} (f : α → Fin n → α)
    (P : ℕ → α → Prop) (a : α) (h0 : P 0 a)
    (step : ∀ (i : Fin n) (a : α), P i.val a → P (i.val + 1) (f a i)) :
    P n (Fin.foldl n f a) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    apply step (Fin.last n)
    exact ih (fun a i => f a i.castSucc) (fun i a h => step i.castSucc a h)

/-- Completed butterfly pairs have their final values; unvisited pairs and other entries retain
those of the input. This lemma proves a loop property without adding an executable transform. -/
theorem foldl_pairs {n : ℕ} (lo hi : Fin n → Fin 256)
    (hlo : Function.Injective lo) (hhi : Function.Injective hi)
    (hcross : ∀ i j, lo i ≠ hi j) (op : Zq → Zq → Zq × Zq) (v : Vector Zq 256) :
    let out := Fin.foldl n (fun a i =>
      let pair := op a[(lo i).val] a[(hi i).val]
      (a.set (hi i).val pair.2).set (lo i).val pair.1) v
    (∀ j, out[(lo j).val] = (op v[(lo j).val] v[(hi j).val]).1) ∧
    (∀ j, out[(hi j).val] = (op v[(lo j).val] v[(hi j).val]).2) ∧
    (∀ k : Fin 256, (∀ j, lo j ≠ k ∧ hi j ≠ k) → out[k.val] = v[k.val]) := by
  let P (t : ℕ) (a : Vector Zq 256) : Prop :=
    (∀ j, a[(lo j).val] = if j.val < t then (op v[(lo j).val] v[(hi j).val]).1 else v[(lo j).val]) ∧
    (∀ j, a[(hi j).val] = if j.val < t then (op v[(lo j).val] v[(hi j).val]).2 else v[(hi j).val]) ∧
    (∀ k : Fin 256, (∀ j, lo j ≠ k ∧ hi j ≠ k) → a[k.val] = v[k.val])
  have h := foldl_invariant (n := n) (P := P) (a := v)
    (fun (a : Vector Zq 256) (i : Fin n) => let pair : Zq × Zq := op a[(lo i).val] a[(hi i).val]
      (a.set (hi i).val pair.2).set (lo i).val pair.1)
    (by simp [P]) (by
      intro i a h
      rcases h with ⟨hl, hh, ho⟩
      have hil := hl i
      have hih := hh i
      simp only [lt_self_iff_false, ite_false] at hil hih
      have cross (i j : Fin n) : (lo i).val ≠ (hi j).val :=
        fun h => hcross i j (Fin.ext h)
      refine ⟨?_, ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j
          simp [hil, hih]
        · have hne : (lo i).val ≠ (lo j).val := fun h => hji (hlo (Fin.ext h)).symm
          have hlt : (j.val < i.val + 1) = (j.val < i.val) := by
            have : j.val ≠ i.val := fun h => hji (Fin.ext h)
            apply propext; omega
          simpa only [Vector.getElem_set, hne, ite_false, Ne.symm (cross j i), hlt] using hl j
      · intro j
        by_cases hji : j = i
        · subst j
          simp [cross, hil, hih]
        · have hne : (hi i).val ≠ (hi j).val := fun h => hji (hhi (Fin.ext h)).symm
          have hlt : (j.val < i.val + 1) = (j.val < i.val) := by
            have : j.val ≠ i.val := fun h => hji (Fin.ext h)
            apply propext; omega
          simpa only [Vector.getElem_set, cross, hne, ite_false, hlt] using hh j
      · intro k hk
        have hkl : (lo i).val ≠ k.val := fun h => (hk i).1 (Fin.ext h)
        have hkh : (hi i).val ≠ k.val := fun h => (hk i).2 (Fin.ext h)
        simpa only [Vector.getElem_set, hkl, hkh, ite_false] using ho k hk)
  simpa only [P, Fin.isLt, ite_true] using h

abbrev low (s : Fin 7) (b : Fin (blocks s)) (j : Fin (len s)) : Fin 256 :=
  ⟨2 * len s * b.val + j.val, by have := index_lt s b j; omega⟩

abbrev high (s : Fin 7) (b : Fin (blocks s)) (j : Fin (len s)) : Fin 256 :=
  ⟨2 * len s * b.val + j.val + len s, index_lt s b j⟩

theorem low_injective (s : Fin 7) (b : Fin (blocks s)) : Function.Injective (low s b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [low] at this
  omega

theorem high_injective (s : Fin 7) (b : Fin (blocks s)) : Function.Injective (high s b) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [high] at this
  omega

theorem low_ne_high (s : Fin 7) (b : Fin (blocks s)) (i j : Fin (len s)) :
    low s b i ≠ high s b j := by
  intro h
  have := congrArg Fin.val h
  dsimp [low, high] at this
  omega

/-- The inner traversal computes each forward butterfly and leaves other blocks alone. -/
theorem forwardBlock_pairs (s : Fin 7) (v : Vector Zq 256) (c : ℕ) (b : Fin (blocks s)) :
    let out := (forwardBlock s (v, c) b).1
    let z : Zq := 17 ^ bitRev 7 c
    (∀ j, out[(low s b j).val] = v[(low s b j).val] + z * v[(high s b j).val]) ∧
    (∀ j, out[(high s b j).val] = v[(low s b j).val] - z * v[(high s b j).val]) ∧
    (∀ k : Fin 256, (∀ j, low s b j ≠ k ∧ high s b j ≠ k) → out[k.val] = v[k.val]) :=
  foldl_pairs (low s b) (high s b) (low_injective s b) (high_injective s b)
    (low_ne_high s b) (fun x y => (x + 17 ^ bitRev 7 c * y, x - 17 ^ bitRev 7 c * y)) v

@[simp] theorem low_div (s : Fin 7) (b : Fin (blocks s)) (j : Fin (len s)) :
    (low s b j).val / (2 * len s) = b.val := by
  have hp : 0 < 2 * len s := by have := len_pos s; omega
  have hj : j.val < 2 * len s := by omega
  simp only [Nat.mul_add_div hp, Nat.div_eq_of_lt hj, Nat.add_zero]

@[simp] theorem high_div (s : Fin 7) (b : Fin (blocks s)) (j : Fin (len s)) :
    (high s b j).val / (2 * len s) = b.val := by
  have hp : 0 < 2 * len s := by have := len_pos s; omega
  have hj : j.val + len s < 2 * len s := by omega
  simp only [Nat.add_assoc, Nat.mul_add_div hp, Nat.div_eq_of_lt hj, Nat.add_zero]

theorem different_blocks (s : Fin 7) (b b' : Fin (blocks s)) (h : b ≠ b')
    (i j : Fin (len s)) :
    (low s b i ≠ low s b' j ∧ high s b i ≠ low s b' j) ∧
    (low s b i ≠ high s b' j ∧ high s b i ≠ high s b' j) := by
  have hl := low_div s b i
  have hh := high_div s b i
  have hl' := low_div s b' j
  have hh' := high_div s b' j
  have hn : b.val ≠ b'.val := fun he => h (Fin.ext he)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro he
  all_goals have he' := congrArg (fun k : Fin 256 => k.val / (2 * len s)) he
  all_goals apply hn; omega

theorem forwardBlock_low (s : Fin 7) (v : Vector Zq 256) (c : ℕ)
    (b b' : Fin (blocks s)) (j : Fin (len s)) :
    (forwardBlock s (v, c) b).1[(low s b' j).val] =
      if b' = b then v[(low s b' j).val] + 17 ^ bitRev 7 c * v[(high s b' j).val]
      else v[(low s b' j).val] := by
  split
  · rename_i h; subst b'; exact (forwardBlock_pairs s v c b).1 j
  · rename_i h
    exact (forwardBlock_pairs s v c b).2.2 (low s b' j)
      (fun i => (different_blocks s b b' (Ne.symm h) i j).1)

theorem forwardBlock_high (s : Fin 7) (v : Vector Zq 256) (c : ℕ)
    (b b' : Fin (blocks s)) (j : Fin (len s)) :
    (forwardBlock s (v, c) b).1[(high s b' j).val] =
      if b' = b then v[(low s b' j).val] - 17 ^ bitRev 7 c * v[(high s b' j).val]
      else v[(high s b' j).val] := by
  split
  · rename_i h; subst b'; exact (forwardBlock_pairs s v c b).2.1 j
  · rename_i h
    exact (forwardBlock_pairs s v c b).2.2 (high s b' j)
      (fun i => (different_blocks s b b' (Ne.symm h) i j).2)

/-- After `t` blocks the counter is `c+t` and precisely those blocks are transformed. -/
theorem forwardStage_pairs (s : Fin 7) (v : Vector Zq 256) (c : ℕ) :
    let out := forwardStage (v, c) s
    out.2 = c + blocks s ∧
    (∀ b j, out.1[(low s b j).val] =
      v[(low s b j).val] + 17 ^ bitRev 7 (c + b.val) * v[(high s b j).val]) ∧
    (∀ b j, out.1[(high s b j).val] =
      v[(low s b j).val] - 17 ^ bitRev 7 (c + b.val) * v[(high s b j).val]) := by
  let P (t : ℕ) (a : Vector Zq 256 × ℕ) : Prop := a.2 = c + t ∧
    (∀ b j, a.1[(low s b j).val] = if b.val < t then
      v[(low s b j).val] + 17 ^ bitRev 7 (c + b.val) * v[(high s b j).val]
      else v[(low s b j).val]) ∧
    (∀ b j, a.1[(high s b j).val] = if b.val < t then
      v[(low s b j).val] - 17 ^ bitRev 7 (c + b.val) * v[(high s b j).val]
      else v[(high s b j).val])
  have h := foldl_invariant (n := blocks s) (forwardBlock s) P (v, c) (by simp [P]) (by
    intro b a h
    rcases h with ⟨hc, hl, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · change a.2 + 1 = c + (b.val + 1)
      omega
    · intro b' j
      rw [show a = (a.1, a.2) from rfl, forwardBlock_low]
      by_cases he : b' = b
      · subst b'
        simp only [ite_true, hl, hh, lt_self_iff_false, ite_false, Nat.lt_succ_self, hc]
      · have hv : b'.val ≠ b.val := fun h => he (Fin.ext h)
        have hlt : (b'.val < b.val + 1) = (b'.val < b.val) := by apply propext; omega
        simpa only [he, ite_false, hlt] using hl b' j
    · intro b' j
      rw [show a = (a.1, a.2) from rfl, forwardBlock_high]
      by_cases he : b' = b
      · subst b'
        simp only [ite_true, hl, hh, lt_self_iff_false, ite_false, Nat.lt_succ_self, hc]
      · have hv : b'.val ≠ b.val := fun h => he (Fin.ext h)
        have hlt : (b'.val < b.val + 1) = (b'.val < b.val) := by apply propext; omega
        simpa only [he, ite_false, hlt] using hh b' j)
  simpa only [P, forwardStage, Fin.isLt, ite_true] using h

/-- The inner traversal computes each inverse butterfly and leaves other blocks alone. -/
theorem inverseBlock_pairs (s : Fin 7) (v : Vector Zq 256) (c : ℕ) (b : Fin (blocks s)) :
    let out := (inverseBlock s (v, c) b).1
    let z : Zq := 17 ^ bitRev 7 c
    (∀ j, out[(low s b j).val] = v[(low s b j).val] + v[(high s b j).val]) ∧
    (∀ j, out[(high s b j).val] = z * (v[(high s b j).val] - v[(low s b j).val])) ∧
    (∀ k : Fin 256, (∀ j, low s b j ≠ k ∧ high s b j ≠ k) → out[k.val] = v[k.val]) := by
  have h := foldl_pairs (high s b) (low s b) (high_injective s b) (low_injective s b)
    (fun i j => Ne.symm (low_ne_high s b j i))
    (fun x y => (17 ^ bitRev 7 c * (x - y), y + x)) v
  exact ⟨h.2.1, h.1, fun k hk => h.2.2 k (fun j => (hk j).symm)⟩

theorem inverseBlock_low (s : Fin 7) (v : Vector Zq 256) (c : ℕ)
    (b b' : Fin (blocks s)) (j : Fin (len s)) :
    (inverseBlock s (v, c) b).1[(low s b' j).val] =
      if b' = b then v[(low s b' j).val] + v[(high s b' j).val]
      else v[(low s b' j).val] := by
  split
  · rename_i h; subst b'; exact (inverseBlock_pairs s v c b).1 j
  · rename_i h
    exact (inverseBlock_pairs s v c b).2.2 (low s b' j)
      (fun i => (different_blocks s b b' (Ne.symm h) i j).1)

theorem inverseBlock_high (s : Fin 7) (v : Vector Zq 256) (c : ℕ)
    (b b' : Fin (blocks s)) (j : Fin (len s)) :
    (inverseBlock s (v, c) b).1[(high s b' j).val] =
      if b' = b then 17 ^ bitRev 7 c * (v[(high s b' j).val] - v[(low s b' j).val])
      else v[(high s b' j).val] := by
  split
  · rename_i h; subst b'; exact (inverseBlock_pairs s v c b).2.1 j
  · rename_i h
    exact (inverseBlock_pairs s v c b).2.2 (high s b' j)
      (fun i => (different_blocks s b b' (Ne.symm h) i j).2)

/-- After `t` blocks the counter is `c-t` and precisely those blocks are transformed. -/
theorem inverseStage_pairs (s : Fin 7) (v : Vector Zq 256) (c : ℕ) :
    let out := inverseStage (v, c) s
    out.2 = c - blocks s ∧
    (∀ b j, out.1[(low s b j).val] =
      v[(low s b j).val] + v[(high s b j).val]) ∧
    (∀ b j, out.1[(high s b j).val] =
      17 ^ bitRev 7 (c - b.val) * (v[(high s b j).val] - v[(low s b j).val])) := by
  let P (t : ℕ) (a : Vector Zq 256 × ℕ) : Prop := a.2 = c - t ∧
    (∀ b j, a.1[(low s b j).val] = if b.val < t then
      v[(low s b j).val] + v[(high s b j).val]
      else v[(low s b j).val]) ∧
    (∀ b j, a.1[(high s b j).val] = if b.val < t then
      17 ^ bitRev 7 (c - b.val) * (v[(high s b j).val] - v[(low s b j).val])
      else v[(high s b j).val])
  have h := foldl_invariant (n := blocks s) (inverseBlock s) P (v, c) (by simp [P]) (by
    intro b a h
    rcases h with ⟨hc, hl, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · change a.2 - 1 = c - (b.val + 1)
      omega
    · intro b' j
      rw [show a = (a.1, a.2) from rfl, inverseBlock_low]
      by_cases he : b' = b
      · subst b'
        simp only [ite_true, hl, hh, lt_self_iff_false, ite_false, Nat.lt_succ_self]
      · have hv : b'.val ≠ b.val := fun h => he (Fin.ext h)
        have hlt : (b'.val < b.val + 1) = (b'.val < b.val) := by apply propext; omega
        simpa only [he, ite_false, hlt] using hl b' j
    · intro b' j
      rw [show a = (a.1, a.2) from rfl, inverseBlock_high]
      by_cases he : b' = b
      · subst b'
        simp only [ite_true, hl, hh, lt_self_iff_false, ite_false, Nat.lt_succ_self, hc]
      · have hv : b'.val ≠ b.val := fun h => he (Fin.ext h)
        have hlt : (b'.val < b.val + 1) = (b'.val < b.val) := by apply propext; omega
        simpa only [he, ite_false, hlt] using hh b' j)
  simpa only [P, inverseStage, Fin.isLt, ite_true] using h

end Wychelean.KEM.MLKEM.NTT
