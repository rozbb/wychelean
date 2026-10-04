import Wychelean.KEM.MLKEM.Properties.Stages
import Mathlib.Tactic.Ring

/-! The FIPS loops of Algorithms 9–11 compute the stage folds of `Properties/Stages.lean`. -/

namespace Wychelean.KEM.MLKEM

namespace NTT

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

end NTT

/-- A fold over the members of `l` with their membership proofs. -/
theorem foldl_attach_eq {α β : Type*} [DecidableEq α] (l : List α) (f : β → {a // a ∈ l} → β)
    (init : β) :
    l.attach.foldl f init = l.foldl (fun b a => if h : a ∈ l then f b ⟨a, h⟩ else b) init := by
  rw [← List.foldl_attach (f := fun b a => if h : a ∈ l then f b ⟨a, h⟩ else b)]
  congr 1
  funext b x
  split
  · rfl
  · exact absurd x.2 ‹_›

theorem foldl_range'_eq {β : Type*} (s n step : ℕ) (g : β → ℕ → β) (init : β) :
    (List.range' s n step).foldl g init = Fin.foldl n (fun b i => g b (s + step * i)) init := by
  induction n generalizing s init with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, Fin.foldl_succ, ih]
    congr 1
    · funext b i
      congr 1
      simp only [Fin.val_succ]
      ring

/-- A fold over the members of `range' s n step`, with their membership proofs, is a fold over
`Fin n'` for any `n' = n`. -/
theorem foldl_attach_range' {β : Type*} (s n step n' : ℕ) (hn : n = n')
    (f : β → {a // a ∈ List.range' s n step} → β) (init : β) :
    (List.range' s n step).attach.foldl f init =
      Fin.foldl n' (fun b i => f b ⟨s + step * i, List.mem_range'.2 ⟨i, hn ▸ i.isLt, rfl⟩⟩) init := by
  subst hn
  rw [foldl_attach_eq, foldl_range'_eq]
  congr 1
  funext b i
  split
  · rfl
  · exact absurd (List.mem_range'.2 ⟨i, i.isLt, rfl⟩) ‹_›

/-- Writing `c i` to the pair `(2i, 2i + 1)` for every `i`. -/
theorem foldl_set_pairs (c : Fin 128 → Zq × Zq) (init : Vector Zq 256) (i : Fin 128) :
    let v := Fin.foldl 128 (fun v (i : Fin 128) =>
      (v.set (2 * i.val) (c i).1 (by omega)).set (2 * i.val + 1) (c i).2 (by omega)) init
    v[2 * i.val] = (c i).1 ∧ v[2 * i.val + 1] = (c i).2 := by
  intro v
  let F (v : Vector Zq 256) (i : Fin 128) : Vector Zq 256 :=
    (v.set (2 * i.val) (c i).1 (by omega)).set (2 * i.val + 1) (c i).2 (by omega)
  let P (t : ℕ) (v : Vector Zq 256) : Prop := ∀ i : Fin 128, i.val < t →
    v[2 * i.val] = (c i).1 ∧ v[2 * i.val + 1] = (c i).2
  have step (t : Fin 128) (v : Vector Zq 256) (hv : P t.val v) : P (t.val + 1) (F v t) := by
    intro i hi
    by_cases hit : i = t
    · subst hit
      simp [F]
    · have hlt : i.val < t.val := by
        have : i.val ≠ t.val := fun h => hit (Fin.ext h)
        omega
      obtain ⟨h0, h1⟩ := hv i hlt
      refine ⟨?_, ?_⟩
      · simp only [F]
        rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_ne _ _ (by omega), h0]
      · simp only [F]
        rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_ne _ _ (by omega), h1]
  exact NTT.foldl_invariant F P init (fun _ h => absurd h (Nat.not_lt_zero _)) step i i.isLt

/-- Algorithm 11 computes the 128 base-case products. -/
theorem mul_eq_multiply (a b : Tq) : a * b = NTT.multiply a b := by
  change MultiplyNTTs a b = _
  unfold MultiplyNTTs
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl, pure_bind,
    Id.run_pure]
  rw [foldl_attach_range' (n' := 128)]
  swap; · rfl
  simp only [zero_add, one_mul]
  have h := foldl_set_pairs (fun i => BaseCaseMultiply a[2 * i.val] a[2 * i.val + 1] b[2 * i.val]
    b[2 * i.val + 1] (ζ ^ (2 * bitRev 7 i.val + 1))) (Vector.replicate 256 0)
  apply Tq.ext
  intro k hk
  rw [Tq.getElem_mk]
  have hm : (NTT.multiply a b)[k] = ((Vector.ofFn fun i : Fin 128 => NTT.baseCaseMultiply
      a[2 * i.val] a[2 * i.val + 1] b[2 * i.val] b[2 * i.val + 1]
      (ζ ^ (2 * bitRev 7 i.val + 1))).flatten)[k] := rfl
  rw [hm, Vector.getElem_flatten, Vector.getElem_ofFn]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨h0, _⟩ := h ⟨j, by omega⟩
    rw [h0]
    simp [BaseCaseMultiply, NTT.baseCaseMultiply]
  · obtain ⟨_, h1⟩ := h ⟨j, by omega⟩
    rw [h1]
    have e1 : (2 * j + 1) / 2 = j := by omega
    have e2 : (2 * j + 1) % 2 = 1 := by omega
    simp [e1, e2, BaseCaseMultiply, NTT.baseCaseMultiply]

theorem len_mem (s : Fin 7) : NTT.len s ∈ [128, 64, 32, 16, 8, 4, 2] := by
  fin_cases s <;> decide

theorem stage_size (s : Fin 7) (h : 0 < 2 * NTT.len s) :
    ({ start := 0, stop := 256, step := 2 * NTT.len s, step_pos := h } : Std.Legacy.Range).size =
      NTT.blocks s := by
  fin_cases s <;> simp [Std.Legacy.Range.size, NTT.len, NTT.blocks]

theorem block_size (a l : ℕ) : [a:a + l].size = l := by
  simp [Std.Legacy.Range.size]

/-- Algorithm 9 is the fold of its seven stages. -/
theorem NTT_eq_forward (f : Polynomial) : f.NTT = ⟨NTT.forward f.coeffs⟩ := by
  unfold Polynomial.NTT NTT.forward
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', bind_pure_comp, Prod.mk.eta,
    List.forIn'_pure_yield_eq_foldl, Id.run_pure, map_pure]
  refine congrArg (fun p : Vector Zq 256 × ℕ => Tq.mk p.1) ?_
  rw [foldl_attach_eq]
  conv_lhs => arg 3; rw [show [128, 64, 32, 16, 8, 4, 2] = (List.finRange 7).map NTT.len by rfl]
  rw [List.foldl_map, ← Fin.foldl_eq_finRange_foldl]
  congr 1
  funext st s
  rw [dite_eq_left_of_eq_true (eq_true (len_mem s))]
  dsimp only
  rw [foldl_attach_range' (n' := NTT.blocks s)]
  swap; · exact stage_size s _
  unfold NTT.forwardStage
  refine congrArg (fun F => Fin.foldl (NTT.blocks s) F st) ?_
  funext b i
  unfold NTT.forwardBlock
  dsimp only
  rw [foldl_attach_range' (n' := NTT.len s)]
  swap; · exact block_size _ _
  refine Prod.ext ?_ rfl
  dsimp only
  refine congrArg (fun F => Fin.foldl (NTT.len s) F b.1) ?_
  funext a j
  simp only [zero_add, one_mul]
  have := NTT.index_lt s i j
  rw [Vector.getElem_set_ne _ _ (by have := NTT.len_pos s; omega)]

theorem len_mem_rev (s : Fin 7) : NTT.len ⟨6 - s.val, by omega⟩ ∈ [2, 4, 8, 16, 32, 64, 128] := by
  fin_cases s <;> decide

/-- Algorithm 10 is the fold of its seven stages, followed by the scaling. -/
theorem NTTInv_eq_inverse (a : Tq) : a.NTTInv = ⟨NTT.inverse a.coeffs⟩ := by
  unfold Tq.NTTInv NTT.inverse
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', bind_pure_comp, Prod.mk.eta,
    List.forIn'_pure_yield_eq_foldl, Id.run_pure, map_pure]
  refine congrArg Polynomial.mk ?_
  have e (v : Vector Zq 256) : (3303 : Zq) • v = v.map (· * 3303) := by
    ext i hi
    rw [Vector.getElem_smul, Vector.getElem_map, smul_eq_mul, mul_comm]
  rw [e]
  refine congrArg (fun p : Vector Zq 256 × ℕ => p.1.map (· * 3303)) ?_
  rw [foldl_attach_eq]
  conv_lhs =>
    arg 3
    rw [show [2, 4, 8, 16, 32, 64, 128] =
      (List.finRange 7).map (fun s : Fin 7 => NTT.len ⟨6 - s.val, by omega⟩) by rfl]
  rw [List.foldl_map, ← Fin.foldl_eq_finRange_foldl]
  refine congrArg (fun F => Fin.foldl 7 F _) ?_
  funext st s
  rw [dite_eq_left_of_eq_true (eq_true (len_mem_rev s))]
  dsimp only
  rw [foldl_attach_range' (n' := NTT.blocks ⟨6 - s.val, by omega⟩)]
  swap; · exact stage_size _ _
  unfold NTT.inverseStage
  refine congrArg (fun F => Fin.foldl _ F st) ?_
  funext b i
  unfold NTT.inverseBlock
  dsimp only
  rw [foldl_attach_range' (n' := NTT.len ⟨6 - s.val, by omega⟩)]
  swap; · exact block_size _ _
  refine Prod.ext ?_ rfl
  dsimp only
  refine congrArg (fun F => Fin.foldl _ F b.1) ?_
  funext a j
  simp only [zero_add, one_mul]
  have := NTT.index_lt _ i j
  rw [Vector.getElem_set_ne _ _ (by have := NTT.len_pos ⟨6 - s.val, by omega⟩; omega)]

end Wychelean.KEM.MLKEM
