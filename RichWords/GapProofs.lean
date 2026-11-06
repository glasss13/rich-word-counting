import RichWords.Proofs

namespace RichWords

theorem expandGaps_length (a : Bool) (ks : List Nat) :
    (expandGaps a ks).length = ks.length + ks.sum + 1 := by
  induction ks with
  | nil => simp [expandGaps]
  | cons k ks ih => simp [expandGaps, ih]; omega

theorem expandGaps_starts (a : Bool) (ks : List Nat) :
    ∃ tail, expandGaps a ks = a :: tail := by
  cases ks with
  | nil => exact ⟨[], rfl⟩
  | cons k ks => exact ⟨_, rfl⟩

theorem gap_prefix_unique (a : Bool) (m n : Nat) (u v : Word)
    (h : List.replicate m (!a) ++ a :: u = List.replicate n (!a) ++ a :: v) :
    m = n ∧ u = v := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simpa using h
    | succ n =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ,
        List.cons_append, List.cons.injEq] at h
      cases a <;> simp_all
  | succ m ih =>
    cases n with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.replicate_succ,
        List.cons_append, List.cons.injEq] at h
      cases a <;> simp_all
    | succ n =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq,
        true_and] at h
      obtain ⟨hm, hv⟩ := ih n h
      exact ⟨by omega, hv⟩

theorem expandGaps_injective (a : Bool) (xs ys : List Nat)
    (h : expandGaps a xs = expandGaps a ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    have hl := congrArg List.length h
    simp only [expandGaps_length, List.length_nil, List.sum_nil] at hl
    have hy : ys.length = 0 := by omega
    simpa using (List.length_eq_zero_iff.mp hy).symm
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hl := congrArg List.length h
      simp only [expandGaps_length, List.length_cons, List.length_nil,
        List.sum_nil, List.sum_cons] at hl
      omega
    | cons y ys =>
      obtain ⟨u, hu⟩ := expandGaps_starts a xs
      obtain ⟨v, hv⟩ := expandGaps_starts a ys
      simp only [expandGaps, List.cons.injEq, true_and] at h
      rw [hu, hv] at h
      obtain ⟨hxy, huv⟩ := gap_prefix_unique a x y u v h
      have ht : expandGaps a xs = expandGaps a ys := by rw [hu, hv, huv]
      simp [hxy, ih ys ht]

theorem expandGaps_append_singleton (a : Bool) (xs : List Nat) (k : Nat) :
    expandGaps a (xs ++ [k]) = expandGaps a xs ++ List.replicate k (!a) ++ [a] := by
  induction xs with
  | nil => simp [expandGaps]
  | cons x xs ih => simp [expandGaps, ih, List.append_assoc]

theorem expandGaps_reverse (a : Bool) (xs : List Nat) :
    (expandGaps a xs).reverse = expandGaps a xs.reverse := by
  induction xs with
  | nil => simp [expandGaps]
  | cons x xs ih =>
    simp [expandGaps, List.reverse_cons, List.reverse_append,
      ih, expandGaps_append_singleton, List.append_assoc]

theorem expandGaps_palindrome_iff (a : Bool) (xs : List Nat) :
    Palindrome (expandGaps a xs) ↔ xs.reverse = xs := by
  simp only [Palindrome, expandGaps_reverse]
  constructor
  · exact expandGaps_injective a _ _
  · intro h; rw [h]

theorem gap_prefix_iff (a : Bool) (m n : Nat) (u v : Word) :
    (List.replicate m (!a) ++ a :: u).IsPrefix
      (List.replicate n (!a) ++ a :: v) ↔ m = n ∧ u.IsPrefix v := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simp
    | succ n => cases a <;> simp [List.replicate_succ]
  | succ m ih =>
    cases n with
    | zero => cases a <;> simp [List.replicate_succ]
    | succ n => simpa [List.replicate_succ] using ih n

theorem gap_runs_prefix_iff (a : Bool) (m n : Nat) (xs ys : List Nat) :
    (List.replicate m (!a) ++ expandGaps a xs).IsPrefix
      (List.replicate n (!a) ++ expandGaps a ys) ↔
        m = n ∧ (expandGaps a xs).IsPrefix (expandGaps a ys) := by
  obtain ⟨u, hu⟩ := expandGaps_starts a xs
  obtain ⟨v, hv⟩ := expandGaps_starts a ys
  rw [hu, hv, gap_prefix_iff]
  simp

theorem expandGaps_prefix_iff (a : Bool) (xs ys : List Nat) :
    (expandGaps a xs).IsPrefix (expandGaps a ys) ↔ xs.IsPrefix ys := by
  induction xs generalizing ys with
  | nil =>
    obtain ⟨u, hu⟩ := expandGaps_starts a ys
    simp [expandGaps, hu]
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h
        have hl := h.length_le
        simp [expandGaps_length] at hl
      · simp
    | cons y ys =>
      simp only [expandGaps, List.cons_prefix_cons, true_and]
      rw [gap_runs_prefix_iff, ih]

theorem expandGaps_skip_opposite (a : Bool) (xs : List Nat) (m : Nat) (w : Word) :
    (expandGaps a xs).IsInfix (List.replicate m (!a) ++ w) ↔
      (expandGaps a xs).IsInfix w := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨u, hu⟩ := expandGaps_starts a xs
    simp only [List.replicate_succ, List.cons_append, List.infix_cons_iff]
    have hp : ¬ (expandGaps a xs).IsPrefix
        ((!a) :: (List.replicate m (!a) ++ w)) := by
      rw [hu, List.cons_prefix_cons]
      cases a <;> simp
    simp only [hp, false_or, ih]

theorem expandGaps_infix_iff (a : Bool) (xs ys : List Nat) :
    (expandGaps a xs).IsInfix (expandGaps a ys) ↔ xs.IsInfix ys := by
  induction ys with
  | nil =>
    constructor
    · intro h
      have hl := h.length_le
      simp only [expandGaps_length, List.length_nil, List.sum_nil] at hl
      have hx : xs.length = 0 := by omega
      simp [List.length_eq_zero_iff.mp hx]
    · intro h
      have hx : xs = [] := by simpa using h
      simp [hx]
  | cons y ys ih =>
    change (expandGaps a xs).IsInfix
      (a :: (List.replicate y (!a) ++ expandGaps a ys)) ↔ _
    rw [List.infix_cons_iff]
    have hp := expandGaps_prefix_iff a xs (y :: ys)
    change (expandGaps a xs).IsPrefix
      (a :: (List.replicate y (!a) ++ expandGaps a ys)) ↔ _ at hp
    rw [hp, expandGaps_skip_opposite, ih, List.infix_cons_iff]

theorem expandGaps_skip_opposite_right (a : Bool) (xs : List Nat) (m : Nat) (w : Word) :
    (expandGaps a xs).IsInfix (w ++ List.replicate m (!a)) ↔
      (expandGaps a xs).IsInfix w := by
  rw [← List.reverse_infix]
  simp only [List.reverse_append, List.reverse_replicate, expandGaps_reverse]
  rw [expandGaps_skip_opposite]
  rw [← expandGaps_reverse, List.reverse_infix]

theorem expandGaps_padded_infix_iff (a : Bool) (xs ys : List Nat) (i j : Nat) :
    (expandGaps a xs).IsInfix
      (List.replicate i (!a) ++ expandGaps a ys ++ List.replicate j (!a)) ↔
      xs.IsInfix ys := by
  rw [List.append_assoc, expandGaps_skip_opposite,
    expandGaps_skip_opposite_right, expandGaps_infix_iff]

theorem binary_gap_normal_form (a : Bool) (w : Word) :
    (∃ k, w = List.replicate k (!a)) ∨
    ∃ i xs j, w = List.replicate i (!a) ++ expandGaps a xs ++ List.replicate j (!a) := by
  induction w with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons b w ih =>
    by_cases h : b = a
    · subst b
      rcases ih with ⟨k, hk⟩ | ⟨i, xs, j, hw⟩
      · exact Or.inr ⟨0, [], k, by simp [expandGaps, hk]⟩
      · exact Or.inr ⟨0, i :: xs, j, by simp [expandGaps, hw, List.append_assoc]⟩
    · have hb : b = !a := by cases a <;> cases b <;> simp_all
      subst b
      rcases ih with ⟨k, hk⟩ | ⟨i, xs, j, hw⟩
      · exact Or.inl ⟨k+1, by simp [List.replicate_succ, hk]⟩
      · exact Or.inr ⟨i+1, xs, j, by simp [List.replicate_succ, hw]⟩

theorem opposite_prefix_zero (a : Bool) (i : Nat) (u v : Word)
    (h : a :: u = List.replicate i (!a) ++ v) : i = 0 := by
  cases i with
  | zero => rfl
  | succ i => cases a <;> simp [List.replicate_succ] at h

theorem palindrome_gap_expansion (a : Bool) (u : Word)
    (hp : Palindrome (a :: u)) : ∃ xs, a :: u = expandGaps a xs := by
  rcases binary_gap_normal_form a (a :: u) with ⟨k, hk⟩ | ⟨i, xs, j, h⟩
  · have hz : k = 0 := opposite_prefix_zero a k u [] (by simpa using hk)
    simp [hz] at hk
  · have hi : i = 0 := opposite_prefix_zero a i u
        (expandGaps a xs ++ List.replicate j (!a)) (by simpa [List.append_assoc] using h)
    simp only [hi, List.replicate_zero, List.nil_append] at h
    have hr := congrArg List.reverse h
    rw [show (a :: u).reverse = a :: u from hp] at hr
    simp only [List.reverse_append, List.reverse_replicate] at hr
    have hj : j = 0 := opposite_prefix_zero a j u (expandGaps a xs).reverse hr
    exact ⟨xs, by simpa [hj] using h⟩

theorem gapsAfter_skip (a : Bool) (m k : Nat) (w : Word) :
    gapsAfter a k (List.replicate m (!a) ++ w) = gapsAfter a (k+m) w := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    have hn : (!a) ≠ a := by cases a <;> decide
    simp only [List.replicate_succ, List.cons_append, gapsAfter, hn, ↓reduceIte]
    rw [ih]
    congr 1
    omega

theorem letterGaps_skip (a : Bool) (m : Nat) (w : Word) :
    letterGaps a (List.replicate m (!a) ++ w) = letterGaps a w := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hn : (!a) ≠ a := by cases a <;> decide
    simp [List.replicate_succ, letterGaps, hn, ih]

theorem gapsAfter_replicate (a : Bool) (m k : Nat) :
    gapsAfter a k (List.replicate m (!a)) = [] := by
  have h := gapsAfter_skip a m k []
  simpa [gapsAfter] using h

theorem letterGaps_replicate (a : Bool) (m : Nat) :
    letterGaps a (List.replicate m (!a)) = [] := by
  have h := letterGaps_skip a m []
  simpa [letterGaps] using h

theorem gapsAfter_expansion (a : Bool) (xs : List Nat) (j k : Nat) :
    gapsAfter a k (expandGaps a xs ++ List.replicate j (!a)) = k :: xs := by
  induction xs generalizing k with
  | nil => simp [expandGaps, gapsAfter, gapsAfter_replicate]
  | cons x xs ih =>
    simp [expandGaps, gapsAfter, List.append_assoc, gapsAfter_skip, ih]

theorem letterGaps_expansion (a : Bool) (xs : List Nat) (j : Nat) :
    letterGaps a (expandGaps a xs ++ List.replicate j (!a)) = xs := by
  cases xs with
  | nil => simp [expandGaps, letterGaps, gapsAfter_replicate]
  | cons x xs =>
    simp [expandGaps, letterGaps, List.append_assoc, gapsAfter_skip, gapsAfter_expansion]

theorem letterGaps_padded (a : Bool) (xs : List Nat) (i j : Nat) :
    letterGaps a (List.replicate i (!a) ++ expandGaps a xs ++ List.replicate j (!a)) = xs := by
  rw [List.append_assoc, letterGaps_skip, letterGaps_expansion]

theorem gap_normal_form_of_mem (a : Bool) (w : Word) (ha : a ∈ w) :
    ∃ i j, w = List.replicate i (!a) ++ expandGaps a (letterGaps a w) ++
      List.replicate j (!a) := by
  rcases binary_gap_normal_form a w with ⟨k, hk⟩ | ⟨i, xs, j, h⟩
  · rw [hk] at ha
    cases a <;> simp at ha
  · refine ⟨i, j, ?_⟩
    have hg : letterGaps a w = xs := by rw [h, letterGaps_padded]
    simpa [hg] using h

theorem letterGaps_of_not_mem (a : Bool) (w : Word) (ha : a ∉ w) :
    letterGaps a w = [] := by
  rcases binary_gap_normal_form a w with ⟨k, hk⟩ | ⟨i, xs, j, h⟩
  · rw [hk, letterGaps_replicate]
  · obtain ⟨u, hu⟩ := expandGaps_starts a xs
    simp [h, hu] at ha

theorem expandGaps_count (a : Bool) (xs : List Nat) :
    (expandGaps a xs).count a = xs.length + 1 := by
  induction xs with
  | nil => simp [expandGaps]
  | cons x xs ih =>
    simp [expandGaps, List.count_append, List.count_replicate, ih]

theorem letterGaps_length (a : Bool) (w : Word) :
    (letterGaps a w).length + (if a ∈ w then 1 else 0) = w.count a := by
  by_cases ha : a ∈ w
  · obtain ⟨i, j, h⟩ := gap_normal_form_of_mem a w ha
    rw [if_pos ha]
    have hc := congrArg (fun v : Word => v.count a) h
    simp [List.count_append, List.count_replicate, expandGaps_count] at hc
    omega
  · simp [ha, letterGaps_of_not_mem a w ha, List.count_eq_zero.mpr ha]

theorem mem_gapPalImage_iff (a : Bool) (w p : Word) :
    p ∈ gapPalImage a w ↔ ∃ u, p = a :: u ∧ p ∈ palindromicFactors w := by
  constructor
  · intro hp
    have ha : a ∈ w := by
      by_cases ha : a ∈ w
      · exact ha
      · simp [gapPalImage, ha] at hp
    simp only [gapPalImage, if_pos ha, List.mem_map] at hp
    obtain ⟨xs, hxs, rfl⟩ := hp
    obtain ⟨u, hu⟩ := expandGaps_starts a xs
    refine ⟨u, hu, (mem_palindromicFactors_iff _ _).mpr ?_⟩
    obtain ⟨hf, hpal⟩ := (mem_palindromicFactors_iff _ _).mp hxs
    obtain ⟨i, j, hw⟩ := gap_normal_form_of_mem a w ha
    constructor
    · change (expandGaps a xs).IsInfix w
      rw [hw, expandGaps_padded_infix_iff]
      exact hf
    · exact (expandGaps_palindrome_iff a xs).mpr hpal
  · rintro ⟨u, rfl, hp⟩
    obtain ⟨hf, hpal⟩ := (mem_palindromicFactors_iff _ _).mp hp
    have ha : a ∈ w := hf.sublist.subset (by simp)
    obtain ⟨xs, hx⟩ := palindrome_gap_expansion a u hpal
    obtain ⟨i, j, hw⟩ := gap_normal_form_of_mem a w ha
    simp only [gapPalImage, if_pos ha, List.mem_map]
    refine ⟨xs, (mem_palindromicFactors_iff _ _).mpr ?_, hx.symm⟩
    constructor
    · change xs.IsInfix (letterGaps a w)
      apply (expandGaps_padded_infix_iff a xs (letterGaps a w) i j).mp
      simpa [← hw, ← hx] using hf
    · exact (expandGaps_palindrome_iff a xs).mp (by simpa [← hx] using hpal)

theorem expandGaps_eq_iff (a : Bool) (xs ys : List Nat) :
    expandGaps a xs = expandGaps a ys ↔ xs = ys := by
  constructor
  · exact expandGaps_injective a xs ys
  · intro h; rw [h]

theorem gapPalImage_nodup (a : Bool) (w : Word) : (gapPalImage a w).Nodup := by
  by_cases ha : a ∈ w
  · simp only [gapPalImage, if_pos ha]
    simpa only [List.Nodup, List.pairwise_map, ne_eq, expandGaps_eq_iff] using
      palindromicFactors_nodup (letterGaps a w)
  · simp [gapPalImage, ha]

theorem gapPalCover_nodup (w : Word) : (gapPalCover w).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · simp [mem_gapPalImage_iff]
  · apply List.nodup_append.mpr
    refine ⟨gapPalImage_nodup false w, gapPalImage_nodup true w, ?_⟩
    intro p hp q hq
    obtain ⟨u, hu, _⟩ := (mem_gapPalImage_iff false w p).mp hp
    obtain ⟨v, hv, _⟩ := (mem_gapPalImage_iff true w q).mp hq
    simp [hu, hv]

theorem mem_gapPalCover_iff (w p : Word) :
    p ∈ gapPalCover w ↔ p ∈ palindromicFactors w := by
  cases p with
  | nil => simp [gapPalCover, mem_palindromicFactors_iff, Factor, Palindrome]
  | cons a u =>
    cases a <;> simp [gapPalCover, mem_gapPalImage_iff]

theorem gapPalCover_length (w : Word) :
    (palindromicFactors w).length = (gapPalCover w).length := by
  have h1 := nodup_subset_length_le (palindromicFactors w) (gapPalCover w)
    (palindromicFactors_nodup w) (fun p hp => (mem_gapPalCover_iff w p).mpr hp)
  have h2 := nodup_subset_length_le (gapPalCover w) (palindromicFactors w)
    (gapPalCover_nodup w) (fun p hp => (mem_gapPalCover_iff w p).mp hp)
  omega

theorem gap_palindrome_count (w : Word) :
    (palindromicFactors w).length = 1 +
      (if false ∈ w then (palindromicFactors (letterGaps false w)).length else 0) +
      (if true ∈ w then (palindromicFactors (letterGaps true w)).length else 0) := by
  rw [gapPalCover_length]
  by_cases h0 : false ∈ w <;> by_cases h1 : true ∈ w <;>
    simp [gapPalCover, gapPalImage, h0, h1] <;> omega

theorem binary_letter_counts (w : Word) : w.count false + w.count true = w.length := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp <;> omega

theorem binary_gap_defect_identity (w : Word) :
    palindromeDefect w = palindromeDefect (letterGaps false w) +
      palindromeDefect (letterGaps true w) := by
  have hp := gap_palindrome_count w
  have h0 := letterGaps_length false w
  have h1 := letterGaps_length true w
  have hc := binary_letter_counts w
  have hb0 := palindromic_factor_count_bound (letterGaps false w)
  have hb1 := palindromic_factor_count_bound (letterGaps true w)
  have hempty : (palindromicFactors ([] : List Nat)).length = 1 := by
    simp [palindromicFactors, factorOccurrences, Palindrome, List.eraseDups_cons]
  dsimp [palindromeDefect]
  by_cases ha0 : false ∈ w <;> by_cases ha1 : true ∈ w <;>
    simp only [ha0, ha1, ↓reduceIte] at hp h0 h1
  · omega
  · have he1 := letterGaps_of_not_mem true w ha1
    simp only [he1, List.length_nil, hempty] at *
    omega
  · have he0 := letterGaps_of_not_mem false w ha0
    simp only [he0, List.length_nil, hempty] at *
    omega
  · have he0 := letterGaps_of_not_mem false w ha0
    have he1 := letterGaps_of_not_mem true w ha1
    simp only [he0, he1, List.length_nil, hempty] at *
    omega

theorem binary_rich_iff_gap_counts (w : Word) :
    Rich w ↔
      (palindromicFactors (letterGaps false w)).length = (letterGaps false w).length + 1 ∧
      (palindromicFactors (letterGaps true w)).length = (letterGaps true w).length + 1 := by
  have h := binary_gap_defect_identity w
  have hb := palindromic_factor_count_bound w
  have h0 := palindromic_factor_count_bound (letterGaps false w)
  have h1 := palindromic_factor_count_bound (letterGaps true w)
  dsimp [Rich, palindromeDefect] at *
  omega

end RichWords

#print axioms RichWords.expandGaps_length
#print axioms RichWords.expandGaps_starts
#print axioms RichWords.gap_prefix_unique
#print axioms RichWords.expandGaps_injective
#print axioms RichWords.expandGaps_append_singleton
#print axioms RichWords.expandGaps_reverse
#print axioms RichWords.expandGaps_palindrome_iff
#print axioms RichWords.gap_prefix_iff
#print axioms RichWords.gap_runs_prefix_iff
#print axioms RichWords.expandGaps_prefix_iff
#print axioms RichWords.expandGaps_skip_opposite
#print axioms RichWords.expandGaps_infix_iff
#print axioms RichWords.expandGaps_skip_opposite_right
#print axioms RichWords.expandGaps_padded_infix_iff
#print axioms RichWords.binary_gap_normal_form
#print axioms RichWords.opposite_prefix_zero
#print axioms RichWords.palindrome_gap_expansion
#print axioms RichWords.gapsAfter_skip
#print axioms RichWords.letterGaps_skip
#print axioms RichWords.gapsAfter_replicate
#print axioms RichWords.letterGaps_replicate
#print axioms RichWords.gapsAfter_expansion
#print axioms RichWords.letterGaps_expansion
#print axioms RichWords.letterGaps_padded
#print axioms RichWords.gap_normal_form_of_mem
#print axioms RichWords.letterGaps_of_not_mem
#print axioms RichWords.expandGaps_count
#print axioms RichWords.letterGaps_length
#print axioms RichWords.mem_gapPalImage_iff
#print axioms RichWords.expandGaps_eq_iff
#print axioms RichWords.gapPalImage_nodup
#print axioms RichWords.gapPalCover_nodup
#print axioms RichWords.mem_gapPalCover_iff
#print axioms RichWords.gapPalCover_length
#print axioms RichWords.gap_palindrome_count
#print axioms RichWords.binary_letter_counts
#print axioms RichWords.binary_gap_defect_identity
#print axioms RichWords.binary_rich_iff_gap_counts
