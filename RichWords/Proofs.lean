import RichWords.Definitions

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem mem_prefixes_iff {α : Type} [DecidableEq α] (p w : List α) : p ∈ prefixes w ↔ p.IsPrefix w := by
  induction w generalizing p with
  | nil => simp [prefixes]
  | cons a w ih =>
    simp only [prefixes, List.mem_cons, List.mem_map, List.prefix_cons_iff]
    constructor
    · intro h
      rcases h with h | ⟨t, ht, hp⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, hp.symm, (ih t).mp ht⟩
    · intro h
      rcases h with h | ⟨t, hp, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, (ih t).mpr ht, hp.symm⟩

theorem mem_factorOccurrences_iff {α : Type} [DecidableEq α] (p w : List α) :
    p ∈ factorOccurrences w ↔ Factor p w := by
  induction w with
  | nil => simp [factorOccurrences, Factor]
  | cons a w ih =>
    simp only [factorOccurrences, List.mem_append, mem_prefixes_iff, ih,
      Factor, List.infix_cons_iff]

theorem mem_palindromicFactors_iff {α : Type} [DecidableEq α] (p w : List α) :
    p ∈ palindromicFactors w ↔ Factor p w ∧ Palindrome p := by
  simp [palindromicFactors, mem_factorOccurrences_iff]

/-- The counting list really has no duplicates. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp
    · exact nodup_eraseDups _
termination_by xs.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == a) xs
  simp only [List.length_cons]
  omega

theorem palindromicFactors_nodup {α : Type} [DecidableEq α] (w : List α) : (palindromicFactors w).Nodup :=
  nodup_eraseDups _

theorem mem_allWords_iff (w : Word) (n : Nat) : w ∈ allWords n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allWords]
  | succ n ih =>
    cases w with
    | nil => simp [allWords]
    | cons b w =>
      cases b <;> simp [allWords, ih]

theorem allWords_nodup (n : Nat) : (allWords n).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    have hn (b : Bool) : ((allWords n).map (b :: ·)).Nodup := by
      simpa only [List.Nodup, List.pairwise_map, ne_eq, List.cons.injEq, true_and] using ih
    apply List.nodup_append.mpr
    refine ⟨hn false, hn true, ?_⟩
    intro a ha b hb
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    simp

theorem palindrome_reverse_iff {α : Type} [DecidableEq α] (w : List α) : Palindrome w.reverse ↔ Palindrome w := by
  simp only [Palindrome, List.reverse_reverse]
  exact eq_comm

theorem empty_rich : Rich [] := by decide
theorem singleton_zero_rich : Rich [false] := by decide
theorem alternating_three_rich : Rich [false, true, false] := by decide

theorem first_nonrich : ¬ Rich [false, false, true, false, true, true, false, false] := by
  decide

theorem counts_zero_through_eight :
    (List.range 9).map richCount = [1, 2, 4, 8, 16, 32, 64, 128, 252] := by
  decide


theorem new_palindrome_is_suffix {α : Type} [DecidableEq α] (p w : List α) (a : α)
    (hp : p ∈ palindromicFactors (w ++ [a]))
    (hn : p ∉ palindromicFactors w) : p.IsSuffix (w ++ [a]) := by
  obtain ⟨hf, hpal⟩ := (mem_palindromicFactors_iff p _).mp hp
  rcases List.infix_concat_iff.mp hf with hs | hf
  · exact hs
  · exact False.elim (hn ((mem_palindromicFactors_iff p w).mpr ⟨hf, hpal⟩))

theorem new_palindrome_eq_of_suffix {α : Type} [DecidableEq α] (p q w : List α) (a : α)
    (hp : p ∈ palindromicFactors (w ++ [a]))
    (hn : p ∉ palindromicFactors w)
    (hq : q ∈ palindromicFactors (w ++ [a]))
    (hqn : q ∉ palindromicFactors w)
    (hs : p.IsSuffix q) : p = q := by
  have hpp := ((mem_palindromicFactors_iff p _).mp hp).2
  have hqp := ((mem_palindromicFactors_iff q _).mp hq).2
  have hpre : p.IsPrefix q := by
    have h := List.reverse_prefix.mpr hs
    simpa only [show p.reverse = p from hpp, show q.reverse = q from hqp] using h
  have hqs := new_palindrome_is_suffix q w a hq hqn
  rcases List.suffix_concat_iff.mp hqs with he | ⟨t, he, ht⟩
  · subst q
    simpa using hpre
  · rw [he] at hpre
    rcases List.prefix_concat_iff.mp hpre with hpq | hpt
    · exact hpq.trans he.symm
    · exact False.elim (hn ((mem_palindromicFactors_iff p w).mpr
        ⟨hpt.isInfix.trans ht.isInfix, hpp⟩))

theorem new_palindrome_unique {α : Type} [DecidableEq α] (p q w : List α) (a : α)
    (hp : p ∈ palindromicFactors (w ++ [a]))
    (hn : p ∉ palindromicFactors w)
    (hq : q ∈ palindromicFactors (w ++ [a]))
    (hqn : q ∉ palindromicFactors w) : p = q := by
  rcases List.suffix_or_suffix_of_suffix
      (new_palindrome_is_suffix p w a hp hn)
      (new_palindrome_is_suffix q w a hq hqn) with hs | hs
  · exact new_palindrome_eq_of_suffix p q w a hp hn hq hqn hs
  · exact (new_palindrome_eq_of_suffix q p w a hq hqn hp hn hs).symm
theorem at_most_one_new_palindromic_factor {α : Type} [DecidableEq α] (w : List α) (a : α) :
    ((palindromicFactors (w ++ [a])).filter
      (fun p => decide (p ∉ palindromicFactors w))).length ≤ 1 := by
  let xs := (palindromicFactors (w ++ [a])).filter
      (fun p => decide (p ∉ palindromicFactors w))
  have hn : xs.Nodup := (List.filter_sublist).nodup (palindromicFactors_nodup _)
  have hu : ∀ p ∈ xs, ∀ q ∈ xs, p = q := by
    intro p hp q hq
    have hp' : p ∈ palindromicFactors (w ++ [a]) ∧ p ∉ palindromicFactors w := by
      simpa [xs] using hp
    have hq' : q ∈ palindromicFactors (w ++ [a]) ∧ q ∉ palindromicFactors w := by
      simpa [xs] using hq
    exact new_palindrome_unique p q w a hp'.1 hp'.2 hq'.1 hq'.2
  change xs.length ≤ 1
  generalize hx : xs = ys at *
  cases ys with
  | nil => simp
  | cons p ys =>
    cases ys with
    | nil => simp
    | cons q zs =>
      have he : p = q := hu p (by simp) q (by simp)
      subst q
      simp at hn


/-- A duplicate-free list included in another list cannot be longer. -/
theorem nodup_subset_length_le {α : Type} [DecidableEq α] (xs ys : List α)
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ ys := hs (by simp)
    have hxs : xs ⊆ ys.erase x := by
      intro y hy
      have hne : y ≠ x := by
        intro he
        subst y
        exact (List.nodup_cons.mp hn).1 hy
      exact (List.mem_erase_of_ne hne).mpr (hs (by simp [hy]))
    have hb := ih (ys.erase x) (List.nodup_cons.mp hn).2 hxs
    have he := List.length_erase_of_mem hx
    have hp : 0 < ys.length := by
      apply List.length_pos_iff.mpr
      intro he
      simp [he] at hx
    simp only [List.length_cons]
    omega

theorem palindromic_factor_extension_bound {α : Type} [DecidableEq α] (w : List α) (a : α) :
    (palindromicFactors (w ++ [a])).length ≤ (palindromicFactors w).length + 1 := by
  let xs := palindromicFactors (w ++ [a])
  let old := xs.filter (fun p => decide (p ∈ palindromicFactors w))
  have hn : old.Nodup := List.filter_sublist.nodup (palindromicFactors_nodup _)
  have hs : old ⊆ palindromicFactors w := by
    intro p hp
    simpa [old] using (List.mem_filter.mp hp).2
  have ho := nodup_subset_length_le old (palindromicFactors w) hn hs
  have hnew := at_most_one_new_palindromic_factor w a
  have hsplit := List.length_eq_countP_add_countP
    (fun p => decide (p ∈ palindromicFactors w)) (l := xs)
  simp only [List.countP_eq_length_filter] at hsplit
  simp only [Bool.not_eq_true, decide_eq_false_iff_not] at hsplit
  change xs.length ≤ (palindromicFactors w).length + 1
  dsimp [old] at ho
  dsimp [xs] at *
  omega

theorem palindromic_factor_count_bound {α : Type} [DecidableEq α] (w : List α) :
    (palindromicFactors w).length ≤ w.length + 1 := by
  have hr (v : List α) : (palindromicFactors v.reverse).length ≤ v.length + 1 := by
    induction v with
    | nil => simp [palindromicFactors, factorOccurrences, Palindrome, List.eraseDups_cons]
    | cons a v ih =>
      have h := palindromic_factor_extension_bound v.reverse a
      simp only [List.reverse_cons, List.length_cons]
      omega
  simpa using hr w.reverse

end RichWords

#print axioms RichWords.mem_prefixes_iff
#print axioms RichWords.mem_factorOccurrences_iff
#print axioms RichWords.mem_palindromicFactors_iff
#print axioms RichWords.palindrome_reverse_iff
#print axioms RichWords.empty_rich
#print axioms RichWords.singleton_zero_rich
#print axioms RichWords.alternating_three_rich
#print axioms RichWords.first_nonrich
#print axioms RichWords.counts_zero_through_eight

#print axioms RichWords.nodup_eraseDups
#print axioms RichWords.palindromicFactors_nodup
#print axioms RichWords.mem_allWords_iff

#print axioms RichWords.allWords_nodup

#print axioms RichWords.new_palindrome_is_suffix

#print axioms RichWords.new_palindrome_eq_of_suffix

#print axioms RichWords.new_palindrome_unique

#print axioms RichWords.at_most_one_new_palindromic_factor

#print axioms RichWords.nodup_subset_length_le
#print axioms RichWords.palindromic_factor_extension_bound
#print axioms RichWords.palindromic_factor_count_bound
