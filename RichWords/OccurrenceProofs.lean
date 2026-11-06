import RichWords.OccurrenceDefinitions
import RichWords.PrefixProofs

namespace RichWords

theorem prefixes_append_singleton {α : Type} (w : List α) (a : α) :
    prefixes (w ++ [a]) = prefixes w ++ [w ++ [a]] := by
  induction w with
  | nil => simp [prefixes]
  | cons b w ih => simp [prefixes, ih, List.map_append]

theorem nodup_same_members_length {α : Type} [DecidableEq α]
    (xs ys : List α) (hx : xs.Nodup) (hy : ys.Nodup)
    (he : ∀ z, z ∈ xs ↔ z ∈ ys) : xs.length = ys.length := by
  have h1 := nodup_subset_length_le xs ys hx (fun z hz => (he z).mp hz)
  have h2 := nodup_subset_length_le ys xs hy (fun z hz => (he z).mpr hz)
  omega

/-- The new palindrome contains every palindromic suffix of this prefix. -/
theorem new_palindrome_suffix_test {α : Type} [DecidableEq α]
    (p q w : List α) (a : α) (hp : Palindrome p)
    (hq : q ∈ palindromicFactors (w ++ [a])) (hn : q ∉ palindromicFactors w) :
    p.IsSuffix (w ++ [a]) ↔ p.IsSuffix q := by
  have hqs := new_palindrome_is_suffix q w a hq hn
  have hqp := ((mem_palindromicFactors_iff q _).mp hq).2
  constructor
  · intro hps
    rcases List.suffix_or_suffix_of_suffix hps hqs with hs | hs
    · exact hs
    · have hpre : q.IsPrefix p := by
        have h := List.reverse_prefix.mpr hs
        simpa only [show p.reverse = p from hp, show q.reverse = q from hqp] using h
      rcases List.suffix_concat_iff.mp hps with he | ⟨t, he, ht⟩
      · subst p
        simp
      · rw [he] at hpre
        rcases List.prefix_concat_iff.mp hpre with hqp_eq | hqt
        · rw [← hqp_eq] at he
          rw [he]
          exact ⟨[], rfl⟩
        · exact False.elim (hn ((mem_palindromicFactors_iff q w).mpr
            ⟨hqt.isInfix.trans ht.isInfix, hqp⟩))
  · intro hs
    exact hs.trans hqs

theorem new_palindrome_membership {α : Type} [DecidableEq α]
    (p q w : List α) (a : α)
    (hq : q ∈ palindromicFactors (w ++ [a])) (hn : q ∉ palindromicFactors w) :
    p ∈ palindromicFactors (w ++ [a]) ↔ p = q ∨ p ∈ palindromicFactors w := by
  constructor
  · intro hp
    by_cases hold : p ∈ palindromicFactors w
    · exact Or.inr hold
    · exact Or.inl (new_palindrome_unique p q w a hp hold hq hn)
  · intro hp
    rcases hp with he | hold
    · simpa [he] using hq
    · exact palindrome_membership_append p w [a] hold

theorem new_palindrome_filter_count {α : Type} [DecidableEq α]
    (q w : List α) (a : α) (f : List α → Bool)
    (hq : q ∈ palindromicFactors (w ++ [a])) (hn : q ∉ palindromicFactors w) :
    ((palindromicFactors (w ++ [a])).filter f).length =
      ((palindromicFactors w).filter f).length + (if f q then 1 else 0) := by
  have he := nodup_same_members_length
    ((palindromicFactors (w ++ [a])).filter f) ((q :: palindromicFactors w).filter f)
    (List.filter_sublist.nodup (palindromicFactors_nodup _))
    (List.filter_sublist.nodup (List.nodup_cons.mpr ⟨hn, palindromicFactors_nodup _⟩))
    (by
      intro p
      simp only [List.mem_filter, List.mem_cons, new_palindrome_membership p q w a hq hn])
  rw [he]
  cases hf : f q <;> simp [hf]

theorem suffix_occurrence_append {α : Type} [DecidableEq α]
    (p w : List α) (a : α) :
    suffixOccurrenceCount p (w ++ [a]) = suffixOccurrenceCount p w +
      (if p.IsSuffix (w ++ [a]) then 1 else 0) := by
  by_cases hs : p.IsSuffix (w ++ [a]) <;>
    simp [suffixOccurrenceCount, prefixes_append_singleton, List.filter_append, hs]

/-- Richness turns first-occurrence suffixes into an exact occurrence census. -/
theorem full_count_palindrome_occurrences {α : Type} [DecidableEq α]
    (p w : List α) (hp : Palindrome p)
    (hw : (palindromicFactors w).length = w.length + 1) :
    suffixOccurrenceCount p w = palindromeSuffixCount p w := by
  have main (v : List α)
      (hv : (palindromicFactors v.reverse).length = v.reverse.length + 1) :
      suffixOccurrenceCount p v.reverse = palindromeSuffixCount p v.reverse := by
    induction v with
    | nil =>
      simp [suffixOccurrenceCount, palindromeSuffixCount, prefixes,
        palindromicFactors, factorOccurrences, Palindrome, List.eraseDups_cons]
    | cons a v ih =>
      simp only [List.reverse_cons] at hv ⊢
      have hprefix := full_palindrome_count_prefix v.reverse [a] hv
      have hind := ih hprefix
      obtain ⟨q, hq, hn⟩ := full_count_extension_has_new_palindrome v.reverse a hv
      have hfilter := new_palindrome_filter_count q v.reverse a
        (fun z => decide (p.IsSuffix z)) hq hn
      change palindromeSuffixCount p (v.reverse ++ [a]) =
        palindromeSuffixCount p v.reverse + (if decide (p.IsSuffix q) then 1 else 0) at hfilter
      rw [suffix_occurrence_append, hind, hfilter]
      simp [new_palindrome_suffix_test p q v.reverse a hp hq hn]
  simpa using main w.reverse (by simpa using hw)

theorem same_palindrome_set_occurrences {α : Type} [DecidableEq α]
    (p u v : List α) (hp : Palindrome p)
    (hu : (palindromicFactors u).length = u.length + 1)
    (hv : (palindromicFactors v).length = v.length + 1)
    (hs : ∀ q, q ∈ palindromicFactors u ↔ q ∈ palindromicFactors v) :
    suffixOccurrenceCount p u = suffixOccurrenceCount p v := by
  rw [full_count_palindrome_occurrences p u hp hu, full_count_palindrome_occurrences p v hp hv]
  apply nodup_same_members_length
  · exact List.filter_sublist.nodup (palindromicFactors_nodup _)
  · exact List.filter_sublist.nodup (palindromicFactors_nodup _)
  · intro q
    simp only [List.mem_filter, hs q]

theorem full_count_maximal_palindrome_unique {α : Type} [DecidableEq α]
    (p w : List α) (hp : p ∈ palindromicFactors w)
    (hw : (palindromicFactors w).length = w.length + 1)
    (hmax : ∀ q, q ∈ palindromicFactors w → Factor p q → q = p) :
    suffixOccurrenceCount p w = 1 := by
  rw [full_count_palindrome_occurrences p w ((mem_palindromicFactors_iff p w).mp hp).2 hw]
  have he := nodup_same_members_length
    ((palindromicFactors w).filter (fun q => decide (p.IsSuffix q))) [p]
    (List.filter_sublist.nodup (palindromicFactors_nodup _)) (by simp)
    (by
      intro q
      constructor
      · intro hq
        obtain ⟨hq, hs⟩ := List.mem_filter.mp hq
        have hs' : p.IsSuffix q := of_decide_eq_true hs
        simp [hmax q hq hs'.isInfix]
      · intro hq
        have he : q = p := by simpa using hq
        subst q
        simp [hp])
  simpa [palindromeSuffixCount] using he

end RichWords

#print axioms RichWords.prefixes_append_singleton
#print axioms RichWords.nodup_same_members_length
#print axioms RichWords.new_palindrome_suffix_test
#print axioms RichWords.new_palindrome_membership
#print axioms RichWords.new_palindrome_filter_count
#print axioms RichWords.suffix_occurrence_append
#print axioms RichWords.full_count_palindrome_occurrences
#print axioms RichWords.same_palindrome_set_occurrences
#print axioms RichWords.full_count_maximal_palindrome_unique
