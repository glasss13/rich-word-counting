import RichWords.OccurrenceProofs
import RichWords.GapProofs
import RichWords.DefectCoordinateDefinitions

namespace RichWords

/-- Without richness, the suffix occurrence census becomes an inequality. -/
theorem palindrome_suffix_count_le_occurrences {α : Type} [DecidableEq α]
    (p w : List α) (hp : Palindrome p) :
    palindromeSuffixCount p w ≤ suffixOccurrenceCount p w := by
  have main (v : List α) :
      palindromeSuffixCount p v.reverse ≤ suffixOccurrenceCount p v.reverse := by
    induction v with
    | nil =>
      simp [suffixOccurrenceCount, palindromeSuffixCount, prefixes,
        palindromicFactors, factorOccurrences, Palindrome, List.eraseDups_cons]
    | cons a v ih =>
      simp only [List.reverse_cons]
      by_cases hex : ∃ q, q ∈ palindromicFactors (v.reverse ++ [a]) ∧
          q ∉ palindromicFactors v.reverse
      · obtain ⟨q,hq,hn⟩ := hex
        have hf := new_palindrome_filter_count q v.reverse a
          (fun z => decide (p.IsSuffix z)) hq hn
        change palindromeSuffixCount p (v.reverse ++ [a]) =
          palindromeSuffixCount p v.reverse + (if decide (p.IsSuffix q) then 1 else 0) at hf
        rw [hf, suffix_occurrence_append]
        have hs := new_palindrome_suffix_test p q v.reverse a hp hq hn
        by_cases h : p.IsSuffix q <;> simp_all
      · have he : palindromeSuffixCount p (v.reverse ++ [a]) =
            palindromeSuffixCount p v.reverse := by
          apply nodup_same_members_length
          · exact List.filter_sublist.nodup (palindromicFactors_nodup _)
          · exact List.filter_sublist.nodup (palindromicFactors_nodup _)
          · intro q
            simp only [List.mem_filter]
            constructor
            · intro h
              have hold : q ∈ palindromicFactors v.reverse := by
                by_cases hn : q ∈ palindromicFactors v.reverse
                · exact hn
                · exact False.elim (hex ⟨q,h.1,hn⟩)
              exact ⟨hold,h.2⟩
            · intro h
              exact ⟨palindrome_membership_append q v.reverse [a] h.1,h.2⟩
        rw [he,suffix_occurrence_append]
        split <;> omega
  simpa using main w.reverse

theorem singleton_suffix_occurrence_count {α : Type} [DecidableEq α]
    (a : α) (w : List α) : suffixOccurrenceCount [a] w = w.count a := by
  have main (v : List α) : suffixOccurrenceCount [a] v.reverse = v.reverse.count a := by
    induction v with
    | nil => simp [suffixOccurrenceCount,prefixes]
    | cons b v ih =>
      simp only [List.reverse_cons, suffix_occurrence_append, List.count_append, ih]
      by_cases h : a=b <;> simp_all [eq_comm]
  simpa using main w.reverse

theorem singleton_palindrome_count_le_count {α : Type} [DecidableEq α]
    (a : α) (w : List α) : palindromeSuffixCount [a] w ≤ w.count a := by
  simpa only [singleton_suffix_occurrence_count] using
    palindrome_suffix_count_le_occurrences [a] w (by simp [Palindrome])

theorem sum_map_add_nat {α : Type} (s : List α) (f g : α → Nat) :
    (s.map (fun a => f a + g a)).sum = (s.map f).sum + (s.map g).sum := by
  induction s with
  | nil => simp
  | cons a s ih => simp [ih]; omega

theorem sum_equality_indicators {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (s : List α) (a : α) :
    (s.map (fun b => if a=b then 1 else 0)).sum = s.count a := by
  induction s with
  | nil => simp
  | cons b s ih => by_cases h : a=b <;> simp_all [eq_comm] <;> omega

theorem sum_map_zero_nat {α : Type} (s : List α) :
    (s.map (fun _ => (0 : Nat))).sum = 0 := by
  induction s <;> simp_all

theorem sum_counts_over_cover {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (s xs : List α) (hs : s.Nodup) (hc : xs ⊆ s) :
    (s.map (fun a => xs.count a)).sum = xs.length := by
  induction xs with
  | nil => simp [sum_map_zero_nat]
  | cons x xs ih =>
    have hx : x ∈ s := hc (by simp)
    have ht : xs ⊆ s := fun a ha => hc (by simp [ha])
    have he (a : α) : (x::xs).count a = xs.count a + (if x=a then 1 else 0) := by
      by_cases h : x=a <;> simp_all [eq_comm] <;> omega
    simp only [he,sum_map_add_nat,sum_equality_indicators,ih ht,List.length_cons]
    rw [hs.count]
    simp [hx]

theorem suffix_palindrome_count_as_last_count {α : Type} [DecidableEq α]
    (a : α) (w : List α) :
    palindromeSuffixCount [a] w = ((palindromicFactors w).map List.getLast?).count (some a) := by
  rw [List.count_eq_countP, List.countP_map]
  simp only [palindromeSuffixCount,List.countP_eq_length_filter,Function.comp_def]
  congr 2
  funext p
  by_cases h : p.getLast? = some a <;>
    simp [List.singleton_suffix_iff_getLast?_eq_some,h]

theorem empty_last_palindrome_count {α : Type} [DecidableEq α] (w : List α) :
    ((palindromicFactors w).map List.getLast?).count none = 1 := by
  rw [List.count_eq_countP,List.countP_map,List.countP_eq_length_filter]
  have he : ((palindromicFactors w).filter
      (fun p => (p.getLast? == none))).length = ([[]] : List (List α)).length := by
    apply nodup_same_members_length
    · exact List.filter_sublist.nodup (palindromicFactors_nodup _)
    · simp
    · intro p
      cases p <;> simp [mem_palindromicFactors_iff, Factor, Palindrome]
  simpa [Function.comp_def] using he

theorem sum_singleton_palindrome_counts {α : Type} [DecidableEq α]
    (s w : List α) (hs : s.Nodup) (hw : w ⊆ s) :
    1 + (s.map (fun a => palindromeSuffixCount [a] w)).sum =
      (palindromicFactors w).length := by
  let labels := none :: s.map some
  have hn : labels.Nodup := by
    simpa [labels,List.Nodup,List.pairwise_map] using hs
  have hc : (palindromicFactors w).map List.getLast? ⊆ labels := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    cases he : p.getLast? with
    | none => simp [labels]
    | some a =>
      have ha : a ∈ w := ((mem_palindromicFactors_iff p w).mp hp).1.sublist.subset
        (List.mem_of_getLast? he)
      simp [labels,hw ha]
  have h := sum_counts_over_cover labels ((palindromicFactors w).map List.getLast?) hn hc
  simp only [labels,List.map_cons,List.sum_cons,List.map_map,List.length_map,
    Function.comp_def] at h
  rw [empty_last_palindrome_count] at h
  simpa only [← suffix_palindrome_count_as_last_count] using h

theorem sum_letter_defects {α : Type} [DecidableEq α]
    (s w : List α) (hs : s.Nodup) (hw : w ⊆ s) :
    (s.map (fun a => letterDefect a w)).sum = palindromeDefect w := by
  have hc := sum_counts_over_cover s w hs hw
  have hp := sum_singleton_palindrome_counts s w hs hw
  have he (a : α) : letterDefect a w + palindromeSuffixCount [a] w = w.count a := by
    have hb := singleton_palindrome_count_le_count a w
    unfold letterDefect
    omega
  have hsum := sum_map_add_nat s (fun a => letterDefect a w)
    (fun a => palindromeSuffixCount [a] w)
  simp only [he,hc] at hsum
  unfold palindromeDefect
  omega

theorem sum_letter_defects_alphabet {α : Type} [DecidableEq α] (w : List α) :
    (w.eraseDups.map (fun a => letterDefect a w)).sum = palindromeDefect w := by
  apply sum_letter_defects
  · exact nodup_eraseDups w
  · intro a ha; simpa using ha

theorem full_count_iff_letter_defects_zero {α : Type} [DecidableEq α] (w : List α) :
    (palindromicFactors w).length = w.length+1 ↔
      ∀ a ∈ w, letterDefect a w = 0 := by
  have hb := palindromic_factor_count_bound w
  have he : (palindromicFactors w).length = w.length+1 ↔ palindromeDefect w = 0 := by
    unfold palindromeDefect
    omega
  rw [he, ← sum_letter_defects_alphabet, List.sum_eq_zero_iff_forall_eq_nat]
  simp

theorem palindrome_singleton_suffix_iff_cons {α : Type} [DecidableEq α]
    (a : α) (p : List α) (hp : Palindrome p) :
    [a].IsSuffix p ↔ ∃ t, p = a::t := by
  have he : [a].IsSuffix p ↔ [a].IsPrefix p := by
    constructor
    · intro h
      have hr := List.reverse_prefix.mpr h
      simpa only [List.reverse_singleton,show p.reverse=p from hp] using hr
    · intro h
      apply List.reverse_prefix.mp
      simpa only [List.reverse_singleton,show p.reverse=p from hp] using h
  rw [he]
  cases p <;> simp [eq_comm]

theorem binary_singleton_palindrome_gap_count (a : Bool) (w : Word) :
    palindromeSuffixCount [a] w = (gapPalImage a w).length := by
  apply nodup_same_members_length
  · exact List.filter_sublist.nodup (palindromicFactors_nodup _)
  · exact gapPalImage_nodup a w
  · intro p
    simp only [List.mem_filter,decide_eq_true_eq,mem_gapPalImage_iff]
    constructor
    · rintro ⟨h,hp⟩
      obtain ⟨t,ht⟩ := (palindrome_singleton_suffix_iff_cons a p
        ((mem_palindromicFactors_iff p w).mp h).2).mp hp
      exact ⟨t,ht,h⟩
    · rintro ⟨t,ht,h⟩
      exact ⟨h,(palindrome_singleton_suffix_iff_cons a p
        ((mem_palindromicFactors_iff p w).mp h).2).mpr ⟨t,ht⟩⟩

theorem binary_letter_defect_gap (a : Bool) (w : Word) :
    letterDefect a w = palindromeDefect (letterGaps a w) := by
  have hl := letterGaps_length a w
  by_cases ha : a ∈ w
  · simp only [if_pos ha] at hl
    simp [letterDefect,binary_singleton_palindrome_gap_count,gapPalImage,ha,
      palindromeDefect,← hl]
  · simp [letterDefect,List.count_eq_zero.mpr ha,palindromeDefect,
      letterGaps_of_not_mem a w ha,palindromicFactors,factorOccurrences,
      Palindrome,List.eraseDups_cons]

theorem full_count_letter_defect_zero {α : Type} [DecidableEq α]
    (a : α) (w : List α) (hw : (palindromicFactors w).length = w.length+1) :
    letterDefect a w = 0 := by
  by_cases ha : a ∈ w
  · exact (full_count_iff_letter_defects_zero w).mp hw a ha
  · simp [letterDefect,List.count_eq_zero.mpr ha]

/-- The transport hypotheses are explicit; this does not assert that an
arbitrary erasure or projection satisfies them. -/
theorem two_transports_force_full_count {α : Type} [DecidableEq α]
    (u v z : List α) (a b : α) (hab : a ≠ b)
    (hv : (palindromicFactors v).length = v.length+1)
    (hz : (palindromicFactors z).length = z.length+1)
    (hcv : ∀ c, c ≠ a → v.count c = u.count c)
    (hpv : ∀ c, c ≠ a → palindromeSuffixCount [c] v = palindromeSuffixCount [c] u)
    (hcz : ∀ c, c ≠ b → z.count c = u.count c)
    (hpz : ∀ c, c ≠ b → palindromeSuffixCount [c] z = palindromeSuffixCount [c] u) :
    (palindromicFactors u).length = u.length+1 := by
  apply (full_count_iff_letter_defects_zero u).mpr
  intro c _
  by_cases hca : c = a
  · subst c
    have h := full_count_letter_defect_zero a z hz
    simpa only [letterDefect,hcz a hab,hpz a hab] using h
  · have h := full_count_letter_defect_zero c v hv
    simpa only [letterDefect,hcv c hca,hpv c hca] using h

end RichWords

#print axioms RichWords.palindrome_suffix_count_le_occurrences
#print axioms RichWords.singleton_suffix_occurrence_count
#print axioms RichWords.singleton_palindrome_count_le_count
#print axioms RichWords.sum_map_add_nat
#print axioms RichWords.sum_equality_indicators
#print axioms RichWords.sum_map_zero_nat
#print axioms RichWords.sum_counts_over_cover
#print axioms RichWords.suffix_palindrome_count_as_last_count
#print axioms RichWords.empty_last_palindrome_count
#print axioms RichWords.sum_singleton_palindrome_counts
#print axioms RichWords.sum_letter_defects
#print axioms RichWords.sum_letter_defects_alphabet
#print axioms RichWords.full_count_iff_letter_defects_zero
#print axioms RichWords.palindrome_singleton_suffix_iff_cons
#print axioms RichWords.binary_singleton_palindrome_gap_count
#print axioms RichWords.binary_letter_defect_gap
#print axioms RichWords.full_count_letter_defect_zero
#print axioms RichWords.two_transports_force_full_count
