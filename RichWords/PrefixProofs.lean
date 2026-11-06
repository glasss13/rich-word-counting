import RichWords.Proofs

namespace RichWords

/-- Appending k letters introduces at most k distinct palindromes. -/
theorem palindromic_factor_append_bound {α : Type} [DecidableEq α]
    (x y : List α) :
    (palindromicFactors (x ++ y)).length ≤ (palindromicFactors x).length + y.length := by
  induction y generalizing x with
  | nil => simp
  | cons a y ih =>
    have h := ih (x ++ [a])
    have hstep := palindromic_factor_extension_bound x a
    simp only [List.append_assoc, List.singleton_append] at h
    simp only [List.length_cons]
    omega

/-- A prefix of a word with the maximum palindrome count also has that count. -/
theorem full_palindrome_count_prefix {α : Type} [DecidableEq α]
    (x y : List α)
    (h : (palindromicFactors (x ++ y)).length = (x ++ y).length + 1) :
    (palindromicFactors x).length = x.length + 1 := by
  have hb := palindromic_factor_append_bound x y
  have hx := palindromic_factor_count_bound x
  simp only [List.length_append] at h
  omega

theorem rich_prefix (x y : Word) (h : Rich (x ++ y)) : Rich x :=
  full_palindrome_count_prefix x y h

/-- Every letter of a maximal-count extension creates a palindrome. -/
theorem full_count_extension_has_new_palindrome {α : Type} [DecidableEq α]
    (x : List α) (a : α)
    (h : (palindromicFactors (x ++ [a])).length = (x ++ [a]).length + 1) :
    ∃ p, p ∈ palindromicFactors (x ++ [a]) ∧ p ∉ palindromicFactors x := by
  classical
  apply Classical.byContradiction
  intro hn
  have hs : palindromicFactors (x ++ [a]) ⊆ palindromicFactors x := by
    intro p hp
    exact Classical.byContradiction (fun hnot => hn ⟨p, hp, hnot⟩)
  have hb := nodup_subset_length_le _ _ (palindromicFactors_nodup _) hs
  have hx := palindromic_factor_count_bound x
  simp only [List.length_append, List.length_singleton] at h
  omega

theorem palindrome_membership_append {α : Type} [DecidableEq α]
    (p x y : List α) (h : p ∈ palindromicFactors x) :
    p ∈ palindromicFactors (x ++ y) := by
  obtain ⟨hf, hp⟩ := (mem_palindromicFactors_iff p x).mp h
  apply (mem_palindromicFactors_iff p (x ++ y)).mpr
  refine ⟨?_, hp⟩
  obtain ⟨u, v, hv⟩ := hf
  exact ⟨u, v ++ y, by simp [← hv, List.append_assoc]⟩

/-- Sharing the first new letter forces a common new palindrome. -/
theorem shared_first_letter_new_palindrome {α : Type} [DecidableEq α]
    (x : List α) (a : α) (u v : List α)
    (h : (palindromicFactors (x ++ a :: u)).length = (x ++ a :: u).length + 1) :
    ∃ p, p ∈ palindromicFactors (x ++ a :: u) ∧
      p ∈ palindromicFactors (x ++ a :: v) ∧ p ∉ palindromicFactors x := by
  have hprefix := full_palindrome_count_prefix (x ++ [a]) u (by simpa using h)
  obtain ⟨p, hp, hnot⟩ := full_count_extension_has_new_palindrome x a hprefix
  refine ⟨p, ?_, ?_, hnot⟩
  · simpa using palindrome_membership_append p (x ++ [a]) u hp
  · simpa using palindrome_membership_append p (x ++ [a]) v hp

/-- Disjoint sets of newly introduced palindromes require different next letters. -/
theorem disjoint_new_palindromes_distinct_letters {α : Type} [DecidableEq α]
    (x : List α) (a b : α) (u v : List α)
    (h : (palindromicFactors (x ++ a :: u)).length = (x ++ a :: u).length + 1)
    (hdis : ∀ p, p ∈ palindromicFactors (x ++ a :: u) →
      p ∈ palindromicFactors (x ++ b :: v) → p ∈ palindromicFactors x) : a ≠ b := by
  intro he
  subst b
  obtain ⟨p, hu, hv, hn⟩ := shared_first_letter_new_palindrome x a u v h
  exact hn (hdis p hu hv)

/-- There cannot be three pairwise disjoint novel-palindrome branches in binary. -/
theorem binary_three_branches_not_disjoint
    (x : Word) (a b c : Bool) (u v w : Word)
    (hu : Rich (x ++ a :: u)) (hv : Rich (x ++ b :: v))
    (hab : ∀ p, p ∈ palindromicFactors (x ++ a :: u) →
      p ∈ palindromicFactors (x ++ b :: v) → p ∈ palindromicFactors x)
    (hac : ∀ p, p ∈ palindromicFactors (x ++ a :: u) →
      p ∈ palindromicFactors (x ++ c :: w) → p ∈ palindromicFactors x)
    (hbc : ∀ p, p ∈ palindromicFactors (x ++ b :: v) →
      p ∈ palindromicFactors (x ++ c :: w) → p ∈ palindromicFactors x) : False := by
  have h1 := disjoint_new_palindromes_distinct_letters x a b u v hu hab
  have h2 := disjoint_new_palindromes_distinct_letters x a c u w hu hac
  have h3 := disjoint_new_palindromes_distinct_letters x b c v w hv hbc
  cases a <;> cases b <;> cases c <;> simp_all

end RichWords

#print axioms RichWords.palindromic_factor_append_bound
#print axioms RichWords.full_palindrome_count_prefix
#print axioms RichWords.rich_prefix
#print axioms RichWords.full_count_extension_has_new_palindrome
#print axioms RichWords.palindrome_membership_append
#print axioms RichWords.shared_first_letter_new_palindrome
#print axioms RichWords.disjoint_new_palindromes_distinct_letters
#print axioms RichWords.binary_three_branches_not_disjoint
