import RichWords.GapProofs
import RichWords.ProtectedDefinitions
namespace RichWords

theorem map_word_eq_iff {α β : Type} (f : α → β) (hf : Function.Injective f)
    (u v : List α) : u.map f = v.map f ↔ u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp
  | cons a u ih =>
    cases v with
    | nil => simp
    | cons b v => simp only [List.map_cons, List.cons.injEq, ih]; exact and_congr hf.eq_iff Iff.rfl

theorem prefixes_map_word {α β : Type} (f : α → β) (w : List α) :
    prefixes (w.map f) = (prefixes w).map (List.map f) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [prefixes, ih, List.map_map, Function.comp_def]

theorem factors_map_word {α β : Type} (f : α → β) (w : List α) :
    factorOccurrences (w.map f) = (factorOccurrences w).map (List.map f) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, factorOccurrences, List.map_append, ih]
    rw [show prefixes (f a :: w.map f) = (prefixes (a :: w)).map (List.map f) from
      prefixes_map_word f (a :: w)]

theorem palindrome_map_word_iff {α β : Type} (f : α → β) (hf : Function.Injective f)
    (w : List α) : Palindrome (w.map f) ↔ Palindrome w := by
  simp only [Palindrome, ← List.map_reverse, map_word_eq_iff f hf]

theorem palindromicFactors_map_membership {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : List α) (p : List β) :
    p ∈ palindromicFactors (w.map f) ↔ p ∈ (palindromicFactors w).map (List.map f) := by
  simp only [palindromicFactors, List.mem_eraseDups, List.mem_filter,
    factors_map_word, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hp⟩
    exact ⟨u, ⟨hu, (palindrome_map_word_iff f hf u).mp hp⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hp⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, (palindrome_map_word_iff f hf u).mpr hp⟩

theorem palindromic_count_injective_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : List α) :
    (palindromicFactors (w.map f)).length = (palindromicFactors w).length := by
  have hn : ((palindromicFactors w).map (List.map f)).Nodup := by
    simpa only [List.Nodup, List.pairwise_map, ne_eq, map_word_eq_iff f hf] using
      palindromicFactors_nodup w
  have h1 := nodup_subset_length_le (palindromicFactors (w.map f))
    ((palindromicFactors w).map (List.map f)) (palindromicFactors_nodup _) (fun p hp =>
      (palindromicFactors_map_membership f hf w p).mp hp)
  have h2 := nodup_subset_length_le ((palindromicFactors w).map (List.map f))
    (palindromicFactors (w.map f)) hn (fun p hp =>
      (palindromicFactors_map_membership f hf w p).mpr hp)
  simp only [List.length_map] at h1 h2
  omega

theorem palindromeDefect_injective_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : List α) :
    palindromeDefect (w.map f) = palindromeDefect w := by
  simp [palindromeDefect, palindromic_count_injective_map f hf]

theorem bitGap_injective (a : Bool) : Function.Injective (bitGap a) := by
  intro b c h
  cases a <;> cases b <;> cases c <;> simp_all [bitGap]

theorem protected_as_gaps (a : Bool) (w : Word) :
    protectedExpand a w = expandGaps a (w.map (bitGap a)) := by
  induction w with
  | nil => rfl
  | cons b w ih => cases a <;> cases b <;> simp_all [protectedExpand, expandGaps, bitGap]

theorem protected_same_gaps (a : Bool) (w : Word) :
    letterGaps a (protectedExpand a w) = w.map (bitGap a) := by
  rw [protected_as_gaps]
  simpa using letterGaps_expansion a (w.map (bitGap a)) 0

theorem protected_other_gapsAfter (a : Bool) (w : Word) (k : Nat) :
    gapsAfter (!a) k (protectedExpand a w) = (gapsAfter (!a) k w).map Nat.succ := by
  induction w generalizing k with
  | nil => cases a <;> simp [protectedExpand, gapsAfter]
  | cons b w ih => cases a <;> cases b <;> simp_all [protectedExpand, gapsAfter]

theorem protected_other_gaps (a : Bool) (w : Word) :
    letterGaps (!a) (protectedExpand a w) = (letterGaps (!a) w).map Nat.succ := by
  induction w with
  | nil => cases a <;> simp [protectedExpand, letterGaps]
  | cons b w ih =>
    cases a <;> cases b <;> simp_all [protectedExpand, letterGaps]
    all_goals first
      | exact protected_other_gapsAfter false w 0
      | exact protected_other_gapsAfter true w 0

theorem protected_same_defect (a : Bool) (w : Word) :
    palindromeDefect (letterGaps a (protectedExpand a w)) = palindromeDefect w := by
  rw [protected_same_gaps, palindromeDefect_injective_map _ (bitGap_injective a)]

theorem protected_other_defect (a : Bool) (w : Word) :
    palindromeDefect (letterGaps (!a) (protectedExpand a w)) =
      palindromeDefect (letterGaps (!a) w) := by
  rw [protected_other_gaps,
    palindromeDefect_injective_map Nat.succ (fun _ _ h => Nat.succ.inj h)]

theorem protected_defect_identity (a : Bool) (w : Word) :
    palindromeDefect (protectedExpand a w) =
      palindromeDefect w + palindromeDefect (letterGaps (!a) w) := by
  have h := binary_gap_defect_identity (protectedExpand a w)
  have hs := protected_same_defect a w
  have ho := protected_other_defect a w
  cases a <;> simp_all <;> omega

theorem rich_iff_defect_zero (w : Word) :
    Rich w ↔ palindromeDefect w = 0 := by
  have hb := palindromic_factor_count_bound w
  unfold Rich palindromeDefect
  omega

theorem protected_rich_iff (a : Bool) (w : Word) :
    Rich (protectedExpand a w) ↔ Rich w := by
  rw [rich_iff_defect_zero, rich_iff_defect_zero, protected_defect_identity]
  have h := binary_gap_defect_identity w
  cases a <;> simp_all <;> omega

theorem protected_injective (a : Bool) : Function.Injective (protectedExpand a) := by
  intro u v h
  have hg := congrArg (letterGaps a) h
  rw [protected_same_gaps, protected_same_gaps] at hg
  exact (map_word_eq_iff _ (bitGap_injective a) u v).mp hg

theorem protected_length (a : Bool) (w : Word) :
    (protectedExpand a w).length = w.length + w.count (!a) + 1 := by
  induction w with
  | nil => cases a <;> simp [protectedExpand]
  | cons b w ih => cases a <;> cases b <;> simp_all [protectedExpand] <;> omega

end RichWords

#print axioms RichWords.map_word_eq_iff
#print axioms RichWords.prefixes_map_word
#print axioms RichWords.factors_map_word
#print axioms RichWords.palindrome_map_word_iff
#print axioms RichWords.palindromicFactors_map_membership
#print axioms RichWords.palindromic_count_injective_map
#print axioms RichWords.palindromeDefect_injective_map
#print axioms RichWords.bitGap_injective
#print axioms RichWords.protected_as_gaps
#print axioms RichWords.protected_same_gaps
#print axioms RichWords.protected_other_gapsAfter
#print axioms RichWords.protected_other_gaps
#print axioms RichWords.protected_same_defect
#print axioms RichWords.protected_other_defect
#print axioms RichWords.protected_defect_identity
#print axioms RichWords.rich_iff_defect_zero
#print axioms RichWords.protected_rich_iff
#print axioms RichWords.protected_injective
#print axioms RichWords.protected_length
