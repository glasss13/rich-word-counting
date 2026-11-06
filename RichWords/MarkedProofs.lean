import RichWords.MarkedDefinitions
import RichWords.OccurrenceProofs

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem mem_markedPalindromeInteriors_iff {α : Type} [DecidableEq α]
    (mark : α → Bool) (p w : List α) :
    p ∈ markedPalindromeInteriors mark w ↔
      Palindrome p ∧ ∃ a b, mark a = true ∧ mark b = true ∧
        Factor (a :: (p ++ [b])) w := by
  simp only [markedPalindromeInteriors, List.mem_filter, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, mem_palindromicFactors_iff, Factor]
  constructor
  · rintro ⟨⟨_,hp⟩,a,_,ha,b,_,hb,hf⟩
    exact ⟨hp,a,b,ha,hb,hf⟩
  · rintro ⟨hp,a,b,ha,hb,hf⟩
    have hsub := hf.sublist.subset
    have ha' : a ∈ w := hsub (by simp)
    have hb' : b ∈ w := hsub (by simp)
    have hpf : Factor p (a :: (p ++ [b])) := by
      exact (List.prefix_append p [b]).isInfix.trans (List.suffix_cons a (p ++ [b])).isInfix
    exact ⟨⟨hpf.trans hf,hp⟩,a,ha',ha,b,hb',hb,hf⟩

theorem markedPalindromeInteriors_nodup {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) :
    (markedPalindromeInteriors mark w).Nodup := by
  exact List.filter_sublist.nodup (palindromicFactors_nodup w)

theorem marked_interior_membership_append {α : Type} [DecidableEq α]
    (mark : α → Bool) (p w v : List α)
    (hp : p ∈ markedPalindromeInteriors mark w) :
    p ∈ markedPalindromeInteriors mark (w ++ v) := by
  obtain ⟨hpal,a,b,ha,hb,hf⟩ := (mem_markedPalindromeInteriors_iff mark p w).mp hp
  apply (mem_markedPalindromeInteriors_iff mark p (w ++ v)).mpr
  exact ⟨hpal,a,b,ha,hb,hf.trans (List.prefix_append w v).isInfix⟩

theorem new_marked_interior_suffix {α : Type} [DecidableEq α]
    (mark : α → Bool) (p w : List α) (a : α)
    (hp : p ∈ markedPalindromeInteriors mark (w ++ [a]))
    (hn : p ∉ markedPalindromeInteriors mark w) :
    Palindrome p ∧ mark a = true ∧ ∃ b, mark b = true ∧ (b :: p).IsSuffix w := by
  obtain ⟨hpal,b,c,hb,hc,hf⟩ :=
    (mem_markedPalindromeInteriors_iff mark p (w ++ [a])).mp hp
  rcases List.infix_concat_iff.mp hf with hs | hold
  · have hs' : ((b :: p) ++ [c]).IsSuffix (w ++ [a]) := by simpa using hs
    have hsplit := (List.suffix_append_inj_of_length_eq
      (l₁ := b :: p) (l₂ := w) (s₁ := [c]) (s₂ := [a]) (by simp)).mp hs'
    have hca : c = a := by simpa using hsplit.2
    subst c
    exact ⟨hpal,hc,b,hb,hsplit.1⟩
  · exact False.elim (hn ((mem_markedPalindromeInteriors_iff mark p w).mpr
      ⟨hpal,b,c,hb,hc,hold⟩))

theorem new_marked_interior_eq_of_length_le {α : Type} [DecidableEq α]
    (mark : α → Bool) (p q w : List α) (a : α)
    (hp : p ∈ markedPalindromeInteriors mark (w ++ [a]))
    (hn : p ∉ markedPalindromeInteriors mark w)
    (hq : q ∈ markedPalindromeInteriors mark (w ++ [a]))
    (hqn : q ∉ markedPalindromeInteriors mark w)
    (hl : p.length ≤ q.length) : p = q := by
  obtain ⟨hpal,_,c,hc,hcp⟩ := new_marked_interior_suffix mark p w a hp hn
  obtain ⟨hqpal,_,b,hb,hbq⟩ := new_marked_interior_suffix mark q w a hq hqn
  have hps : p.IsSuffix w := (List.suffix_cons c p).trans hcp
  have hqs : q.IsSuffix w := (List.suffix_cons b q).trans hbq
  by_cases he : p.length = q.length
  · exact (List.suffix_of_suffix_length_le hps hqs hl).eq_of_length he
  · have hs : (c :: p).IsSuffix q :=
      List.suffix_of_suffix_length_le hcp hqs (by simp only [List.length_cons]; omega)
    have hpre : (p ++ [c]).IsPrefix q := by
      have hr := List.reverse_prefix.mpr hs
      simpa only [List.reverse_cons,show p.reverse=p from hpal,
        show q.reverse=q from hqpal] using hr
    have hpre' : (b :: (p ++ [c])).IsPrefix (b :: q) := by
      simpa only [List.cons_prefix_cons, true_and] using hpre
    have hf : Factor (b :: (p ++ [c])) w := hpre'.isInfix.trans hbq.isInfix
    exact False.elim (hn ((mem_markedPalindromeInteriors_iff mark p w).mpr
      ⟨hpal,b,c,hb,hc,hf⟩))

theorem new_marked_interior_unique {α : Type} [DecidableEq α]
    (mark : α → Bool) (p q w : List α) (a : α)
    (hp : p ∈ markedPalindromeInteriors mark (w ++ [a]))
    (hn : p ∉ markedPalindromeInteriors mark w)
    (hq : q ∈ markedPalindromeInteriors mark (w ++ [a]))
    (hqn : q ∉ markedPalindromeInteriors mark w) : p = q := by
  rcases Nat.le_total p.length q.length with hl | hl
  · exact new_marked_interior_eq_of_length_le mark p q w a hp hn hq hqn hl
  · exact (new_marked_interior_eq_of_length_le mark q p w a hq hqn hp hn hl).symm

theorem at_most_one_new_marked_interior {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) (a : α) :
    ((markedPalindromeInteriors mark (w ++ [a])).filter
      (fun p => decide (p ∉ markedPalindromeInteriors mark w))).length ≤ 1 := by
  let xs := (markedPalindromeInteriors mark (w ++ [a])).filter
      (fun p => decide (p ∉ markedPalindromeInteriors mark w))
  have hn : xs.Nodup := List.filter_sublist.nodup (markedPalindromeInteriors_nodup _ _)
  have hu : ∀ p ∈ xs, ∀ q ∈ xs, p = q := by
    intro p hp q hq
    have hp' : p ∈ markedPalindromeInteriors mark (w ++ [a]) ∧
        p ∉ markedPalindromeInteriors mark w := by simpa [xs] using hp
    have hq' : q ∈ markedPalindromeInteriors mark (w ++ [a]) ∧
        q ∉ markedPalindromeInteriors mark w := by simpa [xs] using hq
    exact new_marked_interior_unique mark p q w a hp'.1 hp'.2 hq'.1 hq'.2
  change xs.length ≤ 1
  generalize hx : xs = ys at *
  cases ys with
  | nil => simp
  | cons p ys =>
    cases ys with
    | nil => simp
    | cons q zs =>
      have he : p=q := hu p (by simp) q (by simp)
      subst q
      simp at hn

theorem marked_interior_extension_bound {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) (a : α) :
    (markedPalindromeInteriors mark (w ++ [a])).length ≤
      (markedPalindromeInteriors mark w).length + 1 := by
  let xs := markedPalindromeInteriors mark (w ++ [a])
  let old := xs.filter (fun p => decide (p ∈ markedPalindromeInteriors mark w))
  have hn : old.Nodup := List.filter_sublist.nodup (markedPalindromeInteriors_nodup _ _)
  have hs : old ⊆ markedPalindromeInteriors mark w := by
    intro p hp
    simpa [old] using (List.mem_filter.mp hp).2
  have ho := nodup_subset_length_le old (markedPalindromeInteriors mark w) hn hs
  have hnew := at_most_one_new_marked_interior mark w a
  have hsplit := List.length_eq_countP_add_countP
    (fun p => decide (p ∈ markedPalindromeInteriors mark w)) (l := xs)
  simp only [List.countP_eq_length_filter] at hsplit
  simp only [Bool.not_eq_true,decide_eq_false_iff_not] at hsplit
  change xs.length ≤ (markedPalindromeInteriors mark w).length + 1
  dsimp [old] at ho
  dsimp [xs] at *
  omega

theorem unmarked_append_interior_count {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) (a : α) (ha : mark a = false) :
    (markedPalindromeInteriors mark (w ++ [a])).length =
      (markedPalindromeInteriors mark w).length := by
  apply nodup_same_members_length
  · exact markedPalindromeInteriors_nodup _ _
  · exact markedPalindromeInteriors_nodup _ _
  · intro p
    constructor
    · intro hp
      by_cases hold : p ∈ markedPalindromeInteriors mark w
      · exact hold
      · have h := (new_marked_interior_suffix mark p w a hp hold).2.1
        simp [ha] at h
    · exact marked_interior_membership_append mark p w [a]

theorem new_marked_interior_prior_mark {α : Type} [DecidableEq α]
    (mark : α → Bool) (p w : List α) (a : α)
    (hp : p ∈ markedPalindromeInteriors mark (w ++ [a]))
    (hn : p ∉ markedPalindromeInteriors mark w) : 0 < w.countP mark := by
  obtain ⟨_,_,b,hb,hs⟩ := new_marked_interior_suffix mark p w a hp hn
  exact List.countP_pos_iff.mpr ⟨b,hs.sublist.subset (by simp),hb⟩

theorem marked_interior_count_bound {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) :
    (markedPalindromeInteriors mark w).length ≤ w.countP mark - 1 := by
  have main (v : List α) :
      (markedPalindromeInteriors mark v.reverse).length ≤ v.reverse.countP mark - 1 := by
    induction v with
    | nil => simp [markedPalindromeInteriors]
    | cons a v ih =>
      simp only [List.reverse_cons]
      by_cases hz : v.reverse.countP mark = 0
      · have hold : markedPalindromeInteriors mark v.reverse = [] := by
          apply List.length_eq_zero_iff.mp
          omega
        have hnew : markedPalindromeInteriors mark (v.reverse ++ [a]) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro p hp
          have hn : p ∉ markedPalindromeInteriors mark v.reverse := by simp [hold]
          have hpos := new_marked_interior_prior_mark mark p v.reverse a hp hn
          omega
        simp [hnew]
      · cases ha : mark a with
        | false =>
          rw [unmarked_append_interior_count mark v.reverse a ha]
          simpa [ha] using ih
        | true =>
          have hb := marked_interior_extension_bound mark v.reverse a
          simp only [List.countP_append,List.countP_singleton,ha,ite_true]
          omega
  simpa using main w.reverse

theorem marked_interior_defect_add_count {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) :
    markedInteriorDefect mark w + (markedPalindromeInteriors mark w).length =
      w.countP mark - 1 := by
  have hb := marked_interior_count_bound mark w
  unfold markedInteriorDefect
  omega

theorem marked_interior_empty_of_at_most_one_mark {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) (h : w.countP mark ≤ 1) :
    markedPalindromeInteriors mark w = [] := by
  have hb := marked_interior_count_bound mark w
  apply List.length_eq_zero_iff.mp
  omega

theorem wrapped_factor_strip {α : Type} [DecidableEq α]
    (p v : List α) (a b c d : α)
    (hf : Factor (c :: (p ++ [d])) (a :: (v ++ [b]))) : Factor p v := by
  have hpw : Factor p (c :: (p ++ [d])) :=
    (List.prefix_append p [d]).isInfix.trans (List.suffix_cons c (p ++ [d])).isInfix
  rcases List.infix_cons_iff.mp hf with hpre | htail
  · have ht : (p ++ [d]).IsPrefix (v ++ [b]) := (List.cons_prefix_cons.mp hpre).2
    rcases List.prefix_concat_iff.mp ht with he | hs
    · have he' : p = v := (List.append_inj' he (by simp)).1
      simp [he',Factor]
    · exact ((List.prefix_append p [d]).trans hs).isInfix
  · rcases List.infix_concat_iff.mp htail with hs | hold
    · have hs' : ((c :: p) ++ [d]).IsSuffix (v ++ [b]) := by simpa using hs
      have hshort := (List.suffix_append_inj_of_length_eq
        (l₁ := c :: p) (l₂ := v) (s₁ := [d]) (s₂ := [b]) (by simp)).mp hs'
      exact ((List.suffix_cons c p).trans hshort.1).isInfix
    · exact hpw.trans hold

theorem factor_has_wrapped_extension {α : Type} [DecidableEq α]
    (p v : List α) (a b : α) (hf : Factor p v) :
    ∃ c d, Factor (c :: (p ++ [d])) (a :: (v ++ [b])) := by
  obtain ⟨s,t,hv⟩ := hf
  subst v
  rcases List.eq_nil_or_concat (a :: s) with hn | ⟨l,c,hl⟩
  · simp at hn
  · have hl' : a :: s = l ++ [c] := by simpa using hl
    obtain ⟨d,r,hr⟩ := List.exists_cons_of_ne_nil (l := t ++ [b]) (by simp)
    refine ⟨c,d,l,r,?_⟩
    calc
      l ++ (c :: (p ++ [d])) ++ r = (l ++ [c]) ++ p ++ (d :: r) := by simp [List.append_assoc]
      _ = (a :: s) ++ p ++ (t ++ [b]) := by rw [← hl',← hr]
      _ = a :: ((s ++ p ++ t) ++ [b]) := by simp [List.append_assoc]

theorem all_marked_interior_count {α : Type} [DecidableEq α]
    (v : List α) (a b : α) :
    (markedPalindromeInteriors (fun _ => true) (a :: (v ++ [b]))).length =
      (palindromicFactors v).length := by
  apply nodup_same_members_length
  · exact markedPalindromeInteriors_nodup _ _
  · exact palindromicFactors_nodup _
  · intro p
    rw [mem_markedPalindromeInteriors_iff,mem_palindromicFactors_iff]
    constructor
    · rintro ⟨hp,c,d,_,_,hf⟩
      exact ⟨wrapped_factor_strip p v a b c d hf,hp⟩
    · rintro ⟨hf,hp⟩
      obtain ⟨c,d,hcd⟩ := factor_has_wrapped_extension p v a b hf
      exact ⟨hp,c,d,rfl,rfl,hcd⟩

theorem all_marked_interior_defect {α : Type} [DecidableEq α]
    (v : List α) (a b : α) :
    markedInteriorDefect (fun _ => true) (a :: (v ++ [b])) = palindromeDefect v := by
  simp [markedInteriorDefect,all_marked_interior_count,palindromeDefect]

theorem rich_word_can_have_positive_marked_defect :
    (palindromicFactors ([1,1,0,2,2] : List Nat)).length = 6 ∧
    ([1,1,0,2,2] : List Nat).countP (fun a => decide (1 ≤ a)) = 4 ∧
    (markedPalindromeInteriors (fun a : Nat => decide (1 ≤ a)) [1,1,0,2,2]).length = 2 ∧
    markedInteriorDefect (fun a : Nat => decide (1 ≤ a)) [1,1,0,2,2] = 1 := by
  decide

end RichWords

#print axioms RichWords.mem_markedPalindromeInteriors_iff
#print axioms RichWords.markedPalindromeInteriors_nodup
#print axioms RichWords.marked_interior_membership_append
#print axioms RichWords.new_marked_interior_suffix
#print axioms RichWords.new_marked_interior_eq_of_length_le
#print axioms RichWords.new_marked_interior_unique
#print axioms RichWords.at_most_one_new_marked_interior
#print axioms RichWords.marked_interior_extension_bound
#print axioms RichWords.unmarked_append_interior_count
#print axioms RichWords.new_marked_interior_prior_mark
#print axioms RichWords.marked_interior_count_bound
#print axioms RichWords.marked_interior_defect_add_count
#print axioms RichWords.marked_interior_empty_of_at_most_one_mark
#print axioms RichWords.wrapped_factor_strip
#print axioms RichWords.factor_has_wrapped_extension
#print axioms RichWords.all_marked_interior_count
#print axioms RichWords.all_marked_interior_defect
#print axioms RichWords.rich_word_can_have_positive_marked_defect
