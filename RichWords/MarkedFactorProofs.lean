import RichWords.MarkedProofs

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem marked_interior_reverse_membership {α : Type} [DecidableEq α]
    (mark : α → Bool) (p w : List α) :
    p ∈ markedPalindromeInteriors mark w.reverse ↔
      p ∈ markedPalindromeInteriors mark w := by
  have forward (v : List α) : p ∈ markedPalindromeInteriors mark v →
      p ∈ markedPalindromeInteriors mark v.reverse := by
    intro hp
    obtain ⟨hpal,a,b,ha,hb,hf⟩ := (mem_markedPalindromeInteriors_iff mark p v).mp hp
    apply (mem_markedPalindromeInteriors_iff mark p v.reverse).mpr
    refine ⟨hpal,b,a,hb,ha,?_⟩
    have hr := List.reverse_infix.mpr hf
    simpa only [List.reverse_cons,List.reverse_append,List.reverse_singleton,
      show p.reverse = p from hpal,List.singleton_append] using hr
  exact ⟨fun h => by simpa using forward w.reverse h, forward w⟩

theorem marked_interior_reverse_count {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) :
    (markedPalindromeInteriors mark w.reverse).length =
      (markedPalindromeInteriors mark w).length := by
  apply nodup_same_members_length
  · exact markedPalindromeInteriors_nodup _ _
  · exact markedPalindromeInteriors_nodup _ _
  · exact fun p => marked_interior_reverse_membership mark p w

theorem marked_interior_defect_reverse {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) :
    markedInteriorDefect mark w.reverse = markedInteriorDefect mark w := by
  simp [markedInteriorDefect,marked_interior_reverse_count]

theorem marked_interior_defect_append_singleton_le {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) (a : α) :
    markedInteriorDefect mark w ≤ markedInteriorDefect mark (w ++ [a]) := by
  have h0 := marked_interior_defect_add_count mark w
  have h1 := marked_interior_defect_add_count mark (w ++ [a])
  cases ha : mark a with
  | false =>
    have he := unmarked_append_interior_count mark w a ha
    simp only [List.countP_append,List.countP_singleton,ha] at h1
    omega
  | true =>
    have hb := marked_interior_extension_bound mark w a
    simp only [List.countP_append,List.countP_singleton,ha,ite_true] at h1
    omega

theorem marked_interior_defect_append_le {α : Type} [DecidableEq α]
    (mark : α → Bool) (w v : List α) :
    markedInteriorDefect mark w ≤ markedInteriorDefect mark (w ++ v) := by
  have main (u : List α) :
      markedInteriorDefect mark w ≤ markedInteriorDefect mark (w ++ u.reverse) := by
    induction u with
    | nil => simp
    | cons a u ih =>
      have hs := marked_interior_defect_append_singleton_le mark (w ++ u.reverse) a
      simpa [List.reverse_cons,List.append_assoc] using Nat.le_trans ih hs
  simpa using main v.reverse

theorem marked_interior_defect_prepend_le {α : Type} [DecidableEq α]
    (mark : α → Bool) (w v : List α) :
    markedInteriorDefect mark w ≤ markedInteriorDefect mark (v ++ w) := by
  have h := marked_interior_defect_append_le mark w.reverse v.reverse
  have he : w.reverse ++ v.reverse = (v ++ w).reverse := by simp
  rw [he,marked_interior_defect_reverse,marked_interior_defect_reverse] at h
  exact h

theorem marked_interior_defect_factor_le {α : Type} [DecidableEq α]
    (mark : α → Bool) (u w : List α) (hf : Factor u w) :
    markedInteriorDefect mark u ≤ markedInteriorDefect mark w := by
  obtain ⟨s,t,hw⟩ := hf
  subst w
  exact Nat.le_trans (marked_interior_defect_prepend_le mark u s)
    (marked_interior_defect_append_le mark (s ++ u) t)

theorem marked_interior_zero_factor {α : Type} [DecidableEq α]
    (mark : α → Bool) (u w : List α) (hf : Factor u w)
    (hz : markedInteriorDefect mark w = 0) :
    markedInteriorDefect mark u = 0 := by
  have h := marked_interior_defect_factor_le mark u w hf
  omega

theorem marked_projection_failure :
    markedInteriorDefect (fun a : Nat => decide (a < 5)) [0,5,1,4,2,3] = 0 ∧
    markedInteriorDefect (fun a : Nat => decide (a < 4)) [0,5,1,4,2,3] = 0 ∧
    markedInteriorDefect (fun a : Nat => decide (a < 4))
      (([0,5,1,4,2,3] : List Nat).filter (fun a => decide (a < 5))) = 1 := by
  decide

end RichWords

#print axioms RichWords.marked_interior_reverse_membership
#print axioms RichWords.marked_interior_reverse_count
#print axioms RichWords.marked_interior_defect_reverse
#print axioms RichWords.marked_interior_defect_append_singleton_le
#print axioms RichWords.marked_interior_defect_append_le
#print axioms RichWords.marked_interior_defect_prepend_le
#print axioms RichWords.marked_interior_defect_factor_le
#print axioms RichWords.marked_interior_zero_factor
#print axioms RichWords.marked_projection_failure
