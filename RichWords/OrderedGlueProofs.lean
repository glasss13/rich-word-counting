import RichWords.MarkedFactorProofs
import RichWords.LeafContractionProofs
import RichWords.DefectCoordinateProofs
import RichWords.OrderedGlueDefinitions
import RichWords.ProtectedProofs
import RichWords.FramedGapProofs

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem ordered_singleton_marked_zero {α : Type} [DecidableEq α]
    (a : α) (w : List α)
    (hw : (palindromicFactors w).length = w.length+1) :
    markedInteriorDefect (fun b => decide (b=a)) w = 0 := by
  let mark := fun b => decide (b=a)
  let interiors := markedPalindromeInteriors mark w
  let suffixes := (palindromicFactors w).filter (fun p => decide ([a].IsSuffix p))
  let cover := [a] :: interiors.map (fun p => a :: (p ++ [a]))
  have hs : suffixes ⊆ cover := by
    intro p hp
    have hp' : p ∈ palindromicFactors w ∧ [a].IsSuffix p := by
      simpa only [suffixes,List.mem_filter,decide_eq_true_eq] using hp
    obtain ⟨hf,hpal⟩ := (mem_palindromicFactors_iff p w).mp hp'.1
    obtain ⟨t,rfl⟩ := (palindrome_singleton_suffix_iff_cons a p hpal).mp hp'.2
    rcases List.eq_nil_or_concat t with ht | ⟨v,b,ht⟩
    · subst t
      simp [cover]
    · subst t
      simp only [List.concat_eq_append] at hpal hf ⊢
      have he : b :: (v.reverse ++ [a]) = a :: (v ++ [b]) := by
        simpa only [Palindrome,List.reverse_cons,List.reverse_append,List.reverse_singleton,
          List.singleton_append] using hpal
      have hba : b=a := (List.cons.inj he).1
      subst b
      have hv : Palindrome v := (List.append_cancel_right (List.cons.inj he).2)
      have hi : v ∈ interiors :=
        (mem_markedPalindromeInteriors_iff mark v w).mpr ⟨hv,a,a,by simp [mark],by simp [mark],hf⟩
      simp only [cover,List.mem_cons,List.mem_map]
      exact Or.inr ⟨v,hi,rfl⟩
  have hn : suffixes.Nodup := List.filter_sublist.nodup (palindromicFactors_nodup w)
  have hle := nodup_subset_length_le suffixes cover hn hs
  have hc := full_count_palindrome_occurrences [a] w (by simp [Palindrome]) hw
  rw [singleton_suffix_occurrence_count] at hc
  change w.count a = suffixes.length at hc
  have hm : w.countP mark = w.count a := by
    simp only [mark,List.count_eq_countP]
    apply List.countP_congr
    intro b hb
    simp only [decide_eq_true_eq,beq_iff_eq]
  have hh := marked_interior_defect_add_count mark w
  change markedInteriorDefect mark w + interiors.length = w.countP mark-1 at hh
  have hcover : cover.length = interiors.length+1 := by simp [cover]
  rw [hcover] at hle
  change markedInteriorDefect mark w = 0
  omega

theorem ordered_marked_congr {α : Type} [DecidableEq α]
    (mark other : α → Bool) (w : List α)
    (he : ∀ a ∈ w, mark a = other a) :
    markedInteriorDefect mark w = markedInteriorDefect other w := by
  have hc : w.countP mark = w.countP other := List.countP_congr (fun a ha => by rw [he a ha])
  have hi : (markedPalindromeInteriors mark w).length =
      (markedPalindromeInteriors other w).length := by
    apply nodup_same_members_length
    · exact markedPalindromeInteriors_nodup _ _
    · exact markedPalindromeInteriors_nodup _ _
    · intro p
      simp only [mem_markedPalindromeInteriors_iff]
      constructor <;> rintro ⟨hpal,a,b,ha,hb,hf⟩
      · exact ⟨hpal,a,b,by rwa [← he a (hf.sublist.subset (by simp))],
          by rwa [← he b (hf.sublist.subset (by simp))],hf⟩
      · exact ⟨hpal,a,b,by rwa [he a (hf.sublist.subset (by simp))],
          by rwa [he b (hf.sublist.subset (by simp))],hf⟩
  simp only [markedInteriorDefect,hc,hi]

theorem ordered_all_marked_zero {α : Type} [DecidableEq α]
    (w : List α) (hw : (palindromicFactors w).length = w.length+1) :
    markedInteriorDefect (fun _ => true) w = 0 := by
  cases w with
  | nil => simp [markedInteriorDefect]
  | cons a w =>
    rcases List.eq_nil_or_concat w with he | ⟨t,b,he⟩
    · subst w
      simp [markedInteriorDefect]
    · subst w
      simp only [List.concat_eq_append] at hw ⊢
      rw [all_marked_interior_defect]
      have ht := full_palindrome_count_factor t (a :: (t ++ [b])) hw
        ((List.prefix_append t [b]).isInfix.trans (List.suffix_cons a (t ++ [b])).isInfix)
      simp [palindromeDefect,ht]

theorem ordered_unmarked_prefix_defect {α : Type} [DecidableEq α]
    (mark : α → Bool) (u v : List α) (hu : ∀ a ∈ u, mark a = false) :
    markedInteriorDefect mark (u ++ v) = markedInteriorDefect mark v := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha : mark a = false := hu a (by simp)
    have hrev := marked_interior_defect_reverse mark (a :: (u ++ v))
    have he := unmarked_append_interior_count mark (u ++ v).reverse a ha
    have hc : markedInteriorDefect mark (a :: (u ++ v)) =
        markedInteriorDefect mark (u ++ v) := by
      rw [← hrev]
      simp only [List.reverse_cons,markedInteriorDefect]
      rw [he,marked_interior_reverse_count]
      simp [ha,Nat.add_comm]
    simpa only [List.cons_append,hc] using ih (fun x hx => hu x (by simp [hx]))

theorem ordered_marked_interior_prefix_letters {α : Type} [DecidableEq α]
    (mark : α → Bool) (u p : List α) (b : α)
    (hp : p ∈ markedPalindromeInteriors mark (u ++ [b])) : p ⊆ u := by
  by_cases hold : p ∈ markedPalindromeInteriors mark u
  · obtain ⟨hpal,a,c,ha,hc,hf⟩ := (mem_markedPalindromeInteriors_iff mark p u).mp hold
    have hpf : Factor p (a :: (p ++ [c])) :=
      (List.prefix_append p [c]).isInfix.trans (List.suffix_cons a (p ++ [c])).isInfix
    exact (hpf.trans hf).sublist.subset
  · obtain ⟨_,_,a,_,hs⟩ := new_marked_interior_suffix mark p u b hp hold
    exact ((List.suffix_cons a p).trans hs).sublist.subset

theorem ordered_marked_endpoint_transport {α : Type} [DecidableEq α]
    (mark : α → Bool) (u p v : List α) (b c : α)
    (hc : mark c = true)
    (hp : p ∈ markedPalindromeInteriors mark (u ++ [b])) :
    p ∈ markedPalindromeInteriors mark (u ++ c :: v) := by
  by_cases hold : p ∈ markedPalindromeInteriors mark u
  · exact marked_interior_membership_append mark p u (c :: v) hold
  · obtain ⟨hpal,_,a,ha,hs⟩ := new_marked_interior_suffix mark p u b hp hold
    apply (mem_markedPalindromeInteriors_iff mark p (u ++ c :: v)).mpr
    refine ⟨hpal,a,c,ha,hc,?_⟩
    obtain ⟨s,he⟩ := hs
    exact ⟨s,v,by simp [← he,List.append_assoc]⟩

theorem ordered_full_guard_interiors {α : Type} [DecidableEq α]
    (mark : α → Bool) (s t p : List α) (b c : α)
    (hb : mark b = true) (hv : ∀ a ∈ t ++ [c], mark a = true)
    (hp : p ∈ palindromicFactors t) :
    p ∈ markedPalindromeInteriors mark ((s ++ [b]) ++ (t ++ [c])) := by
  obtain ⟨hf,hpal⟩ := (mem_palindromicFactors_iff p t).mp hp
  obtain ⟨a,d,had⟩ := factor_has_wrapped_extension p t b c hf
  have hall : ∀ x ∈ b :: (t ++ [c]), mark x = true := by
    intro x hx
    rcases List.mem_cons.mp hx with he | hm
    · simpa [he] using hb
    · exact hv x hm
  have ha : mark a = true := hall a (had.sublist.subset (by simp))
  have hd : mark d = true := hall d (had.sublist.subset (by simp))
  apply (mem_markedPalindromeInteriors_iff mark p _).mpr
  refine ⟨hpal,a,d,ha,hd,?_⟩
  have hs : Factor (b :: (t ++ [c])) ((s ++ [b]) ++ (t ++ [c])) := by
    exact ⟨s,[],by simp [List.append_assoc]⟩
  exact had.trans hs

theorem ordered_disjoint_rich_append {α : Type} [DecidableEq α]
    (u v : List α)
    (hu : (palindromicFactors u).length = u.length+1)
    (hv : (palindromicFactors v).length = v.length+1)
    (hd : ∀ a ∈ u, a ∉ v) :
    (palindromicFactors (u ++ v)).length = (u ++ v).length+1 := by
  let left := palindromicFactors u
  let right := (palindromicFactors v).erase []
  have hleft : left.Nodup := palindromicFactors_nodup u
  have hright : right.Nodup := List.erase_sublist.nodup (palindromicFactors_nodup v)
  have hn : (left ++ right).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hleft,hright,?_⟩
    intro p hp q hq heq
    subst q
    have hq' := (palindromicFactors_nodup v).mem_erase_iff.mp hq
    have hpu := (mem_palindromicFactors_iff p u).mp hp
    have hpv := (mem_palindromicFactors_iff p v).mp hq'.2
    cases p with
    | nil => exact hq'.1 rfl
    | cons a p => exact hd a (hpu.1.sublist.subset (by simp)) (hpv.1.sublist.subset (by simp))
  have hs : left ++ right ⊆ palindromicFactors (u ++ v) := by
    intro p hp
    rcases List.mem_append.mp hp with hl | hr
    · exact palindrome_membership_append p u v hl
    · have hpr := (mem_palindromicFactors_iff p v).mp (List.mem_of_mem_erase hr)
      apply (mem_palindromicFactors_iff p (u ++ v)).mpr
      exact ⟨hpr.1.trans (List.suffix_append u v).isInfix,hpr.2⟩
  have he : [] ∈ palindromicFactors v :=
    (mem_palindromicFactors_iff [] v).mpr ⟨by simp [Factor],by simp [Palindrome]⟩
  have hrlen : right.length = v.length := by
    dsimp [right]
    rw [List.length_erase_of_mem he,hv]
    omega
  have hlo := nodup_subset_length_le _ _ hn hs
  have hhi := palindromic_factor_count_bound (u ++ v)
  change (left ++ right).length ≤ _ at hlo
  simp only [List.length_append,hrlen] at hlo hhi ⊢
  have hllen : left.length = u.length+1 := hu
  omega

/-- A fully marked rich suffix can replace the final marked test endpoint,
provided its alphabet is disjoint and the left word ends at a marked letter. -/
theorem ordered_marked_rich_suffix_glue {α : Type} [DecidableEq α]
    (mark : α → Bool) (s v : List α) (b : α)
    (hne : v ≠ []) (hb : mark b = true)
    (hvmark : ∀ a ∈ v, mark a = true)
    (hdis : ∀ a ∈ s ++ [b], a ∉ v)
    (hv : (palindromicFactors v).length = v.length+1)
    (hu : markedInteriorDefect mark ((s ++ [b]) ++ [b]) = 0) :
    markedInteriorDefect mark ((s ++ [b]) ++ v) = 0 := by
  obtain ⟨t,c,hvc⟩ := List.eq_nil_or_concat v |>.resolve_left hne
  subst v
  simp only [List.concat_eq_append] at hvmark hdis hv ⊢
  have ht : (palindromicFactors t).length = t.length+1 :=
    full_palindrome_count_prefix t [c] hv
  let u := s ++ [b]
  let left := markedPalindromeInteriors mark (u ++ [b])
  let right := (palindromicFactors t).erase []
  have hleft : left.Nodup := markedPalindromeInteriors_nodup mark (u ++ [b])
  have hright : right.Nodup := List.erase_sublist.nodup (palindromicFactors_nodup t)
  have hn : (left ++ right).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hleft,hright,?_⟩
    intro p hp q hq heq
    subst q
    have hq' := (palindromicFactors_nodup t).mem_erase_iff.mp hq
    have hpu := ordered_marked_interior_prefix_letters mark u p b hp
    have hpv := (mem_palindromicFactors_iff p t).mp hq'.2
    cases p with
    | nil => exact hq'.1 rfl
    | cons a p =>
      exact hdis a (hpu (by simp)) (List.mem_append_left _ (hpv.1.sublist.subset (by simp)))
  have hs : left ++ right ⊆ markedPalindromeInteriors mark (u ++ (t ++ [c])) := by
    intro p hp
    rcases List.mem_append.mp hp with hl | hr
    · cases t with
      | nil =>
        exact ordered_marked_endpoint_transport mark u p [] b c (hvmark c (by simp)) hl
      | cons a t =>
        exact ordered_marked_endpoint_transport mark u p (t ++ [c]) b a
          (hvmark a (by simp)) hl
    · exact ordered_full_guard_interiors mark s t p b c hb hvmark (List.mem_of_mem_erase hr)
  have he : [] ∈ palindromicFactors t :=
    (mem_palindromicFactors_iff [] t).mpr ⟨by simp [Factor],by simp [Palindrome]⟩
  have hrlen : right.length = t.length := by
    dsimp [right]
    rw [List.length_erase_of_mem he,ht]
    omega
  have hllen : left.length = u.countP mark := by
    have heq := marked_interior_defect_add_count mark (u ++ [b])
    change markedInteriorDefect mark (u ++ [b]) = 0 at hu
    simp only [List.countP_append,List.countP_singleton,hb,ite_true,hu,Nat.zero_add] at heq
    simpa only [Nat.add_sub_cancel] using heq
  have hvcount : (t ++ [c]).countP mark = (t ++ [c]).length :=
    List.countP_eq_length.mpr hvmark
  have hlo := nodup_subset_length_le _ _ hn hs
  have hbudget := marked_interior_defect_add_count mark (u ++ (t ++ [c]))
  have hupos : 0 < u.countP mark := by
    dsimp [u]
    simp only [List.countP_append,List.countP_singleton,hb,ite_true]
    omega
  change (left ++ right).length ≤ _ at hlo
  simp only [List.length_append,hllen,hrlen] at hlo
  simp only [List.countP_append,hvcount,List.length_append,List.length_singleton] at hbudget
  change markedInteriorDefect mark (u ++ (t ++ [c])) = 0
  omega

theorem ordered_pair_label_injective (lo : Nat) : Function.Injective (orderedPairLabel lo) := by
  intro a b he
  cases a <;> cases b <;> simp_all [orderedPairLabel]

theorem ordered_pair_label_bounds (lo : Nat) (w : Word) (a : Nat)
    (ha : a ∈ w.map (orderedPairLabel lo)) : a=lo ∨ a=lo+1 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  cases b <;> simp [orderedPairLabel]

theorem ordered_pair_gaps_lower (lo : Nat) (ws : List Word) :
    ∀ a ∈ orderedPairGaps lo ws, lo ≤ a := by
  induction ws generalizing lo with
  | nil => simp [orderedPairGaps]
  | cons w ws ih =>
    intro a ha
    rcases List.mem_append.mp ha with hb | hv
    · rcases ordered_pair_label_bounds lo w a hb with he | he <;> omega
    · have hl := ih (lo+2) a hv
      omega

theorem ordered_pair_chain_full_and_thresholds (lo : Nat) (ws : List Word)
    (hw : ∀ w ∈ ws, (∃ s, w=s ++ [true]) ∧ Rich (w ++ [true])) :
    (palindromicFactors (orderedPairGaps lo ws)).length = (orderedPairGaps lo ws).length+1 ∧
    ∀ h, markedInteriorDefect (fun a => decide (h≤a)) (orderedPairGaps lo ws) = 0 := by
  induction ws generalizing lo with
  | nil =>
    simp [orderedPairGaps,palindromicFactors,factorOccurrences,Palindrome,
      markedInteriorDefect,List.eraseDups_cons]
  | cons w ws ih =>
    obtain ⟨⟨s,hs⟩,hwrich⟩ := hw w (by simp)
    have hv := ih (lo+2) (fun z hz => hw z (by simp [hz]))
    let u := w.map (orderedPairLabel lo)
    let v := orderedPairGaps (lo+2) ws
    have huend : u = s.map (orderedPairLabel lo) ++ [lo+1] := by
      simp [u,hs,orderedPairLabel]
    have hupad : (palindromicFactors (u ++ [lo+1])).length = (u ++ [lo+1]).length+1 := by
      have hm := palindromic_count_injective_map (orderedPairLabel lo)
        (ordered_pair_label_injective lo) (w ++ [true])
      simpa [u,orderedPairLabel,Rich] using hm.trans hwrich
    have hurich : (palindromicFactors u).length = u.length+1 :=
      full_palindrome_count_prefix u [lo+1] hupad
    have hdis : ∀ a ∈ u, a ∉ v := by
      intro a ha hav
      have hb := ordered_pair_label_bounds lo w a ha
      have hc := ordered_pair_gaps_lower (lo+2) ws a hav
      omega
    have hfull : (palindromicFactors (u ++ v)).length = (u ++ v).length+1 :=
      ordered_disjoint_rich_append u v hurich hv.1 hdis
    change _ ∧ ∀ h, markedInteriorDefect (fun a => decide (h≤a)) (u ++ v) = 0
    refine ⟨hfull,?_⟩
    intro h
    by_cases hlow : h≤lo
    · rw [ordered_marked_congr (fun a => decide (h≤a)) (fun _ => true) (u ++ v) (by
        intro a ha
        have hl : lo≤a := ordered_pair_gaps_lower lo (w :: ws) a ha
        simp [show h≤a by omega])]
      exact ordered_all_marked_zero (u ++ v) hfull
    · by_cases hmid : h=lo+1
      · subst h
        have hbase : markedInteriorDefect (fun a => decide (lo+1≤a)) (u ++ [lo+1]) = 0 := by
          rw [ordered_marked_congr (fun a => decide (lo+1≤a))
            (fun a => decide (a=lo+1)) (u ++ [lo+1]) (by
              intro a ha
              have hb : a=lo ∨ a=lo+1 := by
                rcases List.mem_append.mp ha with ha | ha
                · exact ordered_pair_label_bounds lo w a ha
                · exact Or.inr (by simpa using ha)
              rcases hb with rfl | rfl <;> simp)]
          exact ordered_singleton_marked_zero (lo+1) (u ++ [lo+1]) hupad
        by_cases hnil : v=[]
        · rw [hnil,List.append_nil]
          exact marked_interior_zero_factor (fun a => decide (lo+1≤a)) u (u ++ [lo+1])
            (List.prefix_append u [lo+1]).isInfix hbase
        · have hg := ordered_marked_rich_suffix_glue (fun a => decide (lo+1≤a))
            (s.map (orderedPairLabel lo)) v (lo+1) hnil (by simp)
            (by intro a ha; have := ordered_pair_gaps_lower (lo+2) ws a ha; simp [show lo+1≤a by omega])
            (by simpa only [← huend] using hdis) hv.1
            (by simpa only [← huend] using hbase)
          simpa only [← huend] using hg
      · rw [ordered_unmarked_prefix_defect (fun a => decide (h≤a)) u v (by
          intro a ha
          have hb := ordered_pair_label_bounds lo w a ha
          simp [show ¬h≤a by omega])]
        exact hv.2 h

theorem ordered_pair_binary_expansion_rich (lo : Nat) (ws : List Word)
    (hw : ∀ w ∈ ws, (∃ s, w=s ++ [true]) ∧ Rich (w ++ [true])) :
    Rich (expandGaps false (orderedPairGaps lo ws)) := by
  have h := ordered_pair_chain_full_and_thresholds lo ws hw
  apply (rich_expansion_iff_threshold_defects false (orderedPairGaps lo ws)).mpr
  exact ⟨by simp [palindromeDefect,h.1],fun k _ _ => h.2 k⟩

end RichWords

#print axioms RichWords.ordered_marked_interior_prefix_letters
#print axioms RichWords.ordered_marked_endpoint_transport
#print axioms RichWords.ordered_full_guard_interiors
#print axioms RichWords.ordered_disjoint_rich_append
#print axioms RichWords.ordered_marked_rich_suffix_glue
#print axioms RichWords.ordered_singleton_marked_zero
#print axioms RichWords.ordered_marked_congr
#print axioms RichWords.ordered_all_marked_zero
#print axioms RichWords.ordered_unmarked_prefix_defect
#print axioms RichWords.ordered_pair_label_injective
#print axioms RichWords.ordered_pair_label_bounds
#print axioms RichWords.ordered_pair_gaps_lower
#print axioms RichWords.ordered_pair_chain_full_and_thresholds
#print axioms RichWords.ordered_pair_binary_expansion_rich
