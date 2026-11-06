import RichWords.FramedGapDefinitions
import RichWords.MarkedProofs
import RichWords.GapProofs
import RichWords.DefectCoordinateProofs

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem replicate_prefix_before_expansion (a : Bool) (k m : Nat) (ys : List Nat) :
    (List.replicate k (!a)).IsPrefix (List.replicate m (!a) ++ expandGaps a ys) ↔ k ≤ m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    cases m with
    | zero =>
      obtain ⟨v,hv⟩ := expandGaps_starts a ys
      cases a <;> simp [List.replicate_succ,hv]
    | succ m => simpa [List.replicate_succ] using ih m

theorem framed_prefix_strip (a : Bool) (i j m : Nat) (xs ys : List Nat) :
    (framedGaps a i xs j).IsPrefix (List.replicate m (!a) ++ expandGaps a ys) ↔
      i=m ∧ (expandGaps a xs ++ List.replicate j (!a)).IsPrefix (expandGaps a ys) := by
  obtain ⟨u,hu⟩ := expandGaps_starts a xs
  obtain ⟨v,hv⟩ := expandGaps_starts a ys
  simp only [framedGaps,hu,hv,List.append_assoc,List.cons_append]
  rw [gap_prefix_iff]
  simp

theorem right_padded_expansion_prefix (a : Bool) (k : Nat) (hk : 0<k)
    (xs ys : List Nat) :
    (expandGaps a xs ++ List.replicate k (!a)).IsPrefix (expandGaps a ys) ↔
      ∃ j, k≤j ∧ (xs ++ [j]).IsPrefix ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      constructor
      · intro h
        have hl := h.length_le
        simp [expandGaps] at hl
        omega
      · simp
    | cons y ys =>
      simp only [expandGaps,List.singleton_append,List.cons_prefix_cons,true_and,
        List.nil_append]
      rw [replicate_prefix_before_expansion]
      simp
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h
        have hl := h.length_le
        simp [expandGaps_length] at hl
        omega
      · simp
    | cons y ys =>
      change (a :: (List.replicate x (!a) ++ expandGaps a xs ++
        List.replicate k (!a))).IsPrefix
        (a :: (List.replicate y (!a) ++ expandGaps a ys)) ↔ _
      rw [List.cons_prefix_cons]
      simp only [true_and]
      change (framedGaps a x xs k).IsPrefix
        (List.replicate y (!a) ++ expandGaps a ys) ↔ _
      rw [framed_prefix_strip,ih]
      simp only [List.cons_append,List.cons_prefix_cons]
      constructor
      · rintro ⟨hxy,j,hkj,hp⟩
        exact ⟨j,hkj,hxy,hp⟩
      · rintro ⟨j,hkj,hxy,hp⟩
        exact ⟨hxy,j,hkj,hp⟩

theorem framed_not_prefix_at_separator (a : Bool) (i j : Nat) (xs : List Nat)
    (w : Word) (hi : 0<i) : ¬ (framedGaps a i xs j).IsPrefix (a :: w) := by
  cases i with
  | zero => omega
  | succ i => cases a <;> simp [framedGaps,List.replicate_succ]

theorem framed_infix_replicate (a : Bool) (i j m : Nat) (xs ys : List Nat)
    (hi : 0<i) :
    (framedGaps a i xs j).IsInfix (List.replicate m (!a) ++ expandGaps a ys) ↔
      (i≤m ∧ (expandGaps a xs ++ List.replicate j (!a)).IsPrefix (expandGaps a ys)) ∨
      (framedGaps a i xs j).IsInfix (expandGaps a ys) := by
  induction m with
  | zero => simp [show ¬i≤0 by omega]
  | succ m ih =>
    have hp := framed_prefix_strip a i j (m+1) xs ys
    simp only [List.replicate_succ,List.cons_append] at hp ⊢
    rw [List.infix_cons_iff,hp,ih]
    by_cases hpre : (expandGaps a xs ++ List.replicate j (!a)).IsPrefix (expandGaps a ys) <;>
      by_cases hf : (framedGaps a i xs j).IsInfix (expandGaps a ys) <;> simp_all <;> omega

theorem framed_infix_iff (a : Bool) (i j : Nat) (xs ys : List Nat)
    (hi : 0<i) (hj : 0<j) :
    Factor (framedGaps a i xs j) (expandGaps a ys) ↔
      ∃ l r, i≤l ∧ j≤r ∧ Factor (l :: (xs ++ [r])) ys := by
  induction ys with
  | nil =>
    constructor
    · intro h
      have hl := h.length_le
      simp [framedGaps,expandGaps_length] at hl
      omega
    · simp [Factor]
  | cons y ys ih =>
    change (framedGaps a i xs j).IsInfix
      (a :: (List.replicate y (!a) ++ expandGaps a ys)) ↔ _
    rw [List.infix_cons_iff]
    have hn := framed_not_prefix_at_separator a i j xs
      (List.replicate y (!a) ++ expandGaps a ys) hi
    simp only [hn,false_or]
    rw [framed_infix_replicate a i j y xs ys hi,right_padded_expansion_prefix a j hj]
    constructor
    · rintro (⟨hiy,r,hjr,hpre⟩ | hf)
      · refine ⟨y,r,hiy,hjr,?_⟩
        exact (List.cons_prefix_cons.mpr ⟨rfl,hpre⟩).isInfix
      · obtain ⟨l,r,hil,hjr,hf⟩ := ih.mp hf
        exact ⟨l,r,hil,hjr,hf.trans (List.suffix_cons y ys).isInfix⟩
    · rintro ⟨l,r,hil,hjr,hf⟩
      rcases List.infix_cons_iff.mp hf with hpre | htail
      · obtain ⟨hly,hrest⟩ := List.cons_prefix_cons.mp hpre
        subst l
        exact Or.inl ⟨hil,r,hjr,hrest⟩
      · exact Or.inr (ih.mpr ⟨l,r,hil,hjr,htail⟩)

theorem framedGaps_reverse (a : Bool) (i j : Nat) (xs : List Nat) :
    (framedGaps a i xs j).reverse = framedGaps a j xs.reverse i := by
  simp [framedGaps,List.reverse_append,expandGaps_reverse,List.append_assoc]

theorem framed_initial_padding_unique (a : Bool) (i j k l : Nat) (xs ys : List Nat)
    (h : framedGaps a i xs j = framedGaps a k ys l) : i=k := by
  obtain ⟨u,hu⟩ := expandGaps_starts a xs
  obtain ⟨v,hv⟩ := expandGaps_starts a ys
  simp only [framedGaps,hu,hv,List.append_assoc,List.cons_append] at h
  exact (gap_prefix_unique a i k (u ++ List.replicate j (!a))
    (v ++ List.replicate l (!a)) h).1

theorem framedGaps_eq_iff (a : Bool) (i j k l : Nat) (xs ys : List Nat) :
    framedGaps a i xs j = framedGaps a k ys l ↔ i=k ∧ xs=ys ∧ j=l := by
  constructor
  · intro h
    have hik := framed_initial_padding_unique a i j k l xs ys h
    have hr := congrArg List.reverse h
    rw [framedGaps_reverse,framedGaps_reverse] at hr
    have hjl := framed_initial_padding_unique a j i l k xs.reverse ys.reverse hr
    subst k
    subst l
    have he : expandGaps a xs = expandGaps a ys :=
      List.append_cancel_left (List.append_cancel_right h)
    exact ⟨rfl,expandGaps_injective a xs ys he,rfl⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

theorem framedGaps_palindrome_iff (a : Bool) (i j : Nat) (xs : List Nat) :
    Palindrome (framedGaps a i xs j) ↔ i=j ∧ Palindrome xs := by
  simp only [Palindrome,framedGaps_reverse,framedGaps_eq_iff]
  constructor
  · rintro ⟨hji,hx,_⟩
    exact ⟨hji.symm,hx⟩
  · rintro ⟨hij,hx⟩
    exact ⟨hij.symm,hx,hij⟩

theorem framed_palindrome_membership_iff (a : Bool) (h : Nat) (xs ys : List Nat)
    (hh : 0<h) :
    framedGaps a h xs h ∈ palindromicFactors (expandGaps a ys) ↔
      xs ∈ markedPalindromeInteriors (fun k => decide (h≤k)) ys := by
  rw [mem_palindromicFactors_iff,framed_infix_iff a h h xs ys hh hh,
    framedGaps_palindrome_iff,mem_markedPalindromeInteriors_iff]
  simp only [true_and,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l,r,hl,hr,hf⟩,hp⟩
    exact ⟨hp,l,r,hl,hr,hf⟩
  · rintro ⟨hp,l,r,hl,hr,hf⟩
    exact ⟨⟨l,r,hl,hr,hf⟩,hp⟩

theorem mixed_palindrome_framed_iff (a : Bool) (p : Word) (ys : List Nat) :
    (p ∈ palindromicFactors (expandGaps a ys) ∧ a ∈ p ∧ ∃ u, p=(!a)::u) ↔
      ∃ h xs, 0<h ∧ p=framedGaps a h xs h ∧
        xs ∈ markedPalindromeInteriors (fun k => decide (h≤k)) ys := by
  constructor
  · rintro ⟨hp,ha,u,hu⟩
    obtain ⟨i,j,hform⟩ := gap_normal_form_of_mem a p ha
    change p = framedGaps a i (letterGaps a p) j at hform
    have hpal := ((mem_palindromicFactors_iff p _).mp hp).2
    have hij := ((framedGaps_palindrome_iff a i j (letterGaps a p)).mp
      (by simpa [← hform] using hpal)).1
    subst j
    have hi : 0<i := by
      cases i with
      | zero =>
        obtain ⟨v,hv⟩ := expandGaps_starts a (letterGaps a p)
        have he : p = a :: v := by simpa [framedGaps,hv] using hform
        rw [hu] at he
        cases a <;> simp at he
      | succ i => omega
    exact ⟨i,letterGaps a p,hi,hform,
      (framed_palindrome_membership_iff a i (letterGaps a p) ys hi).mp (by simpa [← hform] using hp)⟩
  · rintro ⟨h,xs,hh,rfl,hxs⟩
    refine ⟨(framed_palindrome_membership_iff a h xs ys hh).mpr hxs,?_,?_⟩
    · obtain ⟨u,hu⟩ := expandGaps_starts a xs
      simp [framedGaps,hu]
    · cases h with
      | zero => omega
      | succ h =>
        refine ⟨List.replicate h (!a) ++ expandGaps a xs ++ List.replicate (h+1) (!a),?_⟩
        simp [framedGaps,List.replicate_succ]

theorem mem_le_gapMaximum (ys : List Nat) (k : Nat) (hk : k∈ys) : k≤gapMaximum ys := by
  induction ys with
  | nil => simp at hk
  | cons y ys ih =>
    simp only [List.mem_cons] at hk
    simp only [gapMaximum,List.foldr_cons]
    rcases hk with rfl | hk
    · exact Nat.le_max_left _ _
    · have h := ih hk
      unfold gapMaximum at h
      exact Nat.le_trans h (Nat.le_max_right _ _)

theorem threshold_marked_nonempty (ys xs : List Nat) (h : Nat)
    (hx : xs ∈ markedPalindromeInteriors (fun k => decide (h≤k)) ys) : h≤gapMaximum ys := by
  obtain ⟨_,l,r,hl,_,hf⟩ := (mem_markedPalindromeInteriors_iff _ xs ys).mp hx
  have hmem : l∈ys := hf.sublist.subset (by simp)
  have hle := mem_le_gapMaximum ys l hmem
  have hl' : h≤l := of_decide_eq_true hl
  omega

theorem unary_infix_replicate (a : Bool) (k m : Nat) (ys : List Nat) :
    (List.replicate k (!a)).IsInfix (List.replicate m (!a) ++ expandGaps a ys) ↔
      k≤m ∨ (List.replicate k (!a)).IsInfix (expandGaps a ys) := by
  induction m with
  | zero => cases k <;> simp
  | succ m ih =>
    have hp := replicate_prefix_before_expansion a k (m+1) ys
    simp only [List.replicate_succ,List.cons_append] at hp ⊢
    rw [List.infix_cons_iff,hp,ih]
    by_cases hf : (List.replicate k (!a)).IsInfix (expandGaps a ys) <;> simp_all <;> omega

theorem unary_expansion_infix_iff (a : Bool) (k : Nat) (ys : List Nat) :
    Factor (List.replicate k (!a)) (expandGaps a ys) ↔ k≤gapMaximum ys := by
  cases k with
  | zero => simp [Factor]
  | succ k =>
    induction ys with
    | nil => cases a <;> simp [expandGaps,gapMaximum,Factor,List.replicate_succ,List.infix_cons_iff]
    | cons y ys ih =>
      change (List.replicate (k+1) (!a)).IsInfix
        (a :: (List.replicate y (!a) ++ expandGaps a ys)) ↔ _
      rw [List.infix_cons_iff]
      have hn : ¬(List.replicate (k+1) (!a)).IsPrefix
          (a :: (List.replicate y (!a) ++ expandGaps a ys)) := by
        cases a <;> simp [List.replicate_succ]
      simp only [hn,false_or]
      rw [unary_infix_replicate]
      change k+1≤y ∨ Factor (List.replicate (k+1) (!a)) (expandGaps a ys) ↔ _
      rw [ih]
      change k+1≤y ∨ k+1≤gapMaximum ys ↔ k+1≤Nat.max y (gapMaximum ys)
      simp only [Nat.max_def]
      split <;> omega

theorem framedGapPalImage_nodup (a : Bool) (h : Nat) (ys : List Nat) :
    (framedGapPalImage a h ys).Nodup := by
  simp only [framedGapPalImage,List.Nodup,List.pairwise_map]
  apply (markedPalindromeInteriors_nodup (fun k => decide (h≤k)) ys).imp
  intro xs zs hne he
  exact hne ((framedGaps_eq_iff a h h h h xs zs).mp he).2.1

theorem mixedGapPalindromes_nodup (a : Bool) (ys : List Nat) :
    (mixedGapPalindromes a ys).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact framedGapPalImage_nodup a (i+1) ys
  · apply (List.nodup_range (n := gapMaximum ys)).imp
    intro i j hij p hp q hq he
    obtain ⟨xs,_,hxp⟩ := List.mem_map.mp hp
    obtain ⟨zs,_,hzq⟩ := List.mem_map.mp hq
    have hframes : framedGaps a (i+1) xs (i+1) = framedGaps a (j+1) zs (j+1) :=
      hxp.trans (he.trans hzq.symm)
    have heq := (framedGaps_eq_iff a (i+1) (i+1) (j+1) (j+1) xs zs).mp hframes
    exact hij (by omega)

theorem mem_mixedGapPalindromes_iff (a : Bool) (ys : List Nat) (p : Word) :
    p ∈ mixedGapPalindromes a ys ↔
      p ∈ palindromicFactors (expandGaps a ys) ∧ a∈p ∧ ∃ u, p=(!a)::u := by
  rw [mixed_palindrome_framed_iff]
  constructor
  · intro hp
    obtain ⟨i,hi,himage⟩ := List.mem_flatMap.mp hp
    obtain ⟨xs,hxs,hxp⟩ := List.mem_map.mp himage
    exact ⟨i+1,xs,by omega,hxp.symm,hxs⟩
  · rintro ⟨h,xs,hh,rfl,hxs⟩
    have hb := threshold_marked_nonempty ys xs h hxs
    have he : h-1+1=h := by omega
    apply List.mem_flatMap.mpr
    refine ⟨h-1,List.mem_range.mpr (by omega),?_⟩
    rw [he]
    exact List.mem_map.mpr ⟨xs,hxs,rfl⟩

theorem unaryGapPalindromes_nodup (a : Bool) (ys : List Nat) :
    (unaryGapPalindromes a ys).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.nodup_range (n := gapMaximum ys)).imp
  intro i j hij he
  have hl := congrArg List.length he
  simp only [List.length_replicate] at hl
  exact hij (by omega)

theorem mem_unaryGapPalindromes_iff (a : Bool) (ys : List Nat) (p : Word) :
    p ∈ unaryGapPalindromes a ys ↔ ∃ k, 0<k ∧ k≤gapMaximum ys ∧ p=List.replicate k (!a) := by
  constructor
  · intro hp
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hp
    have hi' := List.mem_range.mp hi
    exact ⟨i+1,by omega,by omega,he.symm⟩
  · rintro ⟨k,hk,hb,rfl⟩
    refine List.mem_map.mpr ⟨k-1,List.mem_range.mpr (by omega),?_⟩
    have he : k-1+1=k := by omega
    simp [he]

theorem unaryGapPalindromes_avoid_separator (a : Bool) (ys : List Nat) (p : Word)
    (hp : p ∈ unaryGapPalindromes a ys) : a∉p ∧ p≠[] := by
  obtain ⟨k,hk,_,rfl⟩ := (mem_unaryGapPalindromes_iff a ys p).mp hp
  constructor
  · cases a <;> simp
  · intro he
    have hl := congrArg List.length he
    simp only [List.length_replicate,List.length_nil] at hl
    omega

theorem expansion_palindrome_image_nodup (a : Bool) (ys : List Nat) :
    ((palindromicFactors ys).map (expandGaps a)).Nodup := by
  simpa only [List.Nodup,List.pairwise_map,ne_eq,expandGaps_eq_iff] using
    palindromicFactors_nodup ys

theorem thresholdPalCover_nodup (a : Bool) (ys : List Nat) :
    (thresholdPalCover a ys).Nodup := by
  simp only [thresholdPalCover,List.append_assoc]
  apply List.nodup_cons.mpr
  constructor
  · intro hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨xs,_,he⟩ := List.mem_map.mp hp
      obtain ⟨u,hu⟩ := expandGaps_starts a xs
      simp [hu] at he
    · rcases List.mem_append.mp hp with hp | hp
      · exact (unaryGapPalindromes_avoid_separator a ys [] hp).2 rfl
      · have h := ((mem_mixedGapPalindromes_iff a ys []).mp hp).2.1
        simp at h
  · apply List.nodup_append.mpr
    refine ⟨expansion_palindrome_image_nodup a ys,?_,?_⟩
    · apply List.nodup_append.mpr
      refine ⟨unaryGapPalindromes_nodup a ys,mixedGapPalindromes_nodup a ys,?_⟩
      intro p hp q hq he
      have hn := (unaryGapPalindromes_avoid_separator a ys p hp).1
      have hm := ((mem_mixedGapPalindromes_iff a ys q).mp hq).2.1
      exact hn (by simpa [he] using hm)
    · intro p hp q hq he
      obtain ⟨xs,_,hxp⟩ := List.mem_map.mp hp
      obtain ⟨u,hu⟩ := expandGaps_starts a xs
      rcases List.mem_append.mp hq with hq | hq
      · have hn := (unaryGapPalindromes_avoid_separator a ys q hq).1
        apply hn
        rw [← he,← hxp,hu]
        simp
      · obtain ⟨v,hv⟩ := ((mem_mixedGapPalindromes_iff a ys q).mp hq).2.2
        have hab : a::u = (!a)::v := hu.symm.trans (hxp.trans (he.trans hv))
        cases a <;> simp at hab

theorem no_separator_eq_replicate (a : Bool) (p : Word) (ha : a∉p) :
    ∃ k, p=List.replicate k (!a) := by
  rcases binary_gap_normal_form a p with h | ⟨i,xs,j,h⟩
  · exact h
  · obtain ⟨u,hu⟩ := expandGaps_starts a xs
    simp [h,hu] at ha

theorem mem_thresholdPalCover_iff (a : Bool) (ys : List Nat) (p : Word) :
    p ∈ thresholdPalCover a ys ↔ p ∈ palindromicFactors (expandGaps a ys) := by
  simp only [thresholdPalCover,List.mem_cons,List.mem_append]
  constructor
  · rintro (rfl | ((hp | hp) | hp))
    · simp [mem_palindromicFactors_iff,Factor,Palindrome]
    · obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hp
      obtain ⟨hf,hpal⟩ := (mem_palindromicFactors_iff xs ys).mp hxs
      exact (mem_palindromicFactors_iff _ _).mpr
        ⟨(expandGaps_infix_iff a xs ys).mpr hf,(expandGaps_palindrome_iff a xs).mpr hpal⟩
    · obtain ⟨k,_,hb,rfl⟩ := (mem_unaryGapPalindromes_iff a ys p).mp hp
      exact (mem_palindromicFactors_iff _ _).mpr
        ⟨(unary_expansion_infix_iff a k ys).mpr hb,by simp [Palindrome]⟩
    · exact ((mem_mixedGapPalindromes_iff a ys p).mp hp).1
  · intro hp
    cases p with
    | nil => exact Or.inl rfl
    | cons b u =>
      apply Or.inr
      by_cases he : b=a
      · subst b
        obtain ⟨xs,hx⟩ := palindrome_gap_expansion a u
          ((mem_palindromicFactors_iff _ _).mp hp).2
        apply Or.inl
        apply Or.inl
        apply List.mem_map.mpr
        refine ⟨xs,?_,hx.symm⟩
        obtain ⟨hf,hpal⟩ := (mem_palindromicFactors_iff _ _).mp hp
        rw [hx] at hf hpal
        exact (mem_palindromicFactors_iff xs ys).mpr
          ⟨(expandGaps_infix_iff a xs ys).mp hf,(expandGaps_palindrome_iff a xs).mp hpal⟩
      · have hb : b=(!a) := by cases a <;> cases b <;> simp_all
        by_cases ha : a∈b::u
        · exact Or.inr ((mem_mixedGapPalindromes_iff a ys (b::u)).mpr
            ⟨hp,ha,u,by rw [hb]⟩)
        · obtain ⟨k,hk⟩ := no_separator_eq_replicate a (b::u) ha
          have hpos : 0<k := by
            have hl := congrArg List.length hk
            simp only [List.length_cons,List.length_replicate] at hl
            omega
          have hf := ((mem_palindromicFactors_iff _ _).mp hp).1
          rw [hk] at hf
          exact Or.inl (Or.inr ((mem_unaryGapPalindromes_iff a ys (b::u)).mpr
            ⟨k,hpos,(unary_expansion_infix_iff a k ys).mp hf,hk⟩))

theorem threshold_palindrome_count (a : Bool) (ys : List Nat) :
    (palindromicFactors (expandGaps a ys)).length = 1 + (palindromicFactors ys).length +
      gapMaximum ys + ((List.range (gapMaximum ys)).map
        (fun i => (markedPalindromeInteriors (fun k => decide (i+1≤k)) ys).length)).sum := by
  have he := nodup_same_members_length (palindromicFactors (expandGaps a ys))
    (thresholdPalCover a ys) (palindromicFactors_nodup _) (thresholdPalCover_nodup a ys)
    (fun p => (mem_thresholdPalCover_iff a ys p).symm)
  rw [he]
  simp [thresholdPalCover,unaryGapPalindromes,mixedGapPalindromes,
    framedGapPalImage,List.length_flatMap]
  omega

theorem threshold_indicator_sum (N k : Nat) :
    ((List.range N).map (fun i => if i+1≤k then 1 else 0)).sum = min N k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,ih]
    by_cases h : N+1≤k
    · simp only [h,↓reduceIte,Nat.min_def]
      split <;> omega
    · simp only [h,↓reduceIte,Nat.min_def]
      split <;> omega

theorem threshold_count_sum (ys : List Nat) (N : Nat)
    (hb : ∀ k∈ys, k≤N) :
    ((List.range N).map (fun i => ys.countP (fun k => decide (i+1≤k)))).sum = ys.sum := by
  induction ys with
  | nil => simp [sum_map_zero_nat]
  | cons k ys ih =>
    have hk := hb k (by simp)
    have ht := ih (fun j hj => hb j (by simp [hj]))
    have he : (fun i => (k::ys).countP (fun j => decide (i+1≤j))) =
        (fun i => (if i+1≤k then 1 else 0) + ys.countP (fun j => decide (i+1≤j))) := by
      funext i
      simp [List.countP_cons,Nat.add_comm]
    rw [he,sum_map_add_nat,threshold_indicator_sum,ht]
    simp [Nat.min_eq_right hk]

theorem threshold_count_positive (ys : List Nat) (h : Nat)
    (hh : 0<h) (hb : h≤gapMaximum ys) :
    0 < ys.countP (fun k => decide (h≤k)) := by
  induction ys with
  | nil => simp [gapMaximum] at hb; omega
  | cons k ys ih =>
    by_cases hk : h≤k
    · simp [hk]
    · have ht : h≤gapMaximum ys := by
        change h≤max k (gapMaximum ys) at hb
        rw [Nat.max_def] at hb
        split at hb <;> omega
      have hp := ih ht
      simp [hk,hp]

theorem sum_map_one_nat {α : Type} (s : List α) :
    (s.map (fun _ => (1 : Nat))).sum = s.length := by
  induction s <;> simp_all <;> omega

theorem threshold_defect_budget (ys : List Nat) :
    thresholdDefectSum ys + ((List.range (gapMaximum ys)).map
      (fun i => (markedPalindromeInteriors (fun k => decide (i+1≤k)) ys).length)).sum +
      gapMaximum ys = ys.sum := by
  have he : (List.range (gapMaximum ys)).map
      (fun i => markedInteriorDefect (fun k => decide (i+1≤k)) ys +
        (markedPalindromeInteriors (fun k => decide (i+1≤k)) ys).length + 1) =
      (List.range (gapMaximum ys)).map
        (fun i => ys.countP (fun k => decide (i+1≤k))) := by
    apply List.map_congr_left
    intro i hi
    have hp := threshold_count_positive ys (i+1) (by omega)
      (by have := List.mem_range.mp hi; omega)
    have hd := marked_interior_defect_add_count (fun k => decide (i+1≤k)) ys
    omega
  have hs := congrArg List.sum he
  rw [sum_map_add_nat,sum_map_add_nat,sum_map_one_nat,List.length_range,
    threshold_count_sum ys (gapMaximum ys) (mem_le_gapMaximum ys)] at hs
  exact hs

theorem threshold_gap_defect_identity (a : Bool) (ys : List Nat) :
    palindromeDefect (expandGaps a ys) = palindromeDefect ys + thresholdDefectSum ys := by
  have hp := threshold_palindrome_count a ys
  have hl := expandGaps_length a ys
  have hb := threshold_defect_budget ys
  have hy := palindromic_factor_count_bound ys
  unfold palindromeDefect
  omega

theorem opposite_gap_threshold_defect (a : Bool) (ys : List Nat) :
    palindromeDefect (letterGaps (!a) (expandGaps a ys)) = thresholdDefectSum ys := by
  have he := threshold_gap_defect_identity a ys
  have hg := binary_gap_defect_identity (expandGaps a ys)
  have ho : letterGaps a (expandGaps a ys) = ys := by
    simpa using letterGaps_expansion a ys 0
  cases a <;> simp only [Bool.not_false,Bool.not_true,ho] at * <;> omega

theorem thresholdDefectSum_zero_iff (ys : List Nat) :
    thresholdDefectSum ys = 0 ↔
      ∀ h, 0<h → h≤gapMaximum ys → markedInteriorDefect (fun k => decide (h≤k)) ys = 0 := by
  unfold thresholdDefectSum
  rw [List.sum_eq_zero_iff_forall_eq_nat]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
  constructor
  · intro hz h hh hb
    have he : h-1+1=h := by omega
    have hm : h-1∈List.range (gapMaximum ys) := List.mem_range.mpr (by omega)
    simpa only [he] using hz (h-1) hm
  · intro hz i hi
    exact hz (i+1) (by omega) (by have := List.mem_range.mp hi; omega)

theorem rich_expansion_iff_threshold_defects (a : Bool) (ys : List Nat) :
    Rich (expandGaps a ys) ↔ palindromeDefect ys = 0 ∧
      ∀ h, 0<h → h≤gapMaximum ys → markedInteriorDefect (fun k => decide (h≤k)) ys = 0 := by
  rw [←thresholdDefectSum_zero_iff]
  have hb := palindromic_factor_count_bound (expandGaps a ys)
  have he := threshold_gap_defect_identity a ys
  unfold Rich
  unfold palindromeDefect at he ⊢
  omega

end RichWords

#print axioms RichWords.replicate_prefix_before_expansion
#print axioms RichWords.framed_prefix_strip
#print axioms RichWords.right_padded_expansion_prefix
#print axioms RichWords.framed_not_prefix_at_separator
#print axioms RichWords.framed_infix_replicate
#print axioms RichWords.framed_infix_iff
#print axioms RichWords.framedGaps_reverse
#print axioms RichWords.framed_initial_padding_unique
#print axioms RichWords.framedGaps_eq_iff
#print axioms RichWords.framedGaps_palindrome_iff
#print axioms RichWords.framed_palindrome_membership_iff
#print axioms RichWords.mixed_palindrome_framed_iff
#print axioms RichWords.mem_le_gapMaximum
#print axioms RichWords.threshold_marked_nonempty
#print axioms RichWords.unary_infix_replicate
#print axioms RichWords.unary_expansion_infix_iff
#print axioms RichWords.framedGapPalImage_nodup
#print axioms RichWords.mixedGapPalindromes_nodup
#print axioms RichWords.mem_mixedGapPalindromes_iff
#print axioms RichWords.unaryGapPalindromes_nodup
#print axioms RichWords.mem_unaryGapPalindromes_iff
#print axioms RichWords.unaryGapPalindromes_avoid_separator
#print axioms RichWords.expansion_palindrome_image_nodup
#print axioms RichWords.thresholdPalCover_nodup
#print axioms RichWords.no_separator_eq_replicate
#print axioms RichWords.mem_thresholdPalCover_iff
#print axioms RichWords.threshold_palindrome_count
#print axioms RichWords.threshold_indicator_sum
#print axioms RichWords.threshold_count_sum
#print axioms RichWords.threshold_count_positive
#print axioms RichWords.sum_map_one_nat
#print axioms RichWords.threshold_defect_budget
#print axioms RichWords.threshold_gap_defect_identity
#print axioms RichWords.opposite_gap_threshold_defect
#print axioms RichWords.thresholdDefectSum_zero_iff
#print axioms RichWords.rich_expansion_iff_threshold_defects
