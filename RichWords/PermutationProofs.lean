import RichWords.GapProofs
import RichWords.PermutationDefinitions

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem permCodeWord_palindrome (H : Nat) (p : List Nat) (c : PermPalCode) :
    Palindrome (permCodeWord H p c) := by
  apply (expandGaps_palindrome_iff _ _).mpr
  cases c <;> simp [permCodeTuple, List.reverse_append, List.append_assoc]

theorem permCodeWord_nonempty (H : Nat) (p : List Nat) (c : PermPalCode) :
    permCodeWord H p c ≠ [] := by
  obtain ⟨u, hu⟩ := expandGaps_starts (permCodeStart c) (permCodeTuple H p c)
  simp [permCodeWord, hu]

theorem perm_parameter_at (H : Nat) (p : List Nat)
    (hb : ∀ v ∈ p, 0 < v ∧ v < H) (i : Nat) (hi : i < p.length) :
    0 < p[i]! ∧ p[i]! < H := by
  apply hb
  rw [getElem!_pos p i hi]
  exact List.getElem_mem hi

theorem permCodeTuple_markers (H : Nat) (p : List Nat) (c : PermPalCode)
    (hH : 0 < H) (hb : ∀ v ∈ p, 0 < v ∧ v < H) (hc : permCodeValid H p c) :
    (permCodeTuple H p c).filter (· != 0) = permCodeMarkers H p c := by
  have hH0 : H ≠ 0 := by omega
  cases c with
  | zero t => simp [permCodeTuple, permCodeMarkers]
  | high t => simp [permCodeTuple, permCodeMarkers, hH0]
  | low i t =>
    have hi := (perm_parameter_at H p hb i hc.1).1
    have hv : p[i]! ≠ 0 := by omega
    simp only [List.getElem!_eq_getElem?_getD, Nat.default_eq_zero] at hv
    simp [permCodeTuple, permCodeMarkers, hv]
  | wide i t =>
    have hi := (perm_parameter_at H p hb i hc.1).1
    have hv : p[i]! ≠ 0 := by omega
    simp only [List.getElem!_eq_getElem?_getD, Nat.default_eq_zero] at hv
    simp [permCodeTuple, permCodeMarkers, hv, hH0]
  | one t => simp [permCodeTuple, permCodeMarkers]
  | short i t => simp [permCodeTuple, permCodeMarkers]
  | long i t => simp [permCodeTuple, permCodeMarkers]

theorem permCodeWord_eq_data (H : Nat) (p : List Nat) (c d : PermPalCode)
    (h : permCodeWord H p c = permCodeWord H p d) :
    permCodeStart c = permCodeStart d ∧ permCodeTuple H p c = permCodeTuple H p d := by
  obtain ⟨u, hu⟩ := expandGaps_starts (permCodeStart c) (permCodeTuple H p c)
  obtain ⟨v, hv⟩ := expandGaps_starts (permCodeStart d) (permCodeTuple H p d)
  have hs : permCodeStart c = permCodeStart d := by
    change expandGaps _ _ = expandGaps _ _ at h
    rw [hu, hv] at h
    exact (List.cons.inj h).1
  refine ⟨hs, ?_⟩
  apply expandGaps_injective (permCodeStart d)
  simpa only [permCodeWord, hs] using h

theorem permCodeWord_injective (H : Nat) (p : List Nat)
    (hH : 0 < H) (hn : p.Nodup) (hb : ∀ v ∈ p, 0 < v ∧ v < H)
    (c d : PermPalCode) (hc : permCodeValid H p c) (hd : permCodeValid H p d)
    (h : permCodeWord H p c = permCodeWord H p d) : c = d := by
  obtain ⟨hs, ht⟩ := permCodeWord_eq_data H p c d h
  have hm := congrArg (fun xs : List Nat => xs.filter (· != 0)) ht
  dsimp only at hm
  rw [permCodeTuple_markers H p c hH hb hc,
      permCodeTuple_markers H p d hH hb hd] at hm
  have hl := congrArg List.length ht
  have hbound (i : Nat) (hi : i < p.length) : p[i]! < H :=
    (perm_parameter_at H p hb i hi).2
  have hinj (i j : Nat) (hi : i < p.length) (hj : j < p.length)
      (he : p[i]! = p[j]!) : i = j := (List.getElem!_inj hi hj hn).mp he
  clear h ht
  cases c <;> cases d <;>
    simp only [permCodeStart, permCodeMarkers, permCodeValid,
      List.cons.injEq, List.cons_ne_nil, reduceCtorEq,
      true_and, and_true] at *
  all_goals try contradiction
  all_goals
    simp only [permCodeTuple, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil] at hl
    grind only

theorem expandGaps_zero_prefix (a : Bool) (t : Nat) (xs : List Nat) :
    expandGaps a (List.replicate t 0 ++ xs) = List.replicate t a ++ expandGaps a xs := by
  induction t with
  | zero => simp
  | succ t ih => simp [List.replicate_succ, expandGaps, ih]

theorem expandGaps_zeros (a : Bool) (t : Nat) :
    expandGaps a (List.replicate t 0) = List.replicate (t+1) a := by
  have h := expandGaps_zero_prefix a t []
  simpa [expandGaps, List.replicate_succ'] using h

theorem replicate_cons_join (a : Bool) (t : Nat) (xs : Word) :
    List.replicate t a ++ a :: xs = List.replicate (t+1) a ++ xs := by
  rw [List.replicate_succ', List.append_assoc]
  rfl

theorem permCodeWord_direct (H : Nat) (p : List Nat) (c : PermPalCode)
    (hb : ∀ v ∈ p, 0 < v ∧ v < H) (hc : permCodeValid H p c) :
    permCodeWord H p c = permDirectWord H p c := by
  have hp (i : Nat) (hi : i < p.length) : p[i]!-1+1 = p[i]! := by
    have hv := (perm_parameter_at H p hb i hi).1
    omega
  cases c <;>
    simp only [permCodeWord, permCodeStart, permCodeTuple, permDirectWord,
      List.append_assoc, expandGaps_zero_prefix, List.nil_append, expandGaps,
      Bool.not_false, Bool.not_true, expandGaps_zeros, List.cons_append,
      replicate_cons_join, List.append_assoc]
  case long i t => rw [hp i hc.1]

theorem permTail_prefix (H k : Nat) (p : List Nat) :
    (List.replicate k false).IsPrefix (permTail H k p) := by
  cases p with
  | nil => exact ⟨[], by simp [permTail]⟩
  | cons v vs =>
    refine ⟨[false] ++ List.replicate v true ++ List.replicate (k+1) false ++
      List.replicate H true ++ permTail H (k+1) vs, ?_⟩
    simp only [permTail, List.cons_append, List.nil_append, List.append_assoc, replicate_cons_join]

theorem permTail_length (H k : Nat) (p : List Nat) :
    (permTail H k p).length = k * (2*p.length+1) + p.length*p.length +
      2*p.length + p.sum + p.length*H := by
  induction p generalizing k with
  | nil => simp [permTail]
  | cons v vs ih =>
    simp only [permTail, List.length_append, List.length_replicate, ih,
      List.length_cons, List.sum_cons]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega

theorem permutationWord_length (H : Nat) (p : List Nat) :
    (permutationWord H p).length = (p.length+1)*(p.length+1) + (p.length+1)*H + p.sum := by
  simp only [permutationWord, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, permTail_length]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.zero_mul]
  omega

theorem middle_infix (l m r : Word) : m.IsInfix (l ++ m ++ r) := ⟨l, r, rfl⟩

theorem trim_runs_infix (a b : Bool) (x y l r : Nat) (m : Word)
    (hx : x ≤ l) (hy : y ≤ r) :
    (List.replicate x a ++ m ++ List.replicate y b).IsInfix
      (List.replicate l a ++ m ++ List.replicate r b) := by
  refine ⟨List.replicate (l-x) a, List.replicate (r-y) b, ?_⟩
  have hl : l-x+x = l := by omega
  have hr : y+(r-y) = r := by omega
  simp only [List.append_assoc]
  simp only [← List.append_assoc, List.replicate_append_replicate, hl, hr]

theorem permWindow_occurs (H L k : Nat) (p : List Nat) (i : Nat) (hi : i < p.length) :
    (permWindow H (if i=0 then L else k+i) (k+i) p[i]!).IsInfix
      (List.replicate L false ++ List.replicate H true ++ permTail H k p) := by
  induction p generalizing L k i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero =>
      obtain ⟨u, hu⟩ := permTail_prefix H (k+1) vs
      refine ⟨[], u, ?_⟩
      simp only [List.nil_append, Nat.add_zero, ↓reduceIte, List.getElem!_cons_zero,
        permWindow, permTail]
      rw [← hu]
      simp only [List.append_assoc]
    | succ i =>
      have hi' : i < vs.length := by simpa using hi
      obtain ⟨u, v', he⟩ := ih (k+1) (k+1) i hi'
      refine ⟨List.replicate L false ++ List.replicate H true ++
        List.replicate (k+1) false ++ List.replicate v true ++ u, v', ?_⟩
      have hc : (if i=0 then k+1 else k+1+i) = k+(i+1) := by split <;> omega
      simp only [Nat.succ_ne_zero, ↓reduceIte, List.getElem!_cons_succ]
      rw [show k+i.succ = k+1+i by omega]
      rw [hc] at he
      -- Reassociate the prefix so the induction equality applies.
      simpa only [permTail, List.append_assoc, hc,
        show k+1+i = k+(i+1) by omega] using
        congrArg (fun z => List.replicate L false ++ List.replicate H true ++
          List.replicate (k+1) false ++ List.replicate v true ++ z) he

theorem permutationWindow_occurs (H : Nat) (p : List Nat) (i : Nat) (hi : i < p.length) :
    (permWindow H (if i=0 then 1 else i) i p[i]!).IsInfix (permutationWord H p) := by
  simpa only [Nat.zero_add, List.replicate_one, permutationWord] using
    permWindow_occurs H 1 0 p i hi

theorem window_high_infix (H L k v : Nat) :
    (List.replicate (k+1) false ++ List.replicate H true ++ List.replicate (k+1) false).IsInfix
      (permWindow H L k v) := by
  refine ⟨List.replicate L false ++ List.replicate H true ++ List.replicate (k+1) false ++
    List.replicate v true, [], ?_⟩
  simp only [permWindow, List.append_nil, List.append_assoc]

theorem window_low_infix (H L k v : Nat) :
    (List.replicate (k+1) false ++ List.replicate v true ++ List.replicate (k+1) false).IsInfix
      (permWindow H L k v) := by
  refine ⟨List.replicate L false ++ List.replicate H true,
    List.replicate H true ++ List.replicate (k+1) false, ?_⟩
  simp only [permWindow, List.append_assoc]

theorem window_short_infix (H L k v : Nat) :
    (List.replicate H true ++ List.replicate (k+1) false ++ List.replicate v true).IsInfix
      (permWindow H L k v) := by
  refine ⟨List.replicate L false,
    List.replicate (k+1) false ++ List.replicate H true ++ List.replicate (k+1) false, ?_⟩
  simp only [permWindow, List.append_assoc]

theorem window_long_infix (H L k v : Nat) :
    (List.replicate H true ++ (List.replicate (k+1) false ++ List.replicate v true ++
      List.replicate (k+1) false) ++ List.replicate H true).IsInfix (permWindow H L k v) := by
  refine ⟨List.replicate L false, List.replicate (k+1) false, ?_⟩
  simp only [permWindow, List.append_assoc]

theorem permCodeWord_occurs (H : Nat) (p : List Nat) (hp : 0 < p.length)
    (hb : ∀ v ∈ p, 0 < v ∧ v < H) (c : PermPalCode) (hc : permCodeValid H p c) :
    (permCodeWord H p c).IsInfix (permutationWord H p) := by
  rw [permCodeWord_direct H p c hb hc]
  have hlast : p.length-1 < p.length := by omega
  have hj : p.length-1+1 = p.length := by omega
  have hhigh := (window_high_infix H (if p.length-1=0 then 1 else p.length-1)
    (p.length-1) p[p.length-1]!).trans (permutationWindow_occurs H p (p.length-1) hlast)
  rw [hj] at hhigh
  have hlow (i : Nat) (hi : i < p.length) :=
    (window_low_infix H (if i=0 then 1 else i) i p[i]!).trans (permutationWindow_occurs H p i hi)
  have hshort (i : Nat) (hi : i < p.length) :=
    (window_short_infix H (if i=0 then 1 else i) i p[i]!).trans (permutationWindow_occurs H p i hi)
  have hlong (i : Nat) (hi : i < p.length) :=
    (window_long_infix H (if i=0 then 1 else i) i p[i]!).trans (permutationWindow_occurs H p i hi)
  cases c with
  | zero t =>
    have ht : t+1 ≤ p.length := by exact hc
    have htrim := trim_runs_infix false false (t+1) 0 p.length 0 [] ht (by omega)
    simp only [List.replicate_zero, List.append_nil] at htrim
    exact htrim.trans ((List.prefix_append _ _).isInfix.trans
      (by simpa only [List.append_assoc] using hhigh))
  | high t =>
    exact (trim_runs_infix false false (t+1) (t+1) p.length p.length
      (List.replicate H true) hc hc).trans hhigh
  | low i t =>
    exact (trim_runs_infix false false (t+1) (t+1) (i+1) (i+1)
      (List.replicate p[i]! true) hc.2 hc.2).trans (hlow i hc.1)
  | wide i t =>
    have hl : t+1 ≤ (if i=0 then 1 else i) := hc.2
    have hr : t+1 ≤ i+1 := by split at hl <;> omega
    have hh := trim_runs_infix false false (t+1) (t+1) (if i=0 then 1 else i) (i+1)
      (List.replicate H true ++ List.replicate (i+1) false ++ List.replicate p[i]! true ++
        List.replicate (i+1) false ++ List.replicate H true) hl hr
    apply List.IsInfix.trans ?_ (permutationWindow_occurs H p i hc.1)
    simpa only [permDirectWord, permWindow, List.append_assoc] using hh
  | one t =>
    have htrim := trim_runs_infix true true (t+1) 0 H 0 [] hc (by omega)
    simp only [List.replicate_zero, List.append_nil] at htrim
    have hm : (List.replicate H true).IsInfix (permutationWord H p) := by
      exact middle_infix [false] _ (permTail H 0 p)
    exact htrim.trans hm
  | short i t =>
    have hv := (perm_parameter_at H p hb i hc.1).2
    have ht : t+1 ≤ H := by have := hc.2; omega
    exact (trim_runs_infix true true (t+1) (t+1) H p[i]!
      (List.replicate (i+1) false) ht hc.2).trans (hshort i hc.1)
  | long i t =>
    have hh := (trim_runs_infix true true (t+1) (t+1) H H
      (List.replicate (i+1) false ++ List.replicate p[i]! true ++ List.replicate (i+1) false)
      hc.2 hc.2).trans (hlong i hc.1)
    simpa only [permDirectWord, List.append_assoc] using hh

theorem nodup_map_on {α β : Type} (f : α → β) (xs : List α) (hn : xs.Nodup)
    (hf : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  apply List.pairwise_map.mpr
  apply hn.imp_of_mem
  intro a b ha hb hab he
  exact hab (hf a ha b hb he)

theorem mem_permCodeRows (f : Nat → Nat → PermPalCode) (n : Nat) (b : Nat → Nat) (c : PermPalCode) :
    c ∈ permCodeRows f n b ↔ ∃ i, i < n ∧ ∃ t, t < b i ∧ f i t = c := by
  simp [permCodeRows]

theorem permCodeRows_nodup (f : Nat → Nat → PermPalCode) (n : Nat) (b : Nat → Nat)
    (hf : ∀ i t j u, f i t = f j u → i=j ∧ t=u) : (permCodeRows f n b).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i hi
    exact nodup_map_on (f i) _ List.nodup_range (fun t _ u _ he => (hf i t i u he).2)
  · apply (List.nodup_range (n := n)).imp
    intro i j hij x hx y hy he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
    exact hij (hf i t j u he).1

theorem mem_permCodes (H : Nat) (p : List Nat) (c : PermPalCode) :
    c ∈ permCodes H p ↔ permCodeValid H p c := by
  cases c <;> simp [permCodes, mem_permCodeRows, permCodeValid]

theorem permCodes_nodup (H : Nat) (p : List Nat) : (permCodes H p).Nodup := by
  have hz := nodup_map_on PermPalCode.zero (List.range p.length) List.nodup_range
    (fun a _ b _ he => PermPalCode.zero.inj he)
  have hh := nodup_map_on PermPalCode.high (List.range p.length) List.nodup_range
    (fun a _ b _ he => PermPalCode.high.inj he)
  have ho := nodup_map_on PermPalCode.one (List.range H) List.nodup_range
    (fun a _ b _ he => PermPalCode.one.inj he)
  have hl := permCodeRows_nodup PermPalCode.low p.length (fun i => i+1)
    (fun _ _ _ _ he => PermPalCode.low.inj he)
  have hw := permCodeRows_nodup PermPalCode.wide p.length (fun i => if i=0 then 1 else i)
    (fun _ _ _ _ he => PermPalCode.wide.inj he)
  have hs := permCodeRows_nodup PermPalCode.short p.length (fun i => p[i]!)
    (fun _ _ _ _ he => PermPalCode.short.inj he)
  have hg := permCodeRows_nodup PermPalCode.long p.length (fun _ => H)
    (fun _ _ _ _ he => PermPalCode.long.inj he)
  simp only [permCodes, List.nodup_append, hz, hh, ho, hl, hw, hs, hg, true_and]
  simp [mem_permCodeRows]
  grind only

theorem permCodeRows_length (f : Nat → Nat → PermPalCode) (n : Nat) (b : Nat → Nat) :
    (permCodeRows f n b).length = ((List.range n).map b).sum := by
  simp [permCodeRows, List.length_flatMap]

theorem permLowWide_count (r : Nat) :
    ((List.range r).map (fun i => i+1)).sum +
      ((List.range r).map (fun i => if i=0 then 1 else i)).sum =
      r*r + (if r=0 then 0 else 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hr : r=0
    · simp [hr]
    · simp only [hr, ↓reduceIte, Nat.succ_ne_zero, Nat.add_mul, Nat.mul_add,
        Nat.mul_one, Nat.one_mul] at *
      omega

theorem map_range_getElem_self (p : List Nat) :
    (List.range p.length).map (fun i => p[i]!) = p := by
  induction p with
  | nil => simp
  | cons v vs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.getElem!_cons_zero, List.map_map, Function.comp_def, List.getElem!_cons_succ, ih]

theorem sum_replicate_nat (n a : Nat) : (List.replicate n a).sum = n*a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.add_mul, Nat.add_comm]

theorem permCodes_length (H : Nat) (p : List Nat) (hp : 0 < p.length) :
    (permCodes H p).length = (permutationWord H p).length := by
  have h := permLowWide_count p.length
  have hn : p.length ≠ 0 := by omega
  simp only [hn, ↓reduceIte] at h
  simp only [permCodes, List.length_append, List.length_map, List.length_range,
    permCodeRows_length, map_range_getElem_self]
  simp only [List.map_const', sum_replicate_nat, List.length_range]
  rw [permutationWord_length]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

theorem permutationWord_rich (H : Nat) (p : List Nat) (hp : 0 < p.length)
    (hn : p.Nodup) (hb : ∀ v ∈ p, 0 < v ∧ v < H) : Rich (permutationWord H p) := by
  have hv := perm_parameter_at H p hb 0 hp
  have hH : 0 < H := by omega
  let witnesses := (permCodes H p).map (permCodeWord H p)
  have hw : witnesses.Nodup := nodup_map_on _ _ (permCodes_nodup H p)
    (fun c hc d hd he => permCodeWord_injective H p hH hn hb c d
      ((mem_permCodes H p c).mp hc) ((mem_permCodes H p d).mp hd) he)
  have hne : [] ∉ witnesses := by
    intro hm
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
    exact permCodeWord_nonempty H p c he
  have hw' : ([] :: witnesses).Nodup := by exact List.nodup_cons.mpr ⟨hne, hw⟩
  have hsub : [] :: witnesses ⊆ palindromicFactors (permutationWord H p) := by
    intro w hwmem
    apply (mem_palindromicFactors_iff _ _).mpr
    rcases List.mem_cons.mp hwmem with rfl | hwmem
    · exact ⟨⟨[], permutationWord H p, by simp⟩, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hwmem
      exact ⟨permCodeWord_occurs H p hp hb c ((mem_permCodes H p c).mp hc),
        permCodeWord_palindrome H p c⟩
  have hlo := nodup_subset_length_le _ _ hw' hsub
  have hhi := palindromic_factor_count_bound (permutationWord H p)
  have hlen : witnesses.length = (permutationWord H p).length := by
    simpa only [witnesses, List.length_map] using permCodes_length H p hp
  simp only [List.length_cons, hlen] at hlo
  exact Nat.le_antisymm hhi hlo

theorem permTail_injective_same_length (H k : Nat) (p q : List Nat)
    (hlen : p.length = q.length) (he : permTail H k p = permTail H k q) : p=q := by
  induction p generalizing k q with
  | nil =>
    have hq : q=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    exact hq.symm
  | cons v vs ih =>
    cases q with
    | nil => simp at hlen
    | cons w ws =>
      have ht : vs.length = ws.length := by simpa using hlen
      simp only [permTail, List.append_assoc, List.append_cancel_left_eq] at he
      rw [List.replicate_succ, List.cons_append, List.cons_append] at he
      obtain ⟨hvw, hrest⟩ := gap_prefix_unique false v w _ _ he
      simp only [List.append_cancel_left_eq] at hrest
      have heq := ih (k+1) ws ht hrest
      simp [hvw, heq]

theorem permutationWord_injective_same_length (H : Nat) (p q : List Nat)
    (hlen : p.length = q.length) (he : permutationWord H p = permutationWord H q) : p=q := by
  apply permTail_injective_same_length H 0 p q hlen
  simpa only [permutationWord, List.append_assoc, List.append_cancel_left_eq] using he

theorem permutationParameters_sum (r : Nat) :
    2 * (permutationParameters r).sum = r*(r+1) := by
  induction r with
  | zero => simp [permutationParameters]
  | succ r ih =>
    simp only [permutationParameters, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] at *
    omega

theorem nat_sum_perm (p q : List Nat) (h : p.Perm q) : p.sum = q.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [List.sum_cons, ih]
  | swap a b l => simp only [List.sum_cons]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem permutationParameters_bounds (r : Nat) (p : List Nat)
    (h : p.Perm (permutationParameters r)) :
    p.length = r ∧ p.Nodup ∧ ∀ v ∈ p, 0 < v ∧ v < r+1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [permutationParameters, List.length_map, List.length_range] using h.length_eq
  · apply h.nodup_iff.mpr
    exact nodup_map_on (fun i => i+1) _ List.nodup_range (fun _ _ _ _ he => Nat.add_right_cancel he)
  · intro v hv
    have hm := h.mem_iff.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have hi' := List.mem_range.mp hi
    omega

theorem permutationWord_standard_rich (r : Nat) (p : List Nat) (hr : 0 < r)
    (h : p.Perm (permutationParameters r)) : Rich (permutationWord (r+1) p) := by
  obtain ⟨hl, hn, hb⟩ := permutationParameters_bounds r p h
  exact permutationWord_rich (r+1) p (by omega) hn hb

theorem permutationWord_standard_length (r : Nat) (p : List Nat)
    (h : p.Perm (permutationParameters r)) :
    (permutationWord (r+1) p).length = (5*r*r+9*r+4)/2 := by
  have hl := (permutationParameters_bounds r p h).1
  have hs := (nat_sum_perm p _ h)
  have ht := permutationParameters_sum r
  rw [← hs] at ht
  rw [permutationWord_length, hl]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] at *
  omega

theorem permutationWord_family_count (r : Nat) (ps : List (List Nat)) (hr : 0 < r)
    (hn : ps.Nodup) (ha : ∀ p ∈ ps, p.Perm (permutationParameters r)) :
    ps.length ≤ richCount ((5*r*r+9*r+4)/2) := by
  let ws := ps.map (permutationWord (r+1))
  have hw : ws.Nodup := nodup_map_on _ ps hn (by
    intro p hp q hq he
    apply permutationWord_injective_same_length (r+1) p q _ he
    have hp' := (permutationParameters_bounds r p (ha p hp)).1
    have hq' := (permutationParameters_bounds r q (ha q hq)).1
    omega)
  have hsub : ws ⊆ (allWords ((5*r*r+9*r+4)/2)).filter (fun w => decide (Rich w)) := by
    intro w hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    apply List.mem_filter.mpr
    refine ⟨(mem_allWords_iff _ _).mpr (permutationWord_standard_length r p (ha p hp)), ?_⟩
    simpa only [decide_eq_true_eq] using permutationWord_standard_rich r p hr (ha p hp)
  have hh := nodup_subset_length_le _ _ hw hsub
  simpa only [ws, List.length_map, richCount] using hh

theorem insertPositions_length (x : Nat) (p : List Nat) :
    (insertPositions x p).length = p.length+1 := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [insertPositions, ih]

theorem insertPositions_perm (x : Nat) (p q : List Nat) (hq : q ∈ insertPositions x p) :
    q.Perm (x :: p) := by
  induction p generalizing q with
  | nil => simpa [insertPositions] using hq
  | cons a as ih =>
    rcases List.mem_cons.mp hq with rfl | hq
    · exact List.Perm.refl _
    · obtain ⟨qs, hs, rfl⟩ := List.mem_map.mp hq
      exact ((ih qs hs).cons a).trans (List.Perm.swap x a as)

theorem insertPositions_filter (x : Nat) (p q : List Nat) (hx : x ∉ p)
    (hq : q ∈ insertPositions x p) : q.filter (· != x) = p := by
  induction p generalizing q with
  | nil =>
    have he : q=[x] := by simpa only [insertPositions, List.mem_singleton] using hq
    simp [he]
  | cons a as ih =>
    have hxa : x ≠ a := fun he => hx (he ▸ List.mem_cons_self)
    have hxs : x ∉ as := fun hm => hx (List.mem_cons_of_mem a hm)
    rcases List.mem_cons.mp hq with rfl | hq
    · have hf : (a::as).filter (· != x) = a::as := by
        apply List.filter_eq_self.mpr
        intro v hv
        simp only [bne_iff_ne]
        intro he
        exact hx (he ▸ hv)
      simpa using hf
    · obtain ⟨qs, hs, rfl⟩ := List.mem_map.mp hq
      have hi := ih qs hxs hs
      simp [hi, Ne.symm hxa]

theorem insertPositions_nodup (x : Nat) (p : List Nat) (hx : x ∉ p) :
    (insertPositions x p).Nodup := by
  induction p with
  | nil => simp [insertPositions]
  | cons a as ih =>
    have hxa : x ≠ a := fun he => hx (he ▸ List.mem_cons_self)
    have hxs : x ∉ as := fun hm => hx (List.mem_cons_of_mem a hm)
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨qs, hs, he⟩ := List.mem_map.mp hm
      exact hxa ((List.cons.inj he).1.symm)
    · exact nodup_map_on (a :: ·) _ (ih hxs) (fun _ _ _ _ he => (List.cons.inj he).2)

theorem permutationLists_valid (r : Nat) (p : List Nat) (hp : p ∈ permutationLists r) :
    p.Perm (permutationParameters r) := by
  induction r generalizing p with
  | zero =>
    have he : p=[] := by simpa only [permutationLists, List.mem_singleton] using hp
    simp [he, permutationParameters]
  | succ r ih =>
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    have h1 := insertPositions_perm (r+1) q p hp
    have h2 := (ih q hq).cons (r+1)
    have h3 : ((r+1) :: permutationParameters r).Perm (permutationParameters (r+1)) := by
      simpa only [permutationParameters, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, List.singleton_append] using
        (List.perm_append_comm (l₁ := [r+1]) (l₂ := permutationParameters r))
    exact h1.trans (h2.trans h3)

theorem permutationLists_nodup (r : Nat) : (permutationLists r).Nodup := by
  induction r with
  | zero => simp [permutationLists]
  | succ r ih =>
    have hx (p : List Nat) (hp : p ∈ permutationLists r) : r+1 ∉ p := by
      intro hm
      have hh := (permutationParameters_bounds r p (permutationLists_valid r p hp)).2.2 (r+1) hm
      omega
    apply List.pairwise_flatMap.mpr
    constructor
    · intro p hp
      exact insertPositions_nodup (r+1) p (hx p hp)
    · apply ih.imp_of_mem
      intro p q hp hq hpq u hu v hv he
      have hu' := insertPositions_filter (r+1) p u (hx p hp) hu
      have hv' := insertPositions_filter (r+1) q v (hx q hq) hv
      exact hpq (hu'.symm.trans ((congrArg (List.filter (· != r+1)) he).trans hv'))

theorem flatMap_length_constant {α β : Type} (xs : List α) (f : α → List β) (k : Nat)
    (h : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = k*xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have hs := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.flatMap_cons, List.length_append, ha, hs, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    omega

theorem permutationLists_length (r : Nat) :
    (permutationLists r).length = permutationFactorial r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [permutationLists, flatMap_length_constant _ _ (r+1), ih]
    · rfl
    · intro p hp
      rw [insertPositions_length, (permutationParameters_bounds r p
        (permutationLists_valid r p hp)).1]

theorem permutation_factorial_lower_bound (r : Nat) (hr : 0 < r) :
    permutationFactorial r ≤ richCount ((5*r*r+9*r+4)/2) := by
  have h := permutationWord_family_count r (permutationLists r) hr (permutationLists_nodup r)
    (permutationLists_valid r)
  simpa only [permutationLists_length] using h

theorem permCodeWord_eq_zero (H : Nat) (p : List Nat) (hH : 0 < H)
    (hb : ∀ v ∈ p, 0 < v ∧ v < H) (c : PermPalCode) (hc : permCodeValid H p c)
    (t : Nat) (he : permCodeWord H p c = List.replicate (t+1) false) : c = .zero t := by
  have he' : permCodeWord H p c = permCodeWord H p (.zero t) := by
    simpa only [permCodeWord, permCodeStart, permCodeTuple, expandGaps_zeros] using he
  obtain ⟨hs, ht⟩ := permCodeWord_eq_data H p c (.zero t) he'
  have hm := congrArg (fun xs : List Nat => xs.filter (· != 0)) ht
  dsimp only at hm
  rw [permCodeTuple_markers H p c hH hb hc] at hm
  simp only [permCodeTuple, List.filter_replicate] at hm
  have hl := congrArg List.length ht
  cases c <;>
    simp only [permCodeStart, permCodeMarkers, permCodeTuple, List.length_replicate,
      reduceCtorEq] at *
  all_goals grind only

theorem permTail_suffix (H k : Nat) (p : List Nat) :
    (List.replicate (k+p.length) false).IsSuffix (permTail H k p) := by
  induction p generalizing k with
  | nil => exact ⟨[], by simp [permTail]⟩
  | cons v vs ih =>
    obtain ⟨u, hu⟩ := ih (k+1)
    refine ⟨List.replicate (k+1) false ++ List.replicate v true ++
      List.replicate (k+1) false ++ List.replicate H true ++ u, ?_⟩
    have he : k+(v::vs).length = k+1+vs.length := by simp; omega
    rw [he]
    simpa only [permTail, List.append_assoc] using congrArg (fun z =>
      List.replicate (k+1) false ++ List.replicate v true ++
        List.replicate (k+1) false ++ List.replicate H true ++ z) hu

theorem permutationWord_padded_zero_factor (H : Nat) (p : List Nat) (e t : Nat)
    (ht : t ≤ p.length+e) :
    (List.replicate t false).IsInfix (permutationWord H p ++ List.replicate e false) := by
  obtain ⟨u, hu⟩ := permTail_suffix H 0 p
  simp only [Nat.zero_add] at hu
  have hs : (List.replicate (p.length+e) false).IsInfix
      (permutationWord H p ++ List.replicate e false) := by
    refine ⟨[false] ++ List.replicate H true ++ u, [], ?_⟩
    rw [permutationWord, ← hu]
    simp only [List.append_nil, ← List.replicate_append_replicate,
      List.append_assoc]
  have hm := trim_runs_infix false false t 0 (p.length+e) 0 [] ht (by omega)
  simp only [List.replicate_zero, List.append_nil] at hm
  exact hm.trans hs

theorem permutationWord_padded_rich (H : Nat) (p : List Nat) (e : Nat) (hp : 0 < p.length)
    (hn : p.Nodup) (hb : ∀ v ∈ p, 0 < v ∧ v < H) :
    Rich (permutationWord H p ++ List.replicate e false) := by
  have hv := perm_parameter_at H p hb 0 hp
  have hH : 0 < H := by omega
  let old := (permCodes H p).map (permCodeWord H p)
  let fresh := (List.range e).map (fun t => List.replicate (p.length+t+1) false)
  have hold : old.Nodup := nodup_map_on _ _ (permCodes_nodup H p)
    (fun c hc d hd he => permCodeWord_injective H p hH hn hb c d
      ((mem_permCodes H p c).mp hc) ((mem_permCodes H p d).mp hd) he)
  have hfresh : fresh.Nodup := nodup_map_on _ _ List.nodup_range (by
    intro t ht u hu he
    have hh := congrArg List.length he
    simp only [List.length_replicate] at hh
    omega)
  have hboth : (old ++ fresh).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hold, hfresh, ?_⟩
    intro w hw v hv he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    have hc' := (mem_permCodes H p c).mp hc
    have hz := permCodeWord_eq_zero H p hH hb c hc' (p.length+t) he
    rw [hz] at hc'
    simp only [permCodeValid] at hc'
    omega
  have hne : [] ∉ old ++ fresh := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
      exact permCodeWord_nonempty H p c he
    · obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
      have hh := congrArg List.length he
      simp only [List.length_replicate, List.length_nil] at hh
      omega
  have hnd := List.nodup_cons.mpr ⟨hne, hboth⟩
  have hsub : [] :: (old ++ fresh) ⊆
      palindromicFactors (permutationWord H p ++ List.replicate e false) := by
    intro w hw
    apply (mem_palindromicFactors_iff _ _).mpr
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨⟨[], permutationWord H p ++ List.replicate e false, by simp⟩, rfl⟩
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
        exact ⟨(permCodeWord_occurs H p hp hb c ((mem_permCodes H p c).mp hc)).trans
          List.infix_append_left, permCodeWord_palindrome H p c⟩
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
        have ht' := List.mem_range.mp ht
        exact ⟨permutationWord_padded_zero_factor H p e _ (by omega), by simp [Palindrome]⟩
  have hlo := nodup_subset_length_le _ _ hnd hsub
  have hhi := palindromic_factor_count_bound (permutationWord H p ++ List.replicate e false)
  simp only [List.length_cons, List.length_append, old, fresh, List.length_map,
    List.length_range, permCodes_length H p hp, List.length_replicate] at hlo hhi
  simpa only [Rich, List.length_append, List.length_replicate] using Nat.le_antisymm hhi hlo

theorem permutation_factorial_lower_bound_all_lengths (r n : Nat) (hr : 0 < r)
    (hn : (5*r*r+9*r+4)/2 ≤ n) : permutationFactorial r ≤ richCount n := by
  let N := (5*r*r+9*r+4)/2
  let f := fun p => permutationWord (r+1) p ++ List.replicate (n-N) false
  let ws := (permutationLists r).map f
  have hvalid (p : List Nat) (hp : p ∈ permutationLists r) := permutationLists_valid r p hp
  have hlen (p : List Nat) (hp : p ∈ permutationLists r) :
      (permutationWord (r+1) p).length = N := permutationWord_standard_length r p (hvalid p hp)
  have hw : ws.Nodup := nodup_map_on _ _ (permutationLists_nodup r) (by
    intro p hp q hq he
    apply permutationWord_injective_same_length (r+1) p q
    · have h1 := (permutationParameters_bounds r p (hvalid p hp)).1
      have h2 := (permutationParameters_bounds r q (hvalid q hq)).1
      omega
    · exact List.append_inj_left he ((hlen p hp).trans (hlen q hq).symm))
  have hsub : ws ⊆ (allWords n).filter (fun w => decide (Rich w)) := by
    intro w hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hl, hnd, hb⟩ := permutationParameters_bounds r p (hvalid p hp)
    apply List.mem_filter.mpr
    constructor
    · apply (mem_allWords_iff _ _).mpr
      simp only [f, List.length_append, List.length_replicate, hlen p hp]
      dsimp only [N]
      omega
    · have hh := permutationWord_padded_rich (r+1) p (n-N) (by omega) hnd hb
      simpa only [decide_eq_true_eq] using hh
  have hh := nodup_subset_length_le _ _ hw hsub
  simpa only [ws, List.length_map, permutationLists_length, richCount] using hh

end RichWords

#print axioms RichWords.permCodeWord_palindrome
#print axioms RichWords.permCodeWord_nonempty
#print axioms RichWords.perm_parameter_at
#print axioms RichWords.permCodeTuple_markers
#print axioms RichWords.permCodeWord_eq_data
#print axioms RichWords.permCodeWord_injective
#print axioms RichWords.expandGaps_zero_prefix
#print axioms RichWords.expandGaps_zeros
#print axioms RichWords.replicate_cons_join
#print axioms RichWords.permCodeWord_direct
#print axioms RichWords.permTail_prefix
#print axioms RichWords.permTail_length
#print axioms RichWords.permutationWord_length
#print axioms RichWords.middle_infix
#print axioms RichWords.trim_runs_infix
#print axioms RichWords.permWindow_occurs
#print axioms RichWords.permutationWindow_occurs
#print axioms RichWords.window_high_infix
#print axioms RichWords.window_low_infix
#print axioms RichWords.window_short_infix
#print axioms RichWords.window_long_infix
#print axioms RichWords.permCodeWord_occurs
#print axioms RichWords.nodup_map_on
#print axioms RichWords.mem_permCodeRows
#print axioms RichWords.permCodeRows_nodup
#print axioms RichWords.mem_permCodes
#print axioms RichWords.permCodes_nodup
#print axioms RichWords.permCodeRows_length
#print axioms RichWords.permLowWide_count
#print axioms RichWords.map_range_getElem_self
#print axioms RichWords.sum_replicate_nat
#print axioms RichWords.permCodes_length
#print axioms RichWords.permutationWord_rich
#print axioms RichWords.permTail_injective_same_length
#print axioms RichWords.permutationWord_injective_same_length
#print axioms RichWords.permutationParameters_sum
#print axioms RichWords.nat_sum_perm
#print axioms RichWords.permutationParameters_bounds
#print axioms RichWords.permutationWord_standard_rich
#print axioms RichWords.permutationWord_standard_length
#print axioms RichWords.permutationWord_family_count
#print axioms RichWords.insertPositions_length
#print axioms RichWords.insertPositions_perm
#print axioms RichWords.insertPositions_filter
#print axioms RichWords.insertPositions_nodup
#print axioms RichWords.permutationLists_valid
#print axioms RichWords.permutationLists_nodup
#print axioms RichWords.flatMap_length_constant
#print axioms RichWords.permutationLists_length
#print axioms RichWords.permutation_factorial_lower_bound
#print axioms RichWords.permCodeWord_eq_zero
#print axioms RichWords.permTail_suffix
#print axioms RichWords.permutationWord_padded_zero_factor
#print axioms RichWords.permutationWord_padded_rich
#print axioms RichWords.permutation_factorial_lower_bound_all_lengths
