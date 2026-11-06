import RichWords.OrderedCountDefinitions
import RichWords.OrderedGlueProofs
import RichWords.PermutationProofs

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem ordered_pair_gaps_injective_layout (lo : Nat) (xs ys : List Word)
    (hl : xs.map List.length = ys.map List.length)
    (he : orderedPairGaps lo xs = orderedPairGaps lo ys) : xs=ys := by
  induction xs generalizing lo ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hparts := List.cons.inj hl
      have hlen : (x.map (orderedPairLabel lo)).length = (y.map (orderedPairLabel lo)).length := by
        simpa using hparts.1
      have hsplit := List.append_inj he hlen
      have hxy := (map_word_eq_iff (orderedPairLabel lo) (ordered_pair_label_injective lo) x y).mp hsplit.1
      have hrest := ih (lo+2) ys hparts.2 hsplit.2
      simp [hxy,hrest]

theorem ordered_pair_block_mass (lo : Nat) (w : Word) :
    (w.map (orderedPairLabel lo)).length+(w.map (orderedPairLabel lo)).sum =
      (lo+1)*w.length+w.count true := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a <;> simp [orderedPairLabel,Nat.mul_add] at * <;> omega

theorem ordered_family_choice_properties (lo : Nat) (fs : List OrderedBlockFamily)
    (hf : ∀ f ∈ fs, f.Valid) (ws : List Word) (hw : ws ∈ orderedFamilyChoices fs) :
    ws.map List.length = fs.map OrderedBlockFamily.size ∧
    (∀ w ∈ ws, (∃ s, w=s ++ [true]) ∧ Rich (w ++ [true])) ∧
    (orderedPairGaps lo ws).length+(orderedPairGaps lo ws).sum = orderedFamilyMass lo fs := by
  induction fs generalizing lo ws with
  | nil =>
    have he : ws=[] := by simpa [orderedFamilyChoices] using hw
    subst ws
    simp [orderedPairGaps,orderedFamilyMass]
  | cons f fs ih =>
    obtain ⟨w,hwm,tail,ht,rfl⟩ := (by
      simpa only [orderedFamilyChoices,List.mem_flatMap,List.mem_map] using hw :
        ∃ w ∈ f.words, ∃ tail ∈ orderedFamilyChoices fs, w :: tail = ws)
    have hp := (hf f (by simp)).2 w hwm
    have ht' := ih (lo+2) (fun g hg => hf g (by simp [hg])) tail ht
    refine ⟨by simp [hp.1,ht'.1],?_,?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with he | hm
      · subst z; exact hp.2.2
      · exact ht'.2.1 z hm
    · have hb := ordered_pair_block_mass lo w
      simp only [hp.1,hp.2.1] at hb
      simp only [orderedPairGaps,List.length_append,List.sum_append,orderedFamilyMass]
      omega

theorem ordered_family_choices_nodup (fs : List OrderedBlockFamily)
    (hf : ∀ f ∈ fs, f.Valid) : (orderedFamilyChoices fs).Nodup := by
  induction fs with
  | nil => simp [orderedFamilyChoices]
  | cons f fs ih =>
    have hn := ih (fun g hg => hf g (by simp [hg]))
    change (f.words.flatMap _).Nodup
    apply List.pairwise_flatMap.mpr
    constructor
    · intro w hw
      simpa only [List.Nodup,List.pairwise_map,ne_eq,List.cons.injEq,true_and] using hn
    · apply (hf f (by simp)).1.imp_of_mem
      intro u v hu hv huv x hx y hy he
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hy
      exact huv (List.cons.inj he).1

theorem ordered_family_choices_length (fs : List OrderedBlockFamily) :
    (orderedFamilyChoices fs).length = orderedNatProduct (fs.map (fun f => f.words.length)) := by
  induction fs with
  | nil => simp [orderedFamilyChoices,orderedNatProduct]
  | cons f fs ih =>
    rw [orderedFamilyChoices,flatMap_length_constant _ _ (orderedFamilyChoices fs).length]
    · simp [ih,Nat.mul_comm,orderedNatProduct]
    · intro w hw; simp

theorem ordered_family_count_lower (lo : Nat) (fs : List OrderedBlockFamily)
    (hf : ∀ f ∈ fs, f.Valid) :
    orderedNatProduct (fs.map (fun f => f.words.length)) ≤ richCount (orderedFamilyMass lo fs+1) := by
  let choices := orderedFamilyChoices fs
  let encode := fun ws => expandGaps false (orderedPairGaps lo ws)
  let outputs := choices.map encode
  have hn : outputs.Nodup := nodup_map_on encode choices (ordered_family_choices_nodup fs hf) (by
    intro xs hx ys hy he
    have hxl := (ordered_family_choice_properties lo fs hf xs hx).1
    have hyl := (ordered_family_choice_properties lo fs hf ys hy).1
    exact ordered_pair_gaps_injective_layout lo xs ys (hxl.trans hyl.symm)
      (expandGaps_injective false _ _ he))
  have hs : outputs ⊆ (allWords (orderedFamilyMass lo fs+1)).filter (fun w => decide (Rich w)) := by
    intro w hw
    obtain ⟨ws,hws,rfl⟩ := List.mem_map.mp hw
    have hp := ordered_family_choice_properties lo fs hf ws hws
    apply List.mem_filter.mpr
    refine ⟨(mem_allWords_iff _ _).mpr ?_,?_⟩
    · simp only [encode,expandGaps_length,hp.2.2]
    · simpa only [encode,decide_eq_true_eq] using ordered_pair_binary_expansion_rich lo ws hp.2.1
  have hb := nodup_subset_length_le outputs _ hn hs
  simpa only [outputs,List.length_map,choices,ordered_family_choices_length,richCount] using hb

theorem ordered_perm_tail_zero_count (H k : Nat) (p : List Nat) :
    (permTail H k p).count false = (2*p.length+1)*k+p.length*p.length+2*p.length := by
  induction p generalizing k with
  | nil => simp [permTail]
  | cons a p ih =>
    simp [permTail,ih,List.count_replicate,Nat.add_mul,Nat.mul_add] at *
    omega

theorem ordered_permutation_zero_count (H : Nat) (p : List Nat) :
    (permutationWord H p).count false = (p.length+1)*(p.length+1) := by
  simp [permutationWord,List.count_replicate,ordered_perm_tail_zero_count,Nat.add_mul,Nat.mul_add]
  omega

theorem ordered_complement_ones (w : Word) : (w.map Bool.not).count true = w.count false := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp [ih]

theorem ordered_permutation_end (H : Nat) (p : List Nat) (hp : 0<p.length) :
    ∃ s, permutationWord H p = s ++ [false] := by
  obtain ⟨u,hu⟩ := permTail_suffix H 0 p
  simp only [Nat.zero_add] at hu
  refine ⟨[false] ++ List.replicate H true ++ u ++ List.replicate (p.length-1) false,?_⟩
  rw [permutationWord,← hu]
  have he : List.replicate p.length false = List.replicate (p.length-1) false ++ [false] := by
    have he' : p.length=p.length-1+1 := by omega
    calc
      List.replicate p.length false = List.replicate (p.length-1+1) false :=
        congrArg (fun n => List.replicate n false) he'
      _ = List.replicate (p.length-1) false ++ List.replicate 1 false := List.replicate_append_replicate.symm
      _ = _ := by simp
  rw [he]
  simp [List.append_assoc]

theorem ordered_permutation_family_valid (r : Nat) (hr : 0<r) :
    (orderedPermutationFamily r).Valid := by
  have hnot : Function.Injective Bool.not := by
    intro a b he; cases a <;> cases b <;> simp_all
  constructor
  · apply nodup_map_on _ _ (permutationLists_nodup r)
    intro p hp q hq he
    have hpp := (permutationParameters_bounds r p (permutationLists_valid r p hp)).1
    have hqq := (permutationParameters_bounds r q (permutationLists_valid r q hq)).1
    exact permutationWord_injective_same_length (r+1) p q (by omega)
      ((map_word_eq_iff Bool.not hnot _ _).mp he)
  · intro w hw
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
    have hparam := permutationLists_valid r p hp
    obtain ⟨hlen,hnd,hbounds⟩ := permutationParameters_bounds r p hparam
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [List.length_map,orderedPermutationFamily] using
        permutationWord_standard_length r p hparam
    · simp only [ordered_complement_ones,ordered_permutation_zero_count,hlen,orderedPermutationFamily]
    · obtain ⟨s,hs⟩ := ordered_permutation_end (r+1) p (by omega)
      exact ⟨s.map Bool.not,by simp [hs]⟩
    · have hpad := permutationWord_padded_rich (r+1) p 1 (by omega) hnd hbounds
      have hm := palindromic_count_injective_map Bool.not hnot
        (permutationWord (r+1) p ++ [false])
      unfold Rich at *
      simpa using hm.trans hpad

theorem ordered_permutation_family_size (r : Nat) :
    (orderedPermutationFamily r).words.length = permutationFactorial r := by
  simp [orderedPermutationFamily,permutationLists_length]

theorem ordered_permutation_product_lower (lo : Nat) (rs : List Nat)
    (hr : ∀ r ∈ rs, 0<r) :
    orderedNatProduct (rs.map permutationFactorial) ≤
      richCount (orderedFamilyMass lo (rs.map orderedPermutationFamily)+1) := by
  have h := ordered_family_count_lower lo (rs.map orderedPermutationFamily) (by
    intro f hf
    obtain ⟨r,hrmem,rfl⟩ := List.mem_map.mp hf
    exact ordered_permutation_family_valid r (hr r hrmem))
  simpa only [List.map_map,Function.comp_def,ordered_permutation_family_size] using h

end RichWords

#print axioms RichWords.ordered_pair_gaps_injective_layout
#print axioms RichWords.ordered_pair_block_mass
#print axioms RichWords.ordered_family_choice_properties
#print axioms RichWords.ordered_family_choices_nodup
#print axioms RichWords.ordered_family_choices_length
#print axioms RichWords.ordered_family_count_lower
#print axioms RichWords.ordered_perm_tail_zero_count
#print axioms RichWords.ordered_permutation_zero_count
#print axioms RichWords.ordered_complement_ones
#print axioms RichWords.ordered_permutation_end
#print axioms RichWords.ordered_permutation_family_valid
#print axioms RichWords.ordered_permutation_family_size
#print axioms RichWords.ordered_permutation_product_lower
