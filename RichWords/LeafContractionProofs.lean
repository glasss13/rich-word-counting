import RichWords.LeafContractionDefinitions
import RichWords.OccurrenceProofs

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace RichWords

theorem palindromicFactors_reverse_members {α : Type} [DecidableEq α]
    (p w : List α) : p∈palindromicFactors w.reverse ↔ p∈palindromicFactors w := by
  constructor
  · intro h
    have hh := (mem_palindromicFactors_iff p w.reverse).mp h
    have hf := hh.1.reverse
    have hp : p.reverse=p := hh.2
    apply (mem_palindromicFactors_iff p w).mpr
    exact ⟨by simpa only [List.reverse_reverse,hp] using hf,hh.2⟩
  · intro h
    have hh := (mem_palindromicFactors_iff p w).mp h
    have hf := hh.1.reverse
    have hp : p.reverse=p := hh.2
    apply (mem_palindromicFactors_iff p w.reverse).mpr
    exact ⟨by simpa only [hp] using hf,hh.2⟩

theorem palindromicFactors_reverse_count {α : Type} [DecidableEq α]
    (w : List α) : (palindromicFactors w.reverse).length=(palindromicFactors w).length := by
  exact nodup_same_members_length _ _ (palindromicFactors_nodup _) (palindromicFactors_nodup _)
    (fun p => palindromicFactors_reverse_members p w)

theorem full_palindrome_count_reverse {α : Type} [DecidableEq α]
    (w : List α) (h : (palindromicFactors w).length=w.length+1) :
    (palindromicFactors w.reverse).length=w.reverse.length+1 := by
  simpa [palindromicFactors_reverse_count] using h

theorem full_palindrome_count_suffix {α : Type} [DecidableEq α]
    (x y : List α)
    (h : (palindromicFactors (x++y)).length=(x++y).length+1) :
    (palindromicFactors y).length=y.length+1 := by
  have hr := full_palindrome_count_reverse (x++y) h
  rw [List.reverse_append] at hr
  have hp := full_palindrome_count_prefix y.reverse x.reverse hr
  simpa [palindromicFactors_reverse_count] using hp

theorem full_palindrome_count_factor {α : Type} [DecidableEq α]
    (p w : List α) (h : (palindromicFactors w).length=w.length+1)
    (hf : Factor p w) : (palindromicFactors p).length=p.length+1 := by
  obtain ⟨x,y,he⟩ := hf
  rw [←he] at h
  have hp := full_palindrome_count_prefix (x++p) y h
  exact full_palindrome_count_suffix x p hp

theorem repeatWord_length {α : Type} (w : List α) (k : Nat) :
    (repeatWord w k).length=k*w.length := by
  induction k with
  | zero => simp [repeatWord]
  | succ k ih => simp [repeatWord,ih,Nat.succ_mul,Nat.add_comm]

theorem repeatWord_sublist {α : Type} (u v : List α) (k : Nat)
    (h : u.Sublist v) : (repeatWord u k).Sublist (repeatWord v k) := by
  induction k with
  | zero => exact List.Sublist.refl []
  | succ k ih => exact h.append ih

/-- Every retained nonrich block requires at least one insertion in a rich superword. -/
theorem repeated_nonrich_supersequence_length {α : Type} [DecidableEq α]
    (v : List α) (k : Nat) (z : List α)
    (hv : (palindromicFactors v).length≠v.length+1)
    (hz : (palindromicFactors z).length=z.length+1)
    (hs : (repeatWord v k).Sublist z) : k*(v.length+1)≤z.length := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    obtain ⟨s,t,he,hvs,hvt⟩ := List.append_sublist_iff.mp hs
    subst z
    have hsp := full_palindrome_count_prefix s t hz
    have htp := full_palindrome_count_suffix s t hz
    have hlong : v.length+1≤s.length := by
      by_cases hh : s.length≤v.length
      · have heq := hvs.eq_of_length_le hh
        exact False.elim (hv (by simpa only [heq] using hsp))
      · omega
    have hind := ih t htp hvt
    simp only [Nat.succ_mul,List.length_append]
    omega

theorem leaf_contraction_period_certificate :
    leafContractionPeriod.length=22 ∧
    leafContractionPeriod.count false=11 ∧ leafContractionPeriod.count true=11 ∧
    Rich (leafContractionPeriod++leafContractionPeriod) := by
  decide

theorem leaf_contraction_image_certificate :
    leafContractionImage.length=21 ∧
    leafContractionPeriod.take 9++leafContractionPeriod.drop 10=leafContractionImage ∧
    leafContractionImage.Sublist leafContractionPeriod ∧
    palindromeDefect leafContractionImage=1 ∧ ¬Rich leafContractionImage := by
  decide

theorem leaf_contraction_forbidden_certificate :
    leafContractionForbidden.length=14 ∧
    Factor leafContractionForbidden leafContractionImage ∧
    palindromeDefect leafContractionForbidden=1 ∧ ¬Rich leafContractionForbidden := by
  unfold Factor
  decide

theorem leaf_contraction_power_embedding (k : Nat) :
    (repeatWord leafContractionImage k).Sublist (repeatWord leafContractionPeriod k) := by
  exact repeatWord_sublist _ _ k leaf_contraction_image_certificate.2.2.1

theorem leaf_contraction_repair_lower_bound (k : Nat) (z : Word)
    (hz : Rich z) (hs : (repeatWord leafContractionImage k).Sublist z) :
    (repeatWord leafContractionPeriod k).length≤z.length := by
  have hv : (palindromicFactors leafContractionImage).length≠leafContractionImage.length+1 :=
    leaf_contraction_image_certificate.2.2.2.2
  have h := repeated_nonrich_supersequence_length leafContractionImage k z hv hz hs
  rw [leaf_contraction_image_certificate.1] at h
  simpa only [repeatWord_length,leaf_contraction_period_certificate.1] using h

end RichWords

#print axioms RichWords.palindromicFactors_reverse_members
#print axioms RichWords.palindromicFactors_reverse_count
#print axioms RichWords.full_palindrome_count_reverse
#print axioms RichWords.full_palindrome_count_suffix
#print axioms RichWords.full_palindrome_count_factor
#print axioms RichWords.repeatWord_length
#print axioms RichWords.repeatWord_sublist
#print axioms RichWords.repeated_nonrich_supersequence_length
#print axioms RichWords.leaf_contraction_period_certificate
#print axioms RichWords.leaf_contraction_image_certificate
#print axioms RichWords.leaf_contraction_forbidden_certificate
#print axioms RichWords.leaf_contraction_power_embedding
#print axioms RichWords.leaf_contraction_repair_lower_bound
