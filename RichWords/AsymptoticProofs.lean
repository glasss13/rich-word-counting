import RichWords.AsymptoticDefinitions
import RichWords.OrderedCountProofs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RichWords

theorem asymptotic_factorial_eq (r : ℕ) : permutationFactorial r = r.factorial := by
  induction r with
  | zero => rfl
  | succ r ih => simp [permutationFactorial, Nat.factorial_succ, ih]

theorem asymptotic_factorial_lower (s u : ℕ) (h : s ≤ u) :
    s^u ≤ permutationFactorial (2*u) := by
  rw [asymptotic_factorial_eq]
  calc
    s^u ≤ (u+1)^u := Nat.pow_le_pow_left (by omega) u
    _ ≤ u.factorial * (u+1)^u := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ ≤ (u+u).factorial := Nat.factorial_mul_pow_le_factorial
    _ = _ := by rw [two_mul]

theorem asymptotic_product_append (xs ys : List ℕ) :
    orderedNatProduct (xs ++ ys) = orderedNatProduct xs * orderedNatProduct ys := by
  induction xs with
  | nil => simp [orderedNatProduct]
  | cons x xs ih => simp [orderedNatProduct, ih, mul_assoc]

theorem asymptotic_product_replicate (c r : ℕ) :
    orderedNatProduct (List.replicate c r) = r^c := by
  induction c with
  | zero => simp [orderedNatProduct]
  | succ c ih => simp [List.replicate_succ, orderedNatProduct, ih, pow_succ, mul_comm]

theorem asymptotic_mass_append (lo : ℕ) (xs ys : List OrderedBlockFamily) :
    orderedFamilyMass lo (xs ++ ys) =
      orderedFamilyMass lo xs + orderedFamilyMass (lo+2*xs.length) ys := by
  induction xs generalizing lo with
  | nil => simp [orderedFamilyMass]
  | cons x xs ih =>
    simp only [List.cons_append, orderedFamilyMass, ih, List.length_cons]
    rw [show lo + 2 + 2 * xs.length = lo + 2 * (xs.length + 1) by ring]
    omega

theorem asymptotic_mass_replicate (lo c : ℕ) (f : OrderedBlockFamily) :
    orderedFamilyMass lo (List.replicate c f) =
      c*(lo+c)*f.size + c*f.ones := by
  induction c generalizing lo with
  | zero => simp [orderedFamilyMass]
  | succ c ih =>
    simp only [List.replicate_succ, orderedFamilyMass, ih]
    ring

theorem asymptotic_block_size_upper (r : ℕ) (hr : 0 < r) :
    (orderedPermutationFamily r).size ≤ 9*r^2 := by
  change (5*r*r+9*r+4)/2 ≤ 9*r^2
  have hrr : r ≤ r*r := by nlinarith
  have hnum : 5*r*r+9*r+4 ≤ 2*(9*r^2) := by nlinarith
  exact (Nat.div_le_div_right hnum).trans (by omega)

theorem asymptotic_block_ones_upper (r : ℕ) (hr : 0 < r) :
    (orderedPermutationFamily r).ones ≤ 4*r^2 := by
  change (r+1)*(r+1) ≤ 4*r^2
  nlinarith

theorem scaled_dyadic_positive (s k c : ℕ) (hs : 0<s) :
    ∀ r ∈ scaledDyadicProfile s k c, 0<r := by
  induction k generalizing c with
  | zero => simpa [scaledDyadicProfile] using (fun (_ : c ≠ 0) => hs)
  | succ k ih =>
    intro r hr
    simp only [scaledDyadicProfile, List.mem_append] at hr
    rcases hr with hr | hr
    · have he := (List.mem_replicate.mp hr).2
      subst r
      positivity
    · exact ih (2*c) r hr

theorem scaled_dyadic_count_lower (s k c : ℕ) :
    s^((k+1)*s*c*2^k) ≤
      orderedNatProduct ((scaledDyadicProfile s k c).map permutationFactorial) := by
  have hf (j : ℕ) : s^(s*2^j) ≤ permutationFactorial (2*s*2^j) := by
    have h := asymptotic_factorial_lower s (s*2^j)
      (Nat.le_mul_of_pos_right s (by positivity))
    simpa [mul_assoc] using h
  induction k generalizing c with
  | zero =>
    simpa [scaledDyadicProfile, asymptotic_product_replicate, ← pow_mul] using
      Nat.pow_le_pow_left (hf 0) c
  | succ k ih =>
    simp only [scaledDyadicProfile, List.map_append, List.map_replicate,
      asymptotic_product_append, asymptotic_product_replicate]
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left (hf (k+1)) c) (ih (2*c))
    convert h using 1
    simp only [← pow_mul, ← pow_add, pow_succ]
    congr 1
    ring

theorem scaled_dyadic_level_mass_upper (s j c lo : ℕ) (hs : 0<s) (hc : 0<c)
    (hlo : lo ≤ 2*c) :
      orderedFamilyMass lo (List.replicate c (orderedPermutationFamily (2*s*2^j))) ≤
        200*(s*c*2^j)^2 := by
    rw [asymptotic_mass_replicate]
    have hr : 0 < 2*s*2^j := by positivity
    have hz := asymptotic_block_size_upper _ hr
    have ho := asymptotic_block_ones_upper _ hr
    have h1 := Nat.mul_le_mul_left (c*(lo+c)) hz
    have h2 := Nat.mul_le_mul_left c ho
    have h3 : c*(lo+c) ≤ 3*c^2 := by nlinarith
    have h4 := Nat.mul_le_mul_right (9*(2*s*2^j)^2) h3
    have h5 : c ≤ c^2 := by nlinarith
    have h6 := Nat.mul_le_mul_right (4*(2*s*2^j)^2) h5
    nlinarith

theorem scaled_dyadic_mass_upper (s k c lo : ℕ) (hs : 0<s) (hc : 0<c)
    (hlo : lo ≤ 2*c) :
    orderedFamilyMass lo ((scaledDyadicProfile s k c).map orderedPermutationFamily) ≤
      200*(k+1)*(s*c*2^k)^2 := by
  induction k generalizing c lo with
  | zero => simpa [scaledDyadicProfile] using scaled_dyadic_level_mass_upper s 0 c lo hs hc hlo
  | succ k ih =>
    simp only [scaledDyadicProfile, List.map_append, List.map_replicate,
      asymptotic_mass_append, List.length_replicate]
    have htail := ih (2*c) (lo+2*c) (by omega) (by omega)
    have hhead := scaled_dyadic_level_mass_upper s (k+1) c lo hs hc hlo
    calc
      _ ≤ 200*(s*c*2^(k+1))^2 + 200*(k+1)*(s*(2*c)*2^k)^2 := Nat.add_le_add hhead htail
      _ = _ := by rw [pow_succ]; ring

theorem scaled_dyadic_length_lower (s k : ℕ) : s ≤ scaledDyadicLength s k := by
  have hh : ∃ rs, scaledDyadicProfile s k 1 = (2*s*2^k) :: rs := by
    cases k with
    | zero => exact ⟨[], by simp [scaledDyadicProfile]⟩
    | succ k => exact ⟨scaledDyadicProfile s k 2, by simp [scaledDyadicProfile]⟩
  obtain ⟨rs, hrs⟩ := hh
  have hp : 1 ≤ 2^k := Nat.succ_le_iff.mpr (by positivity)
  have hsr : s ≤ 2*s*2^k := by nlinarith
  have hr : 2*s*2^k ≤ (2*s*2^k+1)*(2*s*2^k+1) := by nlinarith
  unfold scaledDyadicLength
  rw [hrs]
  simp only [List.map_cons, orderedFamilyMass]
  change s ≤ (0+1)*(orderedPermutationFamily (2*s*2^k)).size +
    (2*s*2^k+1)*(2*s*2^k+1) + _ + 1
  omega

theorem scaled_dyadic_length_upper (s k : ℕ) (hs : 0<s) :
    scaledDyadicLength s k ≤ 200*(k+1)*(s*2^k)^2+1 := by
  have h := scaled_dyadic_mass_upper s k 1 0 hs (by omega) (by omega)
  simpa [scaledDyadicLength] using Nat.add_le_add_right h 1

theorem scaled_dyadic_rich_lower (s k : ℕ) (hs : 0<s) :
    s^((k+1)*s*2^k) ≤ richCount (scaledDyadicLength s k) := by
  have h := ordered_permutation_product_lower 0 (scaledDyadicProfile s k 1)
    (scaled_dyadic_positive s k 1 hs)
  have hl : s^((k+1)*s*2^k) ≤
      orderedNatProduct ((scaledDyadicProfile s k 1).map permutationFactorial) := by
    simpa using scaled_dyadic_count_lower s k 1
  exact hl.trans h

/-- Entirely integer-valued witnesses exceeding every fixed square-root exponent multiplier. -/
theorem rich_count_integer_growth (B N : ℕ) :
    ∃ n t : ℕ, N ≤ n ∧ 2 ≤ n ∧ 1 ≤ t ∧ n ≤ t^2 ∧ n^(B*t) < richCount n := by
  let a := 84*B+1
  let k := a^2
  let s := 21*a*2^k+N+2
  let t := 21*a*s*2^k
  let n := scaledDyadicLength s k
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hs : 2 ≤ s := by dsimp [s]; omega
  have hsp : 21*a*2^k ≤ s := by dsimp [s]; omega
  have hNs : N ≤ s := by dsimp [s]; omega
  have hsn : s ≤ n := scaled_dyadic_length_lower s k
  have hx : 1 ≤ s*2^k := Nat.succ_le_iff.mpr (by positivity)
  have ht : 1 ≤ t := Nat.succ_le_iff.mpr (by dsimp [t]; positivity)
  have hnu := scaled_dyadic_length_upper s k (by omega)
  have hnt : n ≤ t^2 := by
    have ha2 : 1 ≤ a^2 := by nlinarith
    have hx2 : 1 ≤ (s*2^k)^2 := by nlinarith
    have hprod := Nat.mul_le_mul_right ((s*2^k)^2) ha2
    dsimp [n, k] at hnu ⊢
    dsimp [t, k]
    dsimp [k] at hx2 hprod
    nlinarith
  have hts : t ≤ s^2 := by
    have h := Nat.mul_le_mul_right s hsp
    dsimp [t]
    nlinarith
  have hns4 : n ≤ s^4 := by
    have h := Nat.pow_le_pow_left hts 2
    calc
      n ≤ t^2 := hnt
      _ ≤ (s^2)^2 := h
      _ = s^4 := by ring
  have he : 4*(B*t) < (k+1)*s*2^k := by
    have hcoeff : 84*B*a < a^2+1 := by dsimp [a]; nlinarith
    have h := Nat.mul_lt_mul_of_pos_right hcoeff (by omega : 0<s*2^k)
    dsimp [t,k]
    nlinarith
  refine ⟨n,t,by omega,by omega,ht,hnt,?_⟩
  calc
    n^(B*t) ≤ (s^4)^(B*t) := Nat.pow_le_pow_left hns4 _
    _ = s^(4*(B*t)) := (pow_mul _ _ _).symm
    _ < s^((k+1)*s*2^k) := Nat.pow_lt_pow_right (by omega) he
    _ ≤ richCount n := scaled_dyadic_rich_lower s k (by omega)

/-- For any real constants and any threshold, a larger length violates the bound. -/
theorem rich_count_exceeds_sqrt_power (C K : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
      K * (n : ℝ) ^ (C * Real.sqrt (n : ℝ)) < (richCount n : ℝ) := by
  obtain ⟨b, hb⟩ := exists_nat_ge C
  obtain ⟨M, hM⟩ := exists_nat_ge K
  obtain ⟨n,t,hN,hn,ht,hnt,hcount⟩ := rich_count_integer_growth (b+1) (max N M)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg _
  have hsqrt : Real.sqrt (n : ℝ) ≤ t := (Real.sqrt_le_left ht0).mpr (by exact_mod_cast hnt)
  have hKn : K ≤ (n:ℝ) := hM.trans (by exact_mod_cast (le_max_right N M).trans hN)
  have hexp : C * Real.sqrt (n:ℝ) ≤ (b:ℝ) * t :=
    mul_le_mul hb hsqrt (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hpow : (n:ℝ) ^ (C * Real.sqrt (n:ℝ)) ≤ (n:ℝ)^(b*t) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1 hexp
    rw [← Nat.cast_mul, Real.rpow_natCast] at h
    exact h
  have hmul : K * (n:ℝ) ^ (C * Real.sqrt (n:ℝ)) ≤ (n:ℝ) * (n:ℝ)^(b*t) :=
    mul_le_mul hKn hpow (Real.rpow_nonneg hn0.le _) hn0.le
  have hexpNat : b*t+1 ≤ (b+1)*t := by nlinarith
  have hlast : (n:ℝ) ^ ((b+1)*t) < (richCount n:ℝ) := by exact_mod_cast hcount
  refine ⟨n, (le_max_left N M).trans hN, hn, ?_⟩
  apply lt_of_le_of_lt hmul
  calc
    (n:ℝ) * (n:ℝ)^(b*t) = (n:ℝ)^(b*t+1) := by rw [pow_succ]; ring
    _ ≤ (n:ℝ)^((b+1)*t) := pow_le_pow_right₀ hn1 hexpNat
    _ < (richCount n:ℝ) := hlast

/-- The original conjecture is false, including its existential function and constants. -/
theorem rich_counting_conjecture_false : ¬ RichCountingConjecture := by
  rintro ⟨g,hg,hgInf,K,hK,N,hbound⟩
  have he : ∀ᶠ n in Filter.atTop, 1 ≤ g n :=
    hgInf.eventually (Filter.eventually_ge_atTop 1)
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp he
  obtain ⟨n,hn,_hn2,hlarge⟩ := rich_count_exceeds_sqrt_power 1 K (max N M)
  have hgn : 1 ≤ g n := hM n ((le_max_right N M).trans hn)
  have hbase : (n:ℝ) / g n ≤ n := div_le_self (Nat.cast_nonneg _) hgn
  have hpow := Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) (hg n).le)
    hbase (Real.sqrt_nonneg (n:ℝ))
  have hupper := (hbound n ((le_max_left N M).trans hn)).trans (mul_le_mul_of_nonneg_left hpow hK.le)
  simp only [one_mul] at hlarge
  exact (not_lt_of_ge hupper) hlarge

/-- No fixed multiplier C in the exponent permits an eventual upper bound. -/
theorem rich_count_no_sqrt_power_upper (C : ℝ) :
    ¬ ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      (richCount n : ℝ) ≤ K * (n : ℝ) ^ (C * Real.sqrt (n : ℝ)) := by
  rintro ⟨K,N,h⟩
  obtain ⟨n,hn,_,hlt⟩ := rich_count_exceeds_sqrt_power C K N
  exact (not_lt_of_ge (h n hn)) hlt

theorem rich_count_normalized_log_unbounded (A : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧ A < normalizedRichLog n := by
  obtain ⟨n,hn,hn2,hlarge⟩ := rich_count_exceeds_sqrt_power A 1 N
  simp only [one_mul] at hlarge
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < n := by linarith
  have hpos := Real.rpow_pos_of_pos hn0 (A * Real.sqrt (n:ℝ))
  have hlog := Real.log_lt_log hpos hlarge
  rw [Real.log_rpow hn0] at hlog
  have hden : 0 < Real.sqrt (n:ℝ) * Real.log (n:ℝ) :=
    mul_pos (Real.sqrt_pos.mpr hn0) (Real.log_pos hn1)
  refine ⟨n,hn,hn2,(lt_div_iff₀ hden).mpr ?_⟩
  simpa only [mul_assoc] using hlog

/-- The logarithmic divergence statement, with both limits fully formalized. -/
theorem rich_count_divergent_subsequence :
    ∃ ns : ℕ → ℕ,
      Filter.Tendsto ns Filter.atTop Filter.atTop ∧
      (∀ k, 2 ≤ ns k) ∧
      Filter.Tendsto (fun k => normalizedRichLog (ns k)) Filter.atTop Filter.atTop := by
  have h (k : ℕ) := rich_count_normalized_log_unbounded (k:ℝ) k
  choose ns hn hn2 hr using h
  refine ⟨ns,Filter.tendsto_atTop_mono hn Filter.tendsto_id,hn2,?_⟩
  exact Filter.tendsto_atTop_mono (fun k => (hr k).le) tendsto_natCast_atTop_atTop

end RichWords

#print axioms RichWords.asymptotic_factorial_eq
#print axioms RichWords.asymptotic_factorial_lower
#print axioms RichWords.asymptotic_product_append
#print axioms RichWords.asymptotic_product_replicate
#print axioms RichWords.asymptotic_mass_append
#print axioms RichWords.asymptotic_mass_replicate
#print axioms RichWords.asymptotic_block_size_upper
#print axioms RichWords.asymptotic_block_ones_upper
#print axioms RichWords.scaled_dyadic_positive
#print axioms RichWords.scaled_dyadic_count_lower
#print axioms RichWords.scaled_dyadic_level_mass_upper
#print axioms RichWords.scaled_dyadic_mass_upper
#print axioms RichWords.scaled_dyadic_length_lower
#print axioms RichWords.scaled_dyadic_length_upper
#print axioms RichWords.scaled_dyadic_rich_lower
#print axioms RichWords.rich_count_integer_growth
#print axioms RichWords.rich_count_exceeds_sqrt_power
#print axioms RichWords.rich_counting_conjecture_false
#print axioms RichWords.rich_count_no_sqrt_power_upper
#print axioms RichWords.rich_count_normalized_log_unbounded
#print axioms RichWords.rich_count_divergent_subsequence
