import RichWords.OrderedCountDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

namespace RichWords

/-- The reference scale is sqrt(n) log(n); only n >= 2 is used in estimates. -/
noncomputable def normalizedRichLog (n : ℕ) : ℝ :=
  Real.log (richCount n : ℝ) / (Real.sqrt (n : ℝ) * Real.log (n : ℝ))

/-- The exact conjecture, with positive real-valued g and arbitrary eventual threshold. -/
def RichCountingConjecture : Prop :=
  ∃ g : ℕ → ℝ, (∀ n, 0 < g n) ∧
    Filter.Tendsto g Filter.atTop Filter.atTop ∧
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N,
      (richCount n : ℝ) ≤ K * ((n : ℝ) / g n) ^ Real.sqrt (n : ℝ)

/-- k+1 scales, with c, 2c, ..., 2^k c blocks and halving parameters.
The extra scale s makes the final comparison entirely algebraic. -/
def scaledDyadicProfile (s : ℕ) : ℕ → ℕ → List ℕ
  | 0, c => List.replicate c (2 * s)
  | k+1, c => List.replicate c (2 * s * 2^(k+1)) ++ scaledDyadicProfile s k (2*c)

def scaledDyadicLength (s k : ℕ) : ℕ :=
  orderedFamilyMass 0 ((scaledDyadicProfile s k 1).map orderedPermutationFamily) + 1

end RichWords
