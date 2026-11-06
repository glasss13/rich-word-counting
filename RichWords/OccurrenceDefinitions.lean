import RichWords.Definitions

namespace RichWords

/-- Number of ending positions of p in w; the empty word has length(w)+1.
Each prefix is listed once, and an occurrence ending there is exactly a suffix.
-/
def suffixOccurrenceCount {α : Type} [DecidableEq α] (p w : List α) : Nat :=
  ((prefixes w).filter (fun x => decide (p.IsSuffix x))).length

/-- Number of distinct palindromes of w having p as a suffix. -/
def palindromeSuffixCount {α : Type} [DecidableEq α] (p w : List α) : Nat :=
  ((palindromicFactors w).filter (fun q => decide (p.IsSuffix q))).length

end RichWords
