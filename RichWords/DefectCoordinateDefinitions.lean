import RichWords.OccurrenceDefinitions
namespace RichWords

/-- Missing palindrome contributions at occurrences of one letter. -/
def letterDefect {α : Type} [DecidableEq α] (a : α) (w : List α) : Nat :=
  w.count a - palindromeSuffixCount [a] w

end RichWords
