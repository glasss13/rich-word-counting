import RichWords.Definitions

namespace RichWords

/-- Distinct palindromic interiors between two positions selected by `mark`.
The endpoint letters need not be equal. The empty interior is permitted. -/
def markedPalindromeInteriors {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) : List (List α) :=
  (palindromicFactors w).filter fun p =>
    w.any fun a => mark a && w.any fun b =>
      mark b && decide ((a :: (p ++ [b])).IsInfix w)

/-- The subset compatibility deficit; the count theorem justifies subtraction. -/
def markedInteriorDefect {α : Type} [DecidableEq α]
    (mark : α → Bool) (w : List α) : Nat :=
  w.countP mark - 1 - (markedPalindromeInteriors mark w).length

end RichWords
