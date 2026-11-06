import Std

/-!
Standalone definitions for the binary-rich-word counting problem.
Only Lean's bundled standard library is imported. Empty factors count;
words are not identified under reversal or exchange of the two letters.
-/
namespace RichWords

abbrev Word := List Bool

def Palindrome {α : Type} (w : List α) : Prop := w.reverse = w
instance {α : Type} [DecidableEq α] (w : List α) : Decidable (Palindrome w) := inferInstanceAs (Decidable (w.reverse = w))

/-- A contiguous factor, not an arbitrary subsequence. -/
def Factor {α : Type} (p w : List α) : Prop := p.IsInfix w

/-- All prefixes including the empty prefix, in increasing length. -/
def prefixes {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: w => [] :: (prefixes w).map (a :: ·)

/-- All contiguous factor occurrences (duplicates allowed). -/
def factorOccurrences {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: w => prefixes (a :: w) ++ factorOccurrences w

/-- Distinct palindromic factors, including the empty word. -/
def palindromicFactors {α : Type} [DecidableEq α] (w : List α) : List (List α) :=
  ((factorOccurrences w).filter (fun p => decide (Palindrome p))).eraseDups

def Rich (w : Word) : Prop := (palindromicFactors w).length = w.length + 1
instance (w : Word) : Decidable (Rich w) :=
  inferInstanceAs (Decidable ((palindromicFactors w).length = w.length + 1))

def allWords : Nat → List Word
  | 0 => [[]]
  | n + 1 => (allWords n).map (false :: ·) ++ (allWords n).map (true :: ·)

/-- Number of ordinary binary rich words of length n. -/
def richCount (n : Nat) : Nat :=
  ((allWords n).filter (fun w => decide (Rich w))).length


/-- Gap encodings and their palindrome-count auxiliaries. -/
def expandGaps (a : Bool) : List Nat → Word
  | [] => [a]
  | k :: ks => a :: (List.replicate k (!a) ++ expandGaps a ks)

def gapsAfter (a : Bool) (k : Nat) : Word → List Nat
  | [] => []
  | b :: w => if b = a then k :: gapsAfter a 0 w else gapsAfter a (k+1) w

def letterGaps (a : Bool) : Word → List Nat
  | [] => []
  | b :: w => if b = a then gapsAfter a 0 w else letterGaps a w

def gapPalImage (a : Bool) (w : Word) : List Word :=
  if a ∈ w then (palindromicFactors (letterGaps a w)).map (expandGaps a) else []

def gapPalCover (w : Word) : List Word :=
  [] :: (gapPalImage false w ++ gapPalImage true w)

def palindromeDefect {α : Type} [DecidableEq α] (w : List α) : Nat :=
  w.length + 1 - (palindromicFactors w).length

end RichWords
