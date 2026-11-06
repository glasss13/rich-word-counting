import RichWords.MarkedDefinitions

namespace RichWords

/-- A gap expansion with specified opposite-letter padding at its two ends. -/
def framedGaps (a : Bool) (i : Nat) (xs : List Nat) (j : Nat) : Word :=
  List.replicate i (!a) ++ expandGaps a xs ++ List.replicate j (!a)

def gapMaximum (ys : List Nat) : Nat := ys.foldr Nat.max 0

def framedGapPalImage (a : Bool) (h : Nat) (ys : List Nat) : List Word :=
  (markedPalindromeInteriors (fun k => decide (h≤k)) ys).map (fun xs => framedGaps a h xs h)

def mixedGapPalindromes (a : Bool) (ys : List Nat) : List Word :=
  (List.range (gapMaximum ys)).flatMap (fun i => framedGapPalImage a (i+1) ys)

def unaryGapPalindromes (a : Bool) (ys : List Nat) : List Word :=
  (List.range (gapMaximum ys)).map (fun i => List.replicate (i+1) (!a))

def thresholdPalCover (a : Bool) (ys : List Nat) : List Word :=
  [] :: ((palindromicFactors ys).map (expandGaps a) ++
    unaryGapPalindromes a ys ++ mixedGapPalindromes a ys)

def thresholdDefectSum (ys : List Nat) : Nat :=
  ((List.range (gapMaximum ys)).map
    (fun i => markedInteriorDefect (fun k => decide (i+1≤k)) ys)).sum

end RichWords
