import RichWords.Definitions

namespace RichWords

/-- Consecutive ordered numeric values for one binary block. -/
def orderedPairLabel (lo : Nat) (b : Bool) : Nat := if b then lo+1 else lo

/-- Distinct consecutive pairs are assigned to successive blocks. -/
def orderedPairGaps (lo : Nat) : List Word → List Nat
  | [] => []
  | w :: ws => w.map (orderedPairLabel lo) ++ orderedPairGaps (lo+2) ws

end RichWords
