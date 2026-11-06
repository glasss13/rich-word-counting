import RichWords.Definitions

namespace RichWords

/-- Concatenation power, with the empty word at exponent zero. -/
def repeatWord {α : Type} (w : List α) : Nat → List α
  | 0 => []
  | k+1 => w ++ repeatWord w k

/-- A balanced rich period with an interior singleton-zero leaf run. -/
def leafContractionPeriod : Word :=
  [false,false,false,true,true,false,false,true,true,false,true,true,
   false,false,true,true,false,false,false,true,true,true]

/-- Delete that singleton zero and merge the neighboring one-runs. -/
def leafContractionImage : Word :=
  [false,false,false,true,true,false,false,true,true,true,true,
   false,false,true,true,false,false,false,true,true,true]

def leafContractionForbidden : Word :=
  [true,true,true,true,false,false,true,true,false,false,false,true,true,true]

end RichWords
