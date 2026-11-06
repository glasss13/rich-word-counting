import RichWords.Definitions
namespace RichWords
/-- Episturmian expansion with its terminal protecting letter. -/
def protectedExpand (a : Bool) : Word → Word
  | [] => [a]
  | b :: w => if b = a then a :: protectedExpand a w
               else a :: (!a) :: protectedExpand a w

def bitGap (a b : Bool) : Nat := if b = a then 0 else 1
end RichWords
