import RichWords.OrderedGlueDefinitions
import RichWords.PermutationDefinitions

namespace RichWords

def orderedNatProduct : List Nat → Nat
  | [] => 1
  | n :: ns => n * orderedNatProduct ns

structure OrderedBlockFamily where
  words : List Word
  size : Nat
  ones : Nat

def OrderedBlockFamily.Valid (f : OrderedBlockFamily) : Prop :=
  f.words.Nodup ∧ ∀ w ∈ f.words,
    w.length=f.size ∧ w.count true=f.ones ∧
      (∃ s, w=s ++ [true]) ∧ Rich (w ++ [true])

def orderedFamilyChoices : List OrderedBlockFamily → List (List Word)
  | [] => [[]]
  | f :: fs => f.words.flatMap (fun w => (orderedFamilyChoices fs).map (w :: ·))

def orderedFamilyMass (lo : Nat) : List OrderedBlockFamily → Nat
  | [] => 0
  | f :: fs => (lo+1)*f.size+f.ones+orderedFamilyMass (lo+2) fs

def orderedPermutationFamily (r : Nat) : OrderedBlockFamily :=
  { words := (permutationLists r).map (fun p => (permutationWord (r+1) p).map Bool.not)
    size := (5*r*r+9*r+4)/2
    ones := (r+1)*(r+1) }

end RichWords
