import RichWords.Definitions

namespace RichWords

inductive PermPalCode where
  | zero (t : Nat)
  | high (t : Nat)
  | low (i t : Nat)
  | wide (i t : Nat)
  | one (t : Nat)
  | short (i t : Nat)
  | long (i t : Nat)
  deriving DecidableEq

def permCodeStart : PermPalCode → Bool
  | .zero _ | .high _ | .low _ _ | .wide _ _ => false
  | .one _ | .short _ _ | .long _ _ => true

def permCodeTuple (H : Nat) (p : List Nat) : PermPalCode → List Nat
  | .zero t | .one t => List.replicate t 0
  | .high t => List.replicate t 0 ++ [H] ++ List.replicate t 0
  | .low i t => List.replicate t 0 ++ [p[i]!] ++ List.replicate t 0
  | .wide i t => List.replicate t 0 ++ [H] ++ List.replicate i 0 ++ [p[i]!] ++
      List.replicate i 0 ++ [H] ++ List.replicate t 0
  | .short i t => List.replicate t 0 ++ [i+1] ++ List.replicate t 0
  | .long i t => List.replicate t 0 ++ [i+1] ++ List.replicate (p[i]!-1) 0 ++
      [i+1] ++ List.replicate t 0

def permCodeWord (H : Nat) (p : List Nat) (c : PermPalCode) : Word :=
  expandGaps (permCodeStart c) (permCodeTuple H p c)

def permCodeValid (H : Nat) (p : List Nat) : PermPalCode → Prop
  | .zero t | .high t => t < p.length
  | .low i t => i < p.length ∧ t < i+1
  | .wide i t => i < p.length ∧ t < (if i = 0 then 1 else i)
  | .one t => t < H
  | .short i t => i < p.length ∧ t < p[i]!
  | .long i t => i < p.length ∧ t < H

def permCodeMarkers (H : Nat) (p : List Nat) : PermPalCode → List Nat
  | .zero _ | .one _ => []
  | .high _ => [H]
  | .low i _ => [p[i]!]
  | .wide i _ => [H, p[i]!, H]
  | .short i _ => [i+1]
  | .long i _ => [i+1, i+1]

def permDirectWord (H : Nat) (p : List Nat) : PermPalCode → Word
  | .zero t => List.replicate (t+1) false
  | .high t => List.replicate (t+1) false ++ List.replicate H true ++ List.replicate (t+1) false
  | .low i t => List.replicate (t+1) false ++ List.replicate p[i]! true ++ List.replicate (t+1) false
  | .wide i t => List.replicate (t+1) false ++ List.replicate H true ++
      List.replicate (i+1) false ++ List.replicate p[i]! true ++
      List.replicate (i+1) false ++ List.replicate H true ++ List.replicate (t+1) false
  | .one t => List.replicate (t+1) true
  | .short i t => List.replicate (t+1) true ++ List.replicate (i+1) false ++ List.replicate (t+1) true
  | .long i t => List.replicate (t+1) true ++ List.replicate (i+1) false ++
      List.replicate p[i]! true ++ List.replicate (i+1) false ++ List.replicate (t+1) true

def permTail (H k : Nat) : List Nat → Word
  | [] => List.replicate k false
  | v :: vs => List.replicate (k+1) false ++ List.replicate v true ++
      List.replicate (k+1) false ++ List.replicate H true ++ permTail H (k+1) vs

def permutationWord (H : Nat) (p : List Nat) : Word :=
  [false] ++ List.replicate H true ++ permTail H 0 p

def permWindow (H L k v : Nat) : Word :=
  List.replicate L false ++ List.replicate H true ++ List.replicate (k+1) false ++
  List.replicate v true ++ List.replicate (k+1) false ++ List.replicate H true ++
  List.replicate (k+1) false

def permCodeRows (f : Nat → Nat → PermPalCode) (n : Nat) (b : Nat → Nat) : List PermPalCode :=
  (List.range n).flatMap (fun i => (List.range (b i)).map (f i))

def permCodes (H : Nat) (p : List Nat) : List PermPalCode :=
  (List.range p.length).map .zero ++
  (List.range p.length).map .high ++
  permCodeRows .low p.length (fun i => i+1) ++
  permCodeRows .wide p.length (fun i => if i=0 then 1 else i) ++
  (List.range H).map .one ++
  permCodeRows .short p.length (fun i => p[i]!) ++
  permCodeRows .long p.length (fun _ => H)

def permutationParameters (r : Nat) : List Nat := (List.range r).map (fun i => i+1)

def insertPositions (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | a :: as => (x :: a :: as) :: (insertPositions x as).map (a :: ·)

def permutationLists : Nat → List (List Nat)
  | 0 => [[]]
  | r+1 => (permutationLists r).flatMap (insertPositions (r+1))

def permutationFactorial : Nat → Nat
  | 0 => 1
  | r+1 => (r+1) * permutationFactorial r

end RichWords
