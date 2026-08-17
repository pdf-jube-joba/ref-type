namespace RefType

inductive USort where
  | set : Nat → USort
  | setKind : Nat → USort
  | prop
  | propKind
  deriving DecidableEq, Repr

namespace USort

def axiomTarget? : USort → Option USort
  | .set i => some (.setKind i)
  | .setKind _ => none
  | .prop => some .propKind
  | .propKind => none

def prodResult? : USort → USort → Option USort
  | .set i, .set j => some (.set (max i j))
  | .set i, .setKind j => some (.setKind (max i j))
  | .setKind i, .setKind j => some (.setKind (max i j))
  | .setKind i, .set j => some (.set (max (i + 1) j))
  | .prop, .prop => some .prop
  | .propKind, .prop => some .prop
  | .propKind, .propKind => some .propKind
  | .set _, .prop => some .prop
  | .set _, .propKind => some .propKind
  | _, _ => none

end USort

end RefType
