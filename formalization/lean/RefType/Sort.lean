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
  | .set i, .set j =>
      if i = j then some (.set i) else none
  | .set i, .setKind j =>
      if i = j then some (.setKind i) else none
  | .setKind i, .setKind j =>
      if i = j then some (.setKind i) else none
  | .setKind i, .set j =>
      if i = j then some (.set (i + 1)) else none
  | .prop, .prop => some .prop
  | .propKind, .prop => some .prop
  | .propKind, .propKind => some .propKind
  | .set _, .prop => some .prop
  | .set _, .propKind => some .propKind
  | _, _ => none

end USort

end RefType
