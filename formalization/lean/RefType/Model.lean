import RefType.system

namespace RefType.System

universe u

/-!
`UniverseTower` is the Lean-side semantic assumption for the direct model of
the original system.  It is intentionally a structure, not a global axiom:
the consistency theorem should eventually be parameterized by an instance of
this structure.

The fields here are only the first stable core.  Product, powerset, subset,
predicate, equality, existence, and take semantics should be added as the
soundness proof reaches the corresponding rules.
-/
structure UniverseTower where
  Val : Type u
  D : RefType.USort → Val → Prop
  sortVal : RefType.USort → Val
  sortAxiom_mem :
    ∀ {s t}, RefType.USort.axiomTarget? s = some t → D t (sortVal s)
  propTrue : Val
  propFalse : Val
  propTrue_mem : D .prop propTrue
  propFalse_mem : D .prop propFalse
  propTrue_ne_false : propTrue ≠ propFalse

end RefType.System
