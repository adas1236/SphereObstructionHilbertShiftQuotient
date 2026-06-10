import Mathlib

set_option linter.style.header false

/-!
Basic shared setup for the `SphereObstructionHilbertShiftQuotient` formalization.

This file intentionally stays lightweight: it provides common notation and small
project-local predicates used to state the first-pass declaration stubs.
-/

namespace SphereObstructionHilbertShiftQuotient

/-- The mathlib model for finite-dimensional real Euclidean space. -/
abbrev RealEuclideanSpace (n : Nat) := _root_.EuclideanSpace Real (Fin n)

/--
A finite subset of one pseudometric space embeds into another with distortion at most `K`,
allowing an overall positive rescaling of distances.
-/
def FiniteMetricEmbedsWithDistortion
    (Y : Type*) {X : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : Finset X) (K : Real) : Prop :=
  exists f : {x : X // x ∈ F} -> Y, exists scale : Real,
    0 < scale /\
      forall x y : {x : X // x ∈ F},
        scale * dist x.1 y.1 <= dist (f x) (f y) /\
          dist (f x) (f y) <= K * scale * dist x.1 y.1

/--
A finite subset embeds into another space after rescaling, with the explicit
`(1 - eps)` and `(1 + eps)` two-sided error used in the blueprint.
-/
def FiniteMetricEmbedsWithScaleError
    (Y : Type*) {X : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : Finset X) (eps : Real) : Prop :=
  exists f : {x : X // x ∈ F} -> Y, exists scale : Real,
    0 < scale /\
      forall x y : {x : X // x ∈ F},
        (1 - eps) * scale * dist x.1 y.1 <= dist (f x) (f y) /\
          dist (f x) (f y) <= (1 + eps) * scale * dist x.1 y.1

/--
Two finite metric sets are bilipschitz equivalent up to distortion `K`, again allowing a
positive rescaling.
-/
def FiniteMetricApproximation
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : Finset X) (G : Finset Y) (K : Real) : Prop :=
  exists f : {x : X // x ∈ F} -> {y : Y // y ∈ G}, exists scale : Real,
    0 < scale /\
      forall x y : {x : X // x ∈ F},
        scale * dist x.1 y.1 <= dist (f x).1 (f y).1 /\
          dist (f x).1 (f y).1 <= K * scale * dist x.1 y.1

end SphereObstructionHilbertShiftQuotient
