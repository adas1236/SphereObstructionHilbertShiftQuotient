import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false

/-!
Sphere quotient models and their quotient metrics.

The declarations here name the one-dimensional shift quotient, the higher-rank
translation quotients, and the metric facts used by downstream files.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

/-- The unit sphere in the real Hilbert space `l2 Int`, before quotienting by shifts. -/
noncomputable def shiftHilbertSphere : Type := by
  sorry

/-- The metric topology on the shift Hilbert sphere. -/
@[reducible]
noncomputable def shiftHilbertSphereMetric : PseudoMetricSpace shiftHilbertSphere := by
  sorry

/-- The bilateral shift action on the Hilbert sphere. -/
noncomputable def shiftAction (k : Int) : shiftHilbertSphere -> shiftHilbertSphere := by
  sorry

/-- The orbit of a unit vector under all integer shifts. -/
noncomputable def shiftOrbit (x : shiftHilbertSphere) : Set shiftHilbertSphere :=
  Set.range fun k : Int => shiftAction k x

/-- Hilbert-space distance between shift-sphere representatives. -/
noncomputable def shiftRepresentativeNorm
    (x y : shiftHilbertSphere) : Real := by
  sorry

/-- Hilbert-space inner product between shift-sphere representatives. -/
noncomputable def shiftRepresentativeInner
    (x y : shiftHilbertSphere) : Real := by
  sorry

/-- The quotient of the unit sphere of `l2 Int` by the bilateral shift. -/
noncomputable def shiftSphereQuotient : Type := by
  sorry

/-- The quotient map from the shift Hilbert sphere to the shift quotient. -/
noncomputable def shiftQuotientMk : shiftHilbertSphere -> shiftSphereQuotient := by
  sorry

/-- The chordal quotient metric on the shift sphere quotient. -/
@[reducible]
noncomputable def shiftChordalMetric : PseudoMetricSpace shiftSphereQuotient := by
  sorry

/-- The angular quotient metric on the shift sphere quotient. -/
@[reducible]
noncomputable def shiftAngularMetric : PseudoMetricSpace shiftSphereQuotient := by
  sorry

/-- Shift orbits on the Hilbert sphere are closed. -/
theorem shiftOrbitsClosed (x : shiftHilbertSphere) :
    (letI : PseudoMetricSpace shiftHilbertSphere := shiftHilbertSphereMetric;
      IsClosed (shiftOrbit x)) := by
  sorry

/-- The chordal and angular quotient metrics are bilipschitz equivalent. -/
theorem chordalAngularMetricEquivalence :
    forall x y : shiftSphereQuotient,
      shiftChordalMetric.dist x y = 2 * Real.sin (shiftAngularMetric.dist x y / 2) /\
        (2 / Real.pi) * shiftAngularMetric.dist x y <= shiftChordalMetric.dist x y /\
          shiftChordalMetric.dist x y <= shiftAngularMetric.dist x y := by
  sorry

/-- The unit sphere in `l2 (Fin n -> Int)`, before quotienting by translations. -/
noncomputable def higherRankHilbertSphere (n : Nat) : Type := by
  sorry

/-- The metric topology on the higher-rank Hilbert sphere. -/
@[reducible]
noncomputable def higherRankHilbertSphereMetric
    (n : Nat) : PseudoMetricSpace (higherRankHilbertSphere n) := by
  sorry

/-- Translation by an element of `Z^n` on the higher-rank Hilbert sphere. -/
noncomputable def higherRankTranslation
    (n : Nat) (a : Fin n -> Int) : higherRankHilbertSphere n -> higherRankHilbertSphere n := by
  sorry

/-- The translation orbit of a higher-rank unit vector. -/
noncomputable def higherRankOrbit
    (n : Nat) (x : higherRankHilbertSphere n) : Set (higherRankHilbertSphere n) :=
  Set.range fun a : Fin n -> Int => higherRankTranslation n a x

/-- Hilbert-space distance between higher-rank representatives. -/
noncomputable def higherRankRepresentativeNorm
    (n : Nat) (x y : higherRankHilbertSphere n) : Real := by
  sorry

/-- Hilbert-space inner product between higher-rank representatives. -/
noncomputable def higherRankRepresentativeInner
    (n : Nat) (x y : higherRankHilbertSphere n) : Real := by
  sorry

/-- The quotient of the unit sphere of `l2 (Fin n -> Int)` by translations. -/
noncomputable def higherRankSphereQuotient (n : Nat) : Type := by
  sorry

/-- The quotient map from representatives to the higher-rank sphere quotient. -/
noncomputable def higherRankQuotientMk
    (n : Nat) : higherRankHilbertSphere n -> higherRankSphereQuotient n := by
  sorry

/-- The chordal quotient metric on the higher-rank sphere quotient. -/
@[reducible]
noncomputable def higherRankChordalMetric
    (n : Nat) : PseudoMetricSpace (higherRankSphereQuotient n) := by
  sorry

/-- The set of translated representative correlations. -/
noncomputable def higherRankCorrelationSet
    (n : Nat) (f g : higherRankHilbertSphere n) : Set Real :=
  Set.range fun a : Fin n -> Int =>
    higherRankRepresentativeInner n f (higherRankTranslation n a g)

/-- The supremum of translated representative correlations. -/
noncomputable def higherRankCorrelationSupFromRepresentatives
    (n : Nat) (f g : higherRankHilbertSphere n) : Real := by
  sorry

/-- The supremal translation correlation appearing in the quotient distance formula. -/
noncomputable def higherRankCorrelationSup
    (n : Nat) (x y : higherRankSphereQuotient n) : Real := by
  sorry

/-- Translation orbits on the higher-rank Hilbert sphere are closed. -/
theorem higherRankTranslationOrbitsClosed (n : Nat) (x : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankHilbertSphere n) := higherRankHilbertSphereMetric n;
      IsClosed (higherRankOrbit n x)) := by
  sorry

/-- The quotient distance is determined by translated representative correlations. -/
theorem higherRankCorrelationFormula (n : Nat) (f g : higherRankHilbertSphere n) :
    (letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      dist (higherRankQuotientMk n f) (higherRankQuotientMk n g) ^ 2 =
        2 - 2 * higherRankCorrelationSupFromRepresentatives n f g) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
