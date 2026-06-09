import SphereObstructionHilbertShiftQuotient.SphereQuotient
import SphereObstructionHilbertShiftQuotient.FlatTori
import SphereObstructionHilbertShiftQuotient.Summation

set_option linter.style.header false

/-!
Gaussian lattice vectors and finite flat-torus realizations.

This file connects the flat torus metric to higher-rank sphere quotients through
Gaussian lattice representatives.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

/-- The normalized Gaussian lattice vector, viewed as a point of the quotient. -/
noncomputable def gaussianLatticeVector
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : EuclideanSpace n) :
    higherRankHilbertSphere n := by
  sorry

/-- The quotient point represented by the normalized Gaussian lattice vector. -/
noncomputable def gaussianQuotientPoint
    (n : Nat) (A : LatticeBasis n) (R : Real) (u : EuclideanSpace n) :
    higherRankSphereQuotient n := by
  exact higherRankQuotientMk n (gaussianLatticeVector n A R u)

/-- The Gaussian representative inner-product asymptotic, uniformly in the torus parameters. -/
theorem gaussianCorrelationAsymptotic
    (n : Nat) (A : LatticeBasis n) (N : Nat) (hN : 1 <= N) :
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall u w : EuclideanSpace n,
        exists theta : Real,
          |theta| <= C / R ^ N /\
            higherRankRepresentativeInner n (gaussianLatticeVector n A R u)
                (gaussianLatticeVector n A R w) =
              Real.exp (-(matrixNormSq n A (fun i => u i - w i)) / (4 * R ^ 2)) *
                (1 + theta) := by
  sorry

/--
Every finite subset of a flat torus embeds into the corresponding higher-rank
sphere quotient with arbitrarily small bilipschitz loss.
-/
theorem flatTorusFiniteSubsetEmbedsInHigherRankSphereQuotient
    (n : Nat) (A : LatticeBasis n)
    (E : Finset (flatTorus n A)) (eps : Real) (heps : 0 < eps) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n;
      FiniteMetricEmbedsWithScaleError (higherRankSphereQuotient n) E eps) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
