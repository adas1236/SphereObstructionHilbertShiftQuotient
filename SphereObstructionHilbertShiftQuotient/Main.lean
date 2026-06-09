import SphereObstructionHilbertShiftQuotient.Distortion
import SphereObstructionHilbertShiftQuotient.SphereQuotient
import SphereObstructionHilbertShiftQuotient.FlatTori
import SphereObstructionHilbertShiftQuotient.Gaussian
import SphereObstructionHilbertShiftQuotient.Coding

set_option linter.style.header false

/-!
Final assembly of the shift-sphere obstruction.

This file is kept small: it names the main infinite-distortion theorem and its
finite-profile corollary.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

/-- The shift sphere quotient has infinite Hilbert distortion for chordal and angular metrics. -/
theorem shiftSphereQuotientInfiniteHilbertDistortion :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      hilbertDistortion shiftSphereQuotient = ⊤) /\
      (letI : PseudoMetricSpace shiftSphereQuotient := shiftAngularMetric;
        hilbertDistortion shiftSphereQuotient = ⊤) := by
  sorry

/-- The finite Hilbert-distortion profile of the shift sphere quotient is unbounded. -/
theorem shiftSphereQuotientFiniteDistortionProfileUnbounded :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      forall C : ENNReal, C < ⊤ ->
        exists F : Finset shiftSphereQuotient,
          C <= hilbertDistortion {x : shiftSphereQuotient // x ∈ F}) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
