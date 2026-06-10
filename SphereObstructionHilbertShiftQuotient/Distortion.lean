import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false

/-!
Hilbert distortion API.

This file records the project-level interface for Euclidean distortion and its
finite-subset determination.  The bodies are intentionally left as stubs for the
first formalization pass.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

/-- The least Hilbert-space bilipschitz distortion of a pseudometric space. -/
noncomputable def hilbertDistortion (X : Type*) [PseudoMetricSpace X] : ENNReal :=
  sInf {D : ENNReal |
    1 ≤ D ∧
      ∃ (H : Type*) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H),
        ∃ f : X → H, ∃ scale : ℝ,
          0 < scale ∧
            ∀ x y : X,
              ENNReal.ofReal (scale * dist x y) ≤ ENNReal.ofReal ‖f x - f y‖ ∧
                ENNReal.ofReal ‖f x - f y‖ ≤ D * ENNReal.ofReal (scale * dist x y)}

/-- Hilbert distortion is determined by finite subsets. -/
theorem finiteDetermination (X : Type*) [PseudoMetricSpace X] :
    hilbertDistortion X =
      iSup (fun F : Finset X => hilbertDistortion {x : X // x ∈ F}) := by
  sorry

end

end SphereObstructionHilbertShiftQuotient
