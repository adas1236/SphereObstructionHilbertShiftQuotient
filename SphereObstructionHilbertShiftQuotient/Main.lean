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

universe u v w

noncomputable section

private lemma hilbertDistortion_lt_top_witness
    (X : Type u) [PseudoMetricSpace X] (h : hilbertDistortion.{u, w} X < ⊤) :
    ∃ D : ENNReal, D < ⊤ /\
      1 ≤ D /\
        ∃ (H : Type (max u w)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
            (_ : CompleteSpace H),
          ∃ f : X → H, ∃ scale : ℝ,
            0 < scale /\
              ∀ x y : X,
                ENNReal.ofReal (scale * dist x y) ≤ ENNReal.ofReal ‖f x - f y‖ /\
                  ENNReal.ofReal ‖f x - f y‖ ≤
                    D * ENNReal.ofReal (scale * dist x y) := by
  rw [hilbertDistortion] at h
  rcases sInf_lt_iff.mp h with ⟨D, hDmem, hDtop⟩
  have hDmem' : 1 ≤ D ∧
      ∃ (H : Type (max u w)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
          (_ : CompleteSpace H),
        ∃ f : X → H, ∃ scale : ℝ,
          0 < scale ∧
            ∀ x y : X,
              ENNReal.ofReal (scale * dist x y) ≤ ENNReal.ofReal ‖f x - f y‖ ∧
                ENNReal.ofReal ‖f x - f y‖ ≤
                  D * ENNReal.ofReal (scale * dist x y) := by
    simpa using hDmem
  exact ⟨D, hDtop, hDmem'⟩

private lemma finiteSubsetHilbertDistortion_le_of_embedsWithDistortion
    {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : Finset X) {K : ℝ} (hK : 1 ≤ K)
    (hFY : FiniteMetricEmbedsWithDistortion Y F K)
    {D : ENNReal} (hD : 1 ≤ D)
    {H : Type (max u w)} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : Y → H) {targetScale : ℝ} (htargetScale : 0 < targetScale)
    (hg : ∀ x y : Y,
      ENNReal.ofReal (targetScale * dist x y) ≤ ENNReal.ofReal ‖g x - g y‖ /\
        ENNReal.ofReal ‖g x - g y‖ ≤
          D * ENNReal.ofReal (targetScale * dist x y)) :
    hilbertDistortion.{u, w} {x : X // x ∈ F} ≤ D * ENNReal.ofReal K := by
  rcases hFY with ⟨f, sourceScale, hsourceScale, hf⟩
  let totalScale : ℝ := targetScale * sourceScale
  have htotalScale : 0 < totalScale := mul_pos htargetScale hsourceScale
  unfold hilbertDistortion
  refine sInf_le ?_
  refine ⟨?_, H, inferInstance, inferInstance, inferInstance,
    (fun x : {x : X // x ∈ F} => g (f x)), totalScale, htotalScale, ?_⟩
  · have hK' : (1 : ENNReal) ≤ ENNReal.ofReal K := by
      simpa using ENNReal.ofReal_le_ofReal hK
    simpa using mul_le_mul' hD hK'
  · intro x y
    have hfxy := hf x y
    constructor
    · change ENNReal.ofReal (totalScale * dist x.1 y.1) ≤
        ENNReal.ofReal ‖g (f x) - g (f y)‖
      have hreal : totalScale * dist x.1 y.1 ≤ targetScale * dist (f x) (f y) := by
        calc
          totalScale * dist x.1 y.1 =
              targetScale * (sourceScale * dist x.1 y.1) := by
                ring
          _ ≤ targetScale * dist (f x) (f y) :=
              mul_le_mul_of_nonneg_left hfxy.1 htargetScale.le
      exact (ENNReal.ofReal_le_ofReal hreal).trans (hg (f x) (f y)).1
    · change ENNReal.ofReal ‖g (f x) - g (f y)‖ ≤
        (D * ENNReal.ofReal K) * ENNReal.ofReal (totalScale * dist x.1 y.1)
      have hK_nonneg : 0 ≤ K := le_trans zero_le_one hK
      have hreal :
          targetScale * dist (f x) (f y) ≤ K * (totalScale * dist x.1 y.1) := by
        calc
          targetScale * dist (f x) (f y) ≤
              targetScale * (K * sourceScale * dist x.1 y.1) :=
                mul_le_mul_of_nonneg_left hfxy.2 htargetScale.le
          _ = K * (totalScale * dist x.1 y.1) := by
                ring
      have hofReal :
          ENNReal.ofReal (targetScale * dist (f x) (f y)) ≤
            ENNReal.ofReal K * ENNReal.ofReal (totalScale * dist x.1 y.1) := by
        calc
          ENNReal.ofReal (targetScale * dist (f x) (f y)) ≤
              ENNReal.ofReal (K * (totalScale * dist x.1 y.1)) :=
                ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal K * ENNReal.ofReal (totalScale * dist x.1 y.1) :=
                ENNReal.ofReal_mul hK_nonneg
      calc
        ENNReal.ofReal ‖g (f x) - g (f y)‖ ≤
            D * ENNReal.ofReal (targetScale * dist (f x) (f y)) :=
              (hg (f x) (f y)).2
        _ ≤ D * (ENNReal.ofReal K * ENNReal.ofReal (totalScale * dist x.1 y.1)) :=
              mul_le_mul_right hofReal D
        _ = (D * ENNReal.ofReal K) * ENNReal.ofReal (totalScale * dist x.1 y.1) := by
              rw [← mul_assoc]

private lemma flatTorusFiniteSubsetEmbedsInShiftQuotientDistortionFive
    (n : Nat) (A : LatticeBasis n) (E : Finset (flatTorus n A)) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      FiniteMetricEmbedsWithDistortion shiftSphereQuotient E 5) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace (higherRankSphereQuotient n) := higherRankChordalMetric n
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  obtain ⟨toHigherRank, higherScale, hhigherScale, hhigher⟩ :=
    flatTorusFiniteSubsetEmbedsInHigherRankSphereQuotient n A E (1 / 2) (by norm_num)
  let G : Finset (higherRankSphereQuotient n) := Finset.univ.image toHigherRank
  let toG : {x : flatTorus n A // x ∈ E} -> {y : higherRankSphereQuotient n // y ∈ G} :=
    fun x => ⟨toHigherRank x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  obtain ⟨toShift, shiftScale, hshiftScale, hshift⟩ :=
    higherRankFiniteSubsetEmbedsInShiftQuotient n G (1 / 2) (by norm_num)
  let totalScale : ℝ := shiftScale * ((1 / 2) * higherScale)
  have htotalScale : 0 < totalScale := by
    dsimp [totalScale]
    positivity
  refine ⟨fun x => toShift (toG x), totalScale, htotalScale, ?_⟩
  intro x y
  have hhigherxy := hhigher x y
  have hshiftxy := hshift (toG x) (toG y)
  have hshiftFactor_nonneg : 0 ≤ (1 + (1 / 2 : ℝ)) * shiftScale := by
    positivity
  constructor
  · calc
      totalScale * dist x.1 y.1 =
          shiftScale * ((1 - (1 / 2 : ℝ)) * higherScale * dist x.1 y.1) := by
            dsimp [totalScale]
            ring
      _ ≤ shiftScale * dist (toHigherRank x) (toHigherRank y) :=
          mul_le_mul_of_nonneg_left hhigherxy.1 hshiftScale.le
      _ ≤ dist (toShift (toG x)) (toShift (toG y)) :=
          hshiftxy.1
  · calc
      dist (toShift (toG x)) (toShift (toG y)) ≤
          (1 + (1 / 2 : ℝ)) * shiftScale * dist (toHigherRank x) (toHigherRank y) :=
            hshiftxy.2
      _ ≤ (1 + (1 / 2 : ℝ)) * shiftScale *
          ((1 + (1 / 2 : ℝ)) * higherScale * dist x.1 y.1) :=
            mul_le_mul_of_nonneg_left hhigherxy.2 hshiftFactor_nonneg
      _ ≤ 5 * totalScale * dist x.1 y.1 := by
            dsimp [totalScale]
            nlinarith [hhigherScale.le, hshiftScale.le, dist_nonneg (x := x.1) (y := y.1)]

private lemma flatTorusHilbertDistortion_le_shiftWitnessBound
    (n : Nat) (A : LatticeBasis n)
    {D : ENNReal} (hD : 1 ≤ D)
    {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : shiftSphereQuotient → H) {targetScale : ℝ} (htargetScale : 0 < targetScale)
    (hg : ∀ x y : shiftSphereQuotient,
      ENNReal.ofReal (targetScale * shiftChordalMetric.dist x y) ≤
          ENNReal.ofReal ‖g x - g y‖ /\
        ENNReal.ofReal ‖g x - g y‖ ≤
          D * ENNReal.ofReal (targetScale * shiftChordalMetric.dist x y)) :
    (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
      hilbertDistortion.{0, w} (flatTorus n A) ≤ D * ENNReal.ofReal 5) := by
  classical
  letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  rw [finiteDetermination.{0, w, w} (flatTorus n A)]
  refine iSup_le ?_
  intro E
  exact finiteSubsetHilbertDistortion_le_of_embedsWithDistortion E (by norm_num)
    (flatTorusFiniteSubsetEmbedsInShiftQuotientDistortionFive n A E) hD g htargetScale
    (by simpa using hg)

private lemma finiteENNReal_lt_khotScale
    {B : ENNReal} (hB : B < ⊤) {c : ℝ} (hc : 0 < c) :
    ∃ N : Nat, B < ENNReal.ofReal (c * Real.sqrt (N : ℝ)) := by
  have hB_ne : B ≠ ⊤ := ne_of_lt hB
  obtain ⟨m, hm⟩ := exists_nat_gt (B.toReal / c)
  refine ⟨m * m, ?_⟩
  have hb_lt_cm : B.toReal < c * (m : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hm hc
    field_simp [ne_of_gt hc] at hmul
    linarith
  have hm_le_sqrt : (m : ℝ) ≤ Real.sqrt ((m * m : Nat) : ℝ) := by
    have hsq : (m : ℝ) ^ 2 ≤ ((m * m : Nat) : ℝ) := by
      norm_num [pow_two]
    exact Real.le_sqrt_of_sq_le hsq
  have hb_lt : B.toReal < c * Real.sqrt ((m * m : Nat) : ℝ) :=
    hb_lt_cm.trans_le (mul_le_mul_of_nonneg_left hm_le_sqrt hc.le)
  have hpos : 0 < c * Real.sqrt ((m * m : Nat) : ℝ) :=
    lt_of_le_of_lt ENNReal.toReal_nonneg hb_lt
  rw [← ENNReal.ofReal_toReal hB_ne]
  exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hb_lt

private lemma shiftChordalHilbertDistortion_eq_top :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      hilbertDistortion.{0, w} shiftSphereQuotient = ⊤) := by
  classical
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  by_contra hnot
  have hlt : hilbertDistortion shiftSphereQuotient < ⊤ := lt_top_iff_ne_top.mpr hnot
  obtain ⟨D, hDtop, hD, H, hNorm, hInner, hComplete, g, targetScale, htargetScale, hg⟩ :=
    hilbertDistortion_lt_top_witness shiftSphereQuotient hlt
  letI : NormedAddCommGroup H := hNorm
  letI : InnerProductSpace ℝ H := hInner
  letI : CompleteSpace H := hComplete
  let B : ENNReal := D * ENNReal.ofReal 5
  have hBtop : B < ⊤ := ENNReal.mul_lt_top hDtop ENNReal.ofReal_lt_top
  rcases khotNaorFlatTorusLowerBound with ⟨c, hc, hKN⟩
  obtain ⟨N, hN⟩ := finiteENNReal_lt_khotScale hBtop (c := c) hc
  obtain ⟨n, hnN, A, hlower⟩ := hKN N
  have hB_lt_lower : B < ENNReal.ofReal (c * Real.sqrt (n : ℝ)) := by
    have hN_le_sqrt : Real.sqrt (N : ℝ) ≤ Real.sqrt (n : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hnN)
    exact hN.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hN_le_sqrt hc.le))
  have hupper :
      (letI : PseudoMetricSpace (flatTorus n A) := flatTorusMetric n A;
        hilbertDistortion (flatTorus n A) ≤ B) := by
    simpa [B] using
      flatTorusHilbertDistortion_le_shiftWitnessBound n A hD g htargetScale hg
  exact (not_lt_of_ge (hlower.trans hupper)) hB_lt_lower

private lemma shiftChordalHilbertDistortion_lt_top_of_angular_lt_top
    (h :
      (letI : PseudoMetricSpace shiftSphereQuotient := shiftAngularMetric;
        hilbertDistortion.{0, w} shiftSphereQuotient < ⊤)) :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      hilbertDistortion.{0, w} shiftSphereQuotient < ⊤) := by
  classical
  letI : PseudoMetricSpace shiftSphereQuotient := shiftAngularMetric
  obtain ⟨D, hDtop, hD, H, hNorm, hInner, hComplete, g, targetScale, htargetScale, hg⟩ :=
    hilbertDistortion_lt_top_witness shiftSphereQuotient h
  letI : NormedAddCommGroup H := hNorm
  letI : InnerProductSpace ℝ H := hInner
  letI : CompleteSpace H := hComplete
  let bound : ENNReal := D * ENNReal.ofReal (Real.pi / 2)
  have hboundTop : bound < ⊤ := ENNReal.mul_lt_top hDtop ENNReal.ofReal_lt_top
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  have hdist_le_bound :
      hilbertDistortion.{0, w} shiftSphereQuotient ≤ bound := by
    unfold hilbertDistortion
    refine sInf_le ?_
    refine ⟨?_, H, inferInstance, inferInstance, inferInstance, g, targetScale,
      htargetScale, ?_⟩
    · have hpi : (1 : ENNReal) ≤ ENNReal.ofReal (Real.pi / 2) := by
        have hreal : (1 : ℝ) ≤ Real.pi / 2 := by
          nlinarith [Real.two_le_pi]
        simpa using ENNReal.ofReal_le_ofReal hreal
      simpa [bound] using mul_le_mul' hD hpi
    · intro x y
      have hmetrics := chordalAngularMetricEquivalence x y
      constructor
      · have hreal :
            targetScale * shiftChordalMetric.dist x y ≤
              targetScale * shiftAngularMetric.dist x y :=
          mul_le_mul_of_nonneg_left hmetrics.2.2 htargetScale.le
        exact (ENNReal.ofReal_le_ofReal hreal).trans (hg x y).1
      · have hang_le :
            shiftAngularMetric.dist x y ≤ (Real.pi / 2) * shiftChordalMetric.dist x y := by
          have hmul := mul_le_mul_of_nonneg_left hmetrics.2.1
            (by positivity : 0 ≤ Real.pi / 2)
          have hfactor : (Real.pi / 2) * (2 / Real.pi) = 1 := by
            field_simp [ne_of_gt Real.pi_pos]
          calc
            shiftAngularMetric.dist x y =
                1 * shiftAngularMetric.dist x y := by ring
            _ = ((Real.pi / 2) * (2 / Real.pi)) * shiftAngularMetric.dist x y := by
                rw [hfactor]
            _ = (Real.pi / 2) * ((2 / Real.pi) * shiftAngularMetric.dist x y) := by
                ring
            _ ≤ (Real.pi / 2) * shiftChordalMetric.dist x y := hmul
        have hreal :
            targetScale * shiftAngularMetric.dist x y ≤
              (Real.pi / 2) * (targetScale * shiftChordalMetric.dist x y) := by
          nlinarith [hang_le, htargetScale.le, dist_nonneg (x := x) (y := y)]
        have hpi_nonneg : 0 ≤ Real.pi / 2 := by positivity
        have hofReal :
            ENNReal.ofReal (targetScale * shiftAngularMetric.dist x y) ≤
              ENNReal.ofReal (Real.pi / 2) *
                ENNReal.ofReal (targetScale * shiftChordalMetric.dist x y) := by
          calc
            ENNReal.ofReal (targetScale * shiftAngularMetric.dist x y) ≤
                ENNReal.ofReal ((Real.pi / 2) *
                  (targetScale * shiftChordalMetric.dist x y)) :=
                  ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal (Real.pi / 2) *
                ENNReal.ofReal (targetScale * shiftChordalMetric.dist x y) :=
                  ENNReal.ofReal_mul hpi_nonneg
        calc
          ENNReal.ofReal ‖g x - g y‖ ≤
              D * ENNReal.ofReal (targetScale * shiftAngularMetric.dist x y) :=
                (hg x y).2
          _ ≤ D * (ENNReal.ofReal (Real.pi / 2) *
              ENNReal.ofReal (targetScale * shiftChordalMetric.dist x y)) :=
                mul_le_mul_right hofReal D
          _ = bound * ENNReal.ofReal (targetScale * shiftChordalMetric.dist x y) := by
                dsimp [bound]
                rw [mul_assoc]
  exact lt_of_le_of_lt hdist_le_bound hboundTop

/-- The shift sphere quotient has infinite Hilbert distortion for chordal and angular metrics. -/
theorem shiftSphereQuotientInfiniteHilbertDistortion :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      hilbertDistortion shiftSphereQuotient = ⊤) /\
      (letI : PseudoMetricSpace shiftSphereQuotient := shiftAngularMetric;
        hilbertDistortion shiftSphereQuotient = ⊤) := by
  refine ⟨shiftChordalHilbertDistortion_eq_top, ?_⟩
  by_contra hnot
  have hang_lt :
      (letI : PseudoMetricSpace shiftSphereQuotient := shiftAngularMetric;
        hilbertDistortion shiftSphereQuotient < ⊤) := lt_top_iff_ne_top.mpr hnot
  have hch_lt :
      (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
        hilbertDistortion shiftSphereQuotient < ⊤) :=
    shiftChordalHilbertDistortion_lt_top_of_angular_lt_top hang_lt
  rw [shiftChordalHilbertDistortion_eq_top] at hch_lt
  exact (lt_irrefl (⊤ : ENNReal)) hch_lt

/-- The finite Hilbert-distortion profile of the shift sphere quotient is unbounded. -/
theorem shiftSphereQuotientFiniteDistortionProfileUnbounded :
    (letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric;
      forall C : ENNReal, C < ⊤ ->
        exists F : Finset shiftSphereQuotient,
          C <= hilbertDistortion {x : shiftSphereQuotient // x ∈ F}) := by
  classical
  letI : PseudoMetricSpace shiftSphereQuotient := shiftChordalMetric
  intro C hC
  by_contra hno
  have hsup_le : (iSup fun F : Finset shiftSphereQuotient =>
      hilbertDistortion {x : shiftSphereQuotient // x ∈ F}) ≤ C := by
    refine iSup_le ?_
    intro F
    exact le_of_lt (not_le.mp (by
      intro hF
      exact hno ⟨F, hF⟩))
  have hiSup_top : (iSup fun F : Finset shiftSphereQuotient =>
      hilbertDistortion {x : shiftSphereQuotient // x ∈ F}) = (⊤ : ENNReal) := by
    exact (finiteDetermination.{0, 0} shiftSphereQuotient).symm.trans (by
      simpa using (shiftSphereQuotientInfiniteHilbertDistortion.{0, 0}).1)
  have htop_le : (⊤ : ENNReal) ≤ C := by
    rw [← hiSup_top]
    exact hsup_le
  exact (not_lt_of_ge htop_le) hC

end

end SphereObstructionHilbertShiftQuotient
