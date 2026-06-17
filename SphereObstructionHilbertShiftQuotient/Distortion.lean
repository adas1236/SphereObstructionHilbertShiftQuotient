import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false

/-!
Hilbert distortion API.

This file records the project-level interface for Euclidean distortion and its
finite-subset determination.  The bodies are intentionally left as stubs for the
first formalization pass.
-/

namespace SphereObstructionHilbertShiftQuotient

universe u v w

open scoped Topology

noncomputable section

/-- The least Hilbert-space bilipschitz distortion of a pseudometric space. -/
noncomputable def hilbertDistortion (X : Type u) [PseudoMetricSpace X] : ENNReal :=
  sInf {D : ENNReal |
    1 ≤ D ∧
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
          (_ : CompleteSpace H),
        ∃ f : X → H, ∃ scale : ℝ,
          0 < scale ∧
            ∀ x y : X,
              ENNReal.ofReal (scale * dist x y) ≤ ENNReal.ofReal ‖f x - f y‖ ∧
                ENNReal.ofReal ‖f x - f y‖ ≤ D * ENNReal.ofReal (scale * dist x y)}

private structure RealHilbertEmbedding (X : Type u) [PseudoMetricSpace X] (K : ℝ) where
  H : Type (max u v)
  normed : NormedAddCommGroup H
  inner : InnerProductSpace ℝ H
  complete : CompleteSpace H
  f : X → H
  lower : ∀ x y : X, dist x y ≤ ‖f x - f y‖
  upper : ∀ x y : X, ‖f x - f y‖ ≤ K * dist x y

private lemma realEmbedding_of_hilbertDistortion_lt
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 1 < K)
    (h : hilbertDistortion.{u, v} X < ENNReal.ofReal K) :
    Nonempty (RealHilbertEmbedding.{u, v} X K) := by
  classical
  rw [hilbertDistortion] at h
  rcases sInf_lt_iff.mp h with ⟨D, hDmem, hDlt⟩
  rcases hDmem with ⟨_hDone, H, hNorm, hInner, hComplete, f, scale, hscale, hf⟩
  letI : NormedAddCommGroup H := hNorm
  letI : InnerProductSpace ℝ H := hInner
  letI : CompleteSpace H := hComplete
  let g : X → H := fun x => scale⁻¹ • f x
  refine ⟨⟨H, hNorm, hInner, hComplete, g, ?_, ?_⟩⟩
  · intro x y
    have hxy := (hf x y).1
    have hreal_scaled : scale * dist x y ≤ ‖f x - f y‖ := by
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp hxy
    have hscale_inv_pos : 0 < scale⁻¹ := inv_pos.mpr hscale
    have hnorm_g : ‖g x - g y‖ = scale⁻¹ * ‖f x - f y‖ := by
      have hgsub : g x - g y = scale⁻¹ • (f x - f y) := by
        simp [g, smul_sub]
      rw [hgsub, norm_smul, Real.norm_of_nonneg hscale_inv_pos.le]
    calc
      dist x y = scale⁻¹ * (scale * dist x y) := by field_simp [hscale.ne']
      _ ≤ scale⁻¹ * ‖f x - f y‖ :=
          mul_le_mul_of_nonneg_left hreal_scaled hscale_inv_pos.le
      _ = ‖g x - g y‖ := hnorm_g.symm
  · intro x y
    have hxy := (hf x y).2
    have hscaled_nonneg : 0 ≤ scale * dist x y := mul_nonneg hscale.le dist_nonneg
    have hK_nonneg : 0 ≤ K := le_trans zero_le_one hK.le
    have hENN :
        ENNReal.ofReal ‖f x - f y‖ ≤
          ENNReal.ofReal K * ENNReal.ofReal (scale * dist x y) := by
      exact hxy.trans (mul_le_mul' hDlt.le le_rfl)
    have hreal_scaled : ‖f x - f y‖ ≤ K * (scale * dist x y) := by
      rw [← ENNReal.ofReal_mul hK_nonneg] at hENN
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK_nonneg hscaled_nonneg)).mp hENN
    have hscale_inv_pos : 0 < scale⁻¹ := inv_pos.mpr hscale
    have hnorm_g : ‖g x - g y‖ = scale⁻¹ * ‖f x - f y‖ := by
      have hgsub : g x - g y = scale⁻¹ • (f x - f y) := by
        simp [g, smul_sub]
      rw [hgsub, norm_smul, Real.norm_of_nonneg hscale_inv_pos.le]
    calc
      ‖g x - g y‖ = scale⁻¹ * ‖f x - f y‖ := hnorm_g
      _ ≤ scale⁻¹ * (K * (scale * dist x y)) :=
          mul_le_mul_of_nonneg_left hreal_scaled hscale_inv_pos.le
      _ = K * dist x y := by field_simp [hscale.ne']

private noncomputable def finiteCenteredGram
    {X : Type u} [PseudoMetricSpace X] {K : ℝ}
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    (x0 x y : X) (F : Finset X) : ℝ := by
  classical
  by_cases hx0 : x0 ∈ F
  · by_cases hx : x ∈ F
    · by_cases hy : y ∈ F
      · let e := emb F
        letI : NormedAddCommGroup e.H := e.normed
        letI : InnerProductSpace ℝ e.H := e.inner
        exact inner ℝ (e.f ⟨x, hx⟩ - e.f ⟨x0, hx0⟩)
          (e.f ⟨y, hy⟩ - e.f ⟨x0, hx0⟩)
      · exact 0
    · exact 0
  · exact 0

private lemma finiteCenteredGram_apply_of_mem
    {X : Type u} [PseudoMetricSpace X] {K : ℝ}
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} {F : Finset X} (hx0 : x0 ∈ F) (hx : x ∈ F) (hy : y ∈ F) :
    finiteCenteredGram emb x0 x y F =
      let e := emb F
      letI : NormedAddCommGroup e.H := e.normed
      letI : InnerProductSpace ℝ e.H := e.inner
      inner ℝ (e.f ⟨x, hx⟩ - e.f ⟨x0, hx0⟩)
        (e.f ⟨y, hy⟩ - e.f ⟨x0, hx0⟩) := by
  simp [finiteCenteredGram, hx0, hx, hy]

private def gramBound {X : Type u} [PseudoMetricSpace X] (K : ℝ) (x0 x y : X) : ℝ :=
  (K * dist x x0) * (K * dist y x0)

private lemma gramBound_nonneg {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (x0 x y : X) : 0 ≤ gramBound K x0 x y := by
  exact mul_nonneg (mul_nonneg hK dist_nonneg) (mul_nonneg hK dist_nonneg)

private abbrev GramBox {X : Type u} [PseudoMetricSpace X] (K : ℝ) (x0 : X) :=
  (p : X × X) → Set.Icc (-(gramBound K x0 p.1 p.2)) (gramBound K x0 p.1 p.2)

private noncomputable def boundedGramPoint
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    (x0 : X) (F : Finset X) : GramBox K x0 :=
  fun p =>
    let C := gramBound K x0 p.1 p.2
    Set.projIcc (-C) C (by linarith [gramBound_nonneg (K := K) hK x0 p.1 p.2])
      (finiteCenteredGram emb x0 p.1 p.2 F)

private def gramBoxCoord {X : Type u} [PseudoMetricSpace X] {K : ℝ} {x0 : X}
    (x y : X) (z : GramBox K x0) : ℝ :=
  (z (x, y)).1

@[fun_prop]
private lemma continuous_gramBoxCoord {X : Type u} [PseudoMetricSpace X] {K : ℝ} {x0 : X}
    (x y : X) : Continuous (gramBoxCoord (K := K) (x0 := x0) x y) := by
  exact continuous_subtype_val.comp (continuous_apply (x, y))

private lemma finiteCenteredGram_abs_le_bound
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} {F : Finset X} (hx0 : x0 ∈ F) (hx : x ∈ F) (hy : y ∈ F) :
    |finiteCenteredGram emb x0 x y F| ≤ gramBound K x0 x y := by
  rw [finiteCenteredGram_apply_of_mem emb hx0 hx hy]
  let e := emb F
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  have hxupper := e.upper ⟨x, hx⟩ ⟨x0, hx0⟩
  have hyupper := e.upper ⟨y, hy⟩ ⟨x0, hx0⟩
  have hxnonneg : 0 ≤ K * dist x x0 := mul_nonneg hK dist_nonneg
  calc
    |inner ℝ (e.f ⟨x, hx⟩ - e.f ⟨x0, hx0⟩)
        (e.f ⟨y, hy⟩ - e.f ⟨x0, hx0⟩)| =
        ‖inner ℝ (e.f ⟨x, hx⟩ - e.f ⟨x0, hx0⟩)
          (e.f ⟨y, hy⟩ - e.f ⟨x0, hx0⟩)‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ‖e.f ⟨x, hx⟩ - e.f ⟨x0, hx0⟩‖ *
        ‖e.f ⟨y, hy⟩ - e.f ⟨x0, hx0⟩‖ :=
          norm_inner_le_norm _ _
    _ ≤ (K * dist x x0) * (K * dist y x0) :=
          mul_le_mul hxupper hyupper (norm_nonneg _) hxnonneg

private lemma gramBoxCoord_boundedGramPoint_of_mem
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} {F : Finset X} (hx0 : x0 ∈ F) (hx : x ∈ F) (hy : y ∈ F) :
    gramBoxCoord x y (boundedGramPoint hK emb x0 F) =
      finiteCenteredGram emb x0 x y F := by
  unfold gramBoxCoord boundedGramPoint
  let C := gramBound K x0 x y
  have habs := finiteCenteredGram_abs_le_bound hK emb hx0 hx hy
  have hmem : finiteCenteredGram emb x0 x y F ∈ Set.Icc (-C) C := by
    rw [Set.mem_Icc]
    exact (abs_le.mp (by simpa [C] using habs))
  rw [Set.projIcc_of_mem (by linarith [gramBound_nonneg (K := K) hK x0 x y]) hmem]

private lemma finiteSuperset_mem_atTop {X : Type u} (S : Finset X) :
    {F : Finset X | S ⊆ F} ∈ (Filter.atTop : Filter (Finset X)) := by
  simpa using (Filter.mem_atTop S : {F : Finset X | S ≤ F} ∈
    (Filter.atTop : Filter (Finset X)))

private lemma finiteSuperset_mem_ultrafilterAtTop {X : Type u} (S : Finset X) :
    {F : Finset X | S ⊆ F} ∈
      (Ultrafilter.of (Filter.atTop : Filter (Finset X)) : Ultrafilter (Finset X)) := by
  exact Ultrafilter.of_le (Filter.atTop : Filter (Finset X)) (finiteSuperset_mem_atTop S)

private lemma ultralimit_nonneg_of_eventually_nonneg
    {ι Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (U : Ultrafilter ι) (a : ι → Y) {P : Y → ℝ} (hP : Continuous P)
    (hEv : ∀ᶠ i in (U : Filter ι), 0 ≤ P (a i)) :
    0 ≤ P ((U.map a).lim) := by
  have htend_a : Filter.Tendsto a (U : Filter ι) (𝓝 (U.map a).lim) := by
    simpa [Ultrafilter.coe_map] using (Ultrafilter.le_nhds_lim (U.map a))
  have htend :
      Filter.Tendsto (fun i => P (a i)) (U : Filter ι) (𝓝 (P ((U.map a).lim))) :=
    hP.tendsto _ |>.comp htend_a
  exact isClosed_Ici.mem_of_tendsto htend hEv

private lemma ultralimit_le_of_eventually_le
    {ι Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (U : Ultrafilter ι) (a : ι → Y) {P : Y → ℝ} (hP : Continuous P) {c : ℝ}
    (hEv : ∀ᶠ i in (U : Filter ι), P (a i) ≤ c) :
    P ((U.map a).lim) ≤ c := by
  have htend_a : Filter.Tendsto a (U : Filter ι) (𝓝 (U.map a).lim) := by
    simpa [Ultrafilter.coe_map] using (Ultrafilter.le_nhds_lim (U.map a))
  exact isClosed_Iic.mem_of_tendsto (hP.tendsto _ |>.comp htend_a) hEv

private lemma ultralimit_const_le_of_eventually_const_le
    {ι Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (U : Ultrafilter ι) (a : ι → Y) {P : Y → ℝ} (hP : Continuous P) {c : ℝ}
    (hEv : ∀ᶠ i in (U : Filter ι), c ≤ P (a i)) :
    c ≤ P ((U.map a).lim) := by
  have htend_a : Filter.Tendsto a (U : Filter ι) (𝓝 (U.map a).lim) := by
    simpa [Ultrafilter.coe_map] using (Ultrafilter.le_nhds_lim (U.map a))
  exact isClosed_Ici.mem_of_tendsto (hP.tendsto _ |>.comp htend_a) hEv

private lemma ultralimit_eq_of_eventually_eq
    {ι Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (U : Ultrafilter ι) (a : ι → Y) {P Q : Y → ℝ}
    (hP : Continuous P) (hQ : Continuous Q)
    (hEv : ∀ᶠ i in (U : Filter ι), P (a i) = Q (a i)) :
    P ((U.map a).lim) = Q ((U.map a).lim) := by
  have htend_a : Filter.Tendsto a (U : Filter ι) (𝓝 (U.map a).lim) := by
    simpa [Ultrafilter.coe_map] using (Ultrafilter.le_nhds_lim (U.map a))
  exact (isClosed_eq hP hQ).mem_of_tendsto htend_a hEv

private def quadPoly {X : Type u} [PseudoMetricSpace X] {K : ℝ} {x0 : X}
    (c : X →₀ ℝ) (z : GramBox K x0) : ℝ :=
  ∑ x ∈ c.support, ∑ y ∈ c.support,
    c x * c y * gramBoxCoord (K := K) (x0 := x0) x y z

private lemma continuous_quadPoly {X : Type u} [PseudoMetricSpace X] {K : ℝ} {x0 : X}
    (c : X →₀ ℝ) : Continuous (quadPoly (K := K) (x0 := x0) c) := by
  unfold quadPoly
  fun_prop

private def distSqPoly {X : Type u} [PseudoMetricSpace X] {K : ℝ} {x0 : X}
    (x y : X) (z : GramBox K x0) : ℝ :=
  gramBoxCoord x x z + gramBoxCoord y y z - 2 * gramBoxCoord x y z

private lemma continuous_distSqPoly {X : Type u} [PseudoMetricSpace X] {K : ℝ} {x0 : X}
    (x y : X) : Continuous (distSqPoly (K := K) (x0 := x0) x y) := by
  unfold distSqPoly
  fun_prop

private lemma quadPoly_boundedGramPoint_nonneg_of_subset
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 : X} {c : X →₀ ℝ} {F : Finset X}
    (hx0 : x0 ∈ F) (hsupp : c.support ⊆ F) :
    0 ≤ quadPoly c (boundedGramPoint hK emb x0 F) := by
  classical
  let e := emb F
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  let v : X → e.H := fun x =>
    if hx : x ∈ F then e.f ⟨x, hx⟩ - e.f ⟨x0, hx0⟩ else 0
  have hcoord {x y : X} (hx : x ∈ c.support) (hy : y ∈ c.support) :
      gramBoxCoord x y (boundedGramPoint hK emb x0 F) = inner ℝ (v x) (v y) := by
    have hxF : x ∈ F := hsupp hx
    have hyF : y ∈ F := hsupp hy
    rw [gramBoxCoord_boundedGramPoint_of_mem hK emb hx0 hxF hyF]
    rw [finiteCenteredGram_apply_of_mem emb hx0 hxF hyF]
    simp [v, e, hxF, hyF]
  calc
    quadPoly c (boundedGramPoint hK emb x0 F) =
        ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * inner ℝ (v x) (v y) := by
      unfold quadPoly
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [hcoord hx hy]
    _ = ‖∑ x ∈ c.support, c x • v x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (∑ x ∈ c.support, c x • v x)]
      simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
      simp [real_inner_comm, Finset.mul_sum, mul_assoc]
    _ ≥ 0 := sq_nonneg _

private def scalarCLM (a : ℝ) : ℝ →L[ℝ] ℝ :=
  a • (1 : ℝ →L[ℝ] ℝ)

private def opKernel {X : Type u} (G : Matrix X X ℝ) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => scalarCLM (G x y)

private lemma opKernel_isHermitian {X : Type u} {G : Matrix X X ℝ} (hG : G.PosSemidef) :
    (opKernel G).IsHermitian := by
  classical
  ext x y
  simp only [opKernel, scalarCLM, Matrix.conjTranspose_apply, Matrix.of_apply, star_smul,
    star_trivial, star_one, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  simpa using hG.1.apply x y

private lemma opKernel_posSemidef {X : Type u} {G : Matrix X X ℝ} (hG : G.PosSemidef) :
    (opKernel G).PosSemidef := by
  classical
  refine (RKHS.posSemidef_tfae (K := opKernel G)).out 2 0 |>.mp ?_
  exact ⟨opKernel_isHermitian hG, by
    intro vv
    rw [Finsupp.sum_comm]
    simpa [opKernel, scalarCLM, mul_assoc, mul_comm, mul_left_comm] using hG.2 vv⟩

private lemma rkhs_inner {X : Type u} {G : Matrix X X ℝ} (hG : G.PosSemidef) (x y : X) :
    letI : Fact (opKernel G).PosSemidef := ⟨opKernel_posSemidef hG⟩
    inner ℝ ((RKHS.kerFun (RKHS.OfKernel (opKernel G)) x) (1 : ℝ))
      ((RKHS.kerFun (RKHS.OfKernel (opKernel G)) y) (1 : ℝ)) = G y x := by
  letI : Fact (opKernel G).PosSemidef := ⟨opKernel_posSemidef hG⟩
  let H := RKHS.OfKernel (opKernel G)
  have hxy : RKHS.kernel H y x = opKernel G y x := by
    simp [H]
  have hxy1 : RKHS.kernel H y x (1 : ℝ) = opKernel G y x (1 : ℝ) :=
    congrArg (fun T : ℝ →L[ℝ] ℝ => T (1 : ℝ)) hxy
  calc
    inner ℝ ((RKHS.kerFun H x) (1 : ℝ)) ((RKHS.kerFun H y) (1 : ℝ)) =
        inner ℝ (RKHS.kernel H y x (1 : ℝ)) (1 : ℝ) := by
          rw [RKHS.kernel_inner]
    _ = inner ℝ (opKernel G y x (1 : ℝ)) (1 : ℝ) := by rw [hxy1]
    _ = G y x := by simp [opKernel, scalarCLM]

private lemma centered_inner_dist_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b c : H) :
    inner ℝ (a - c) (a - c) + inner ℝ (b - c) (b - c) -
      2 * inner ℝ (a - c) (b - c) = ‖a - b‖ ^ 2 := by
  have hsub : (a - c) - (b - c) = a - b := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [← real_inner_self_eq_norm_sq (a - b)]
  conv_rhs =>
    rw [← hsub, inner_sub_sub_self]
  rw [real_inner_comm (b - c) (a - c)]
  ring

private lemma distSqPoly_boundedGramPoint_eq_norm_sq
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} {F : Finset X} (hx0 : x0 ∈ F) (hx : x ∈ F) (hy : y ∈ F) :
    distSqPoly x y (boundedGramPoint hK emb x0 F) =
      let e := emb F
      letI : NormedAddCommGroup e.H := e.normed
      ‖e.f ⟨x, hx⟩ - e.f ⟨y, hy⟩‖ ^ 2 := by
  classical
  let e := emb F
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  let a := e.f ⟨x, hx⟩
  let b := e.f ⟨y, hy⟩
  let c := e.f ⟨x0, hx0⟩
  unfold distSqPoly
  rw [gramBoxCoord_boundedGramPoint_of_mem hK emb hx0 hx hx]
  rw [gramBoxCoord_boundedGramPoint_of_mem hK emb hx0 hy hy]
  rw [gramBoxCoord_boundedGramPoint_of_mem hK emb hx0 hx hy]
  rw [finiteCenteredGram_apply_of_mem emb hx0 hx hx]
  rw [finiteCenteredGram_apply_of_mem emb hx0 hy hy]
  rw [finiteCenteredGram_apply_of_mem emb hx0 hx hy]
  change inner ℝ (a - c) (a - c) + inner ℝ (b - c) (b - c) -
      2 * inner ℝ (a - c) (b - c) = ‖a - b‖ ^ 2
  exact centered_inner_dist_sq a b c

private lemma dist_sq_le_of_le_norm {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) :
    a ^ 2 ≤ b ^ 2 := by
  exact sq_le_sq.mpr (by simpa [abs_of_nonneg ha, abs_of_nonneg hb] using h)

private lemma le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  exact (by simpa [abs_of_nonneg ha, abs_of_nonneg hb] using (sq_le_sq.mp h))

private lemma distSqPoly_boundedGramPoint_lower
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} {F : Finset X} (hx0 : x0 ∈ F) (hx : x ∈ F) (hy : y ∈ F) :
    dist x y ^ 2 ≤ distSqPoly x y (boundedGramPoint hK emb x0 F) := by
  let e := emb F
  letI : NormedAddCommGroup e.H := e.normed
  rw [distSqPoly_boundedGramPoint_eq_norm_sq hK emb hx0 hx hy]
  have hle : dist x y ≤ ‖e.f ⟨x, hx⟩ - e.f ⟨y, hy⟩‖ := by
    simpa [e] using e.lower ⟨x, hx⟩ ⟨y, hy⟩
  exact dist_sq_le_of_le_norm dist_nonneg (norm_nonneg _) hle

private lemma distSqPoly_boundedGramPoint_upper
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} {F : Finset X} (hx0 : x0 ∈ F) (hx : x ∈ F) (hy : y ∈ F) :
    distSqPoly x y (boundedGramPoint hK emb x0 F) ≤ (K * dist x y) ^ 2 := by
  let e := emb F
  letI : NormedAddCommGroup e.H := e.normed
  rw [distSqPoly_boundedGramPoint_eq_norm_sq hK emb hx0 hx hy]
  have hle : ‖e.f ⟨x, hx⟩ - e.f ⟨y, hy⟩‖ ≤ K * dist x y := by
    simpa [e] using e.upper ⟨x, hx⟩ ⟨y, hy⟩
  exact dist_sq_le_of_le_norm (norm_nonneg _) (mul_nonneg hK dist_nonneg)
    hle

private noncomputable def limitGramMatrix
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    (x0 : X) : Matrix X X ℝ :=
  let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
  let L : GramBox K x0 := (U.map (boundedGramPoint hK emb x0)).lim
  Matrix.of fun x y => gramBoxCoord x y L

private lemma limitGramMatrix_posSemidef
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    (x0 : X) : (limitGramMatrix hK emb x0).PosSemidef := by
  classical
  let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
  let a : Finset X → GramBox K x0 := boundedGramPoint hK emb x0
  let L : GramBox K x0 := (U.map a).lim
  have hL : L = (U.map (boundedGramPoint hK emb x0)).lim := rfl
  refine ⟨?hermitian, ?nonneg⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    let S : Finset X := insert x0 (insert x (insert y ∅))
    have hEv : ∀ᶠ F in (U : Filter (Finset X)),
        gramBoxCoord x y (a F) = gramBoxCoord y x (a F) := by
      filter_upwards [finiteSuperset_mem_ultrafilterAtTop S] with F hF
      have hx0F : x0 ∈ F := hF (by simp [S])
      have hxF : x ∈ F := hF (by simp [S])
      have hyF : y ∈ F := hF (by simp [S])
      rw [gramBoxCoord_boundedGramPoint_of_mem hK emb hx0F hxF hyF]
      rw [gramBoxCoord_boundedGramPoint_of_mem hK emb hx0F hyF hxF]
      rw [finiteCenteredGram_apply_of_mem emb hx0F hxF hyF]
      rw [finiteCenteredGram_apply_of_mem emb hx0F hyF hxF]
      let e := emb F
      letI : NormedAddCommGroup e.H := e.normed
      letI : InnerProductSpace ℝ e.H := e.inner
      simp [e, real_inner_comm]
    have hlim :
        gramBoxCoord x y L = gramBoxCoord y x L :=
      ultralimit_eq_of_eventually_eq U a (continuous_gramBoxCoord x y)
        (continuous_gramBoxCoord y x) hEv
    change star (gramBoxCoord y x L) = gramBoxCoord x y L
    simp [hlim]
  · intro c
    have hEv : ∀ᶠ F in (U : Filter (Finset X)), 0 ≤ quadPoly c (a F) := by
      let S : Finset X := insert x0 c.support
      filter_upwards [finiteSuperset_mem_ultrafilterAtTop S] with F hF
      have hx0F : x0 ∈ F := hF (by simp [S])
      have hsupp : c.support ⊆ F := by
        intro x hx
        exact hF (by simp [S, hx])
      exact quadPoly_boundedGramPoint_nonneg_of_subset hK emb hx0F hsupp
    have hquad : 0 ≤ quadPoly c L :=
      ultralimit_nonneg_of_eventually_nonneg U a (continuous_quadPoly c) hEv
    simpa [limitGramMatrix, L, a, U, hL, quadPoly, gramBoxCoord, Finsupp.sum,
      mul_assoc, mul_comm, mul_left_comm] using hquad

private lemma limit_distSqPoly_lower
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} :
    let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
    let L : GramBox K x0 := (U.map (boundedGramPoint hK emb x0)).lim
    dist x y ^ 2 ≤ distSqPoly x y L := by
  classical
  let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
  let a : Finset X → GramBox K x0 := boundedGramPoint hK emb x0
  let L : GramBox K x0 := (U.map a).lim
  let S : Finset X := insert x0 (insert x (insert y ∅))
  have hEv : ∀ᶠ F in (U : Filter (Finset X)), dist x y ^ 2 ≤ distSqPoly x y (a F) := by
    filter_upwards [finiteSuperset_mem_ultrafilterAtTop S] with F hF
    have hx0F : x0 ∈ F := hF (by simp [S])
    have hxF : x ∈ F := hF (by simp [S])
    have hyF : y ∈ F := hF (by simp [S])
    exact distSqPoly_boundedGramPoint_lower hK emb hx0F hxF hyF
  exact ultralimit_const_le_of_eventually_const_le U a (continuous_distSqPoly x y) hEv

private lemma limit_distSqPoly_upper
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K)
    {x0 x y : X} :
    let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
    let L : GramBox K x0 := (U.map (boundedGramPoint hK emb x0)).lim
    distSqPoly x y L ≤ (K * dist x y) ^ 2 := by
  classical
  let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
  let a : Finset X → GramBox K x0 := boundedGramPoint hK emb x0
  let L : GramBox K x0 := (U.map a).lim
  let S : Finset X := insert x0 (insert x (insert y ∅))
  have hEv : ∀ᶠ F in (U : Filter (Finset X)), distSqPoly x y (a F) ≤
      (K * dist x y) ^ 2 := by
    filter_upwards [finiteSuperset_mem_ultrafilterAtTop S] with F hF
    have hx0F : x0 ∈ F := hF (by simp [S])
    have hxF : x ∈ F := hF (by simp [S])
    have hyF : y ∈ F := hF (by simp [S])
    exact distSqPoly_boundedGramPoint_upper hK emb hx0F hxF hyF
  exact ultralimit_le_of_eventually_le U a (continuous_distSqPoly x y) hEv

private lemma rkhs_norm_sq_eq_matrix_distSq
    {X : Type u} {G : Matrix X X ℝ} (hG : G.PosSemidef) (x y : X) :
    letI : Fact (opKernel G).PosSemidef := ⟨opKernel_posSemidef hG⟩
    let H := RKHS.OfKernel (opKernel G)
    let f : X → H := fun z => (RKHS.kerFun H z) (1 : ℝ)
    ‖f x - f y‖ ^ 2 = G x x + G y y - 2 * G x y := by
  letI : Fact (opKernel G).PosSemidef := ⟨opKernel_posSemidef hG⟩
  let H := RKHS.OfKernel (opKernel G)
  let f : X → H := fun z => (RKHS.kerFun H z) (1 : ℝ)
  have hsym : G y x = G x y := by
    simpa using hG.1.apply x y
  change ‖f x - f y‖ ^ 2 = G x x + G y y - 2 * G x y
  rw [← real_inner_self_eq_norm_sq (f x - f y)]
  rw [inner_sub_sub_self]
  rw [rkhs_inner hG x x]
  rw [rkhs_inner hG x y]
  rw [rkhs_inner hG y x]
  rw [rkhs_inner hG y y]
  rw [hsym]
  ring

private lemma realEmbedding_of_finite_realEmbeddings
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 0 ≤ K)
    (emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} ↥F K) :
    Nonempty (RealHilbertEmbedding.{u, u} X K) := by
  classical
  by_cases hne : Nonempty X
  · rcases hne with ⟨x0⟩
    let U : Ultrafilter (Finset X) := Ultrafilter.of (Filter.atTop : Filter (Finset X))
    let L : GramBox K x0 := (U.map (boundedGramPoint hK emb x0)).lim
    let G : Matrix X X ℝ := limitGramMatrix hK emb x0
    have hG : G.PosSemidef := limitGramMatrix_posSemidef hK emb x0
    letI : Fact (opKernel G).PosSemidef := ⟨opKernel_posSemidef hG⟩
    let H := RKHS.OfKernel (opKernel G)
    let f : X → H := fun x => (RKHS.kerFun H x) (1 : ℝ)
    have hnormsq (x y : X) :
        ‖f x - f y‖ ^ 2 = distSqPoly x y L := by
      have h := rkhs_norm_sq_eq_matrix_distSq hG x y
      simpa [f, H, G, L, U, limitGramMatrix, distSqPoly] using h
    refine ⟨⟨H, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩⟩
    · intro x y
      have hlim : dist x y ^ 2 ≤ distSqPoly x y L := by
        simpa [L, U] using (limit_distSqPoly_lower hK emb (x0 := x0) (x := x) (y := y))
      have hsq : dist x y ^ 2 ≤ ‖f x - f y‖ ^ 2 := by
        simpa [hnormsq x y] using hlim
      exact le_of_sq_le_sq_of_nonneg dist_nonneg (norm_nonneg _) hsq
    · intro x y
      have hlim : distSqPoly x y L ≤ (K * dist x y) ^ 2 := by
        simpa [L, U] using (limit_distSqPoly_upper hK emb (x0 := x0) (x := x) (y := y))
      have hsq : ‖f x - f y‖ ^ 2 ≤ (K * dist x y) ^ 2 := by
        simpa [hnormsq x y] using hlim
      exact le_of_sq_le_sq_of_nonneg (norm_nonneg _) (mul_nonneg hK dist_nonneg) hsq
  · let H : Type u := PUnit.{u + 1}
    let f : X → H := fun x => False.elim (hne ⟨x⟩)
    refine ⟨⟨H, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩⟩
    · intro x _y
      exact False.elim (hne ⟨x⟩)
    · intro x _y
      exact False.elim (hne ⟨x⟩)

private noncomputable def embeddingGramMatrix
    {X : Type u} [PseudoMetricSpace X] {K : ℝ}
    (e : RealHilbertEmbedding.{u, v} X K) : Matrix (ULift.{w, u} X) (ULift.{w, u} X) ℝ := by
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  exact Matrix.of fun x y => inner ℝ (e.f x.down) (e.f y.down)

private lemma embeddingGramMatrix_posSemidef
    {X : Type u} [PseudoMetricSpace X] {K : ℝ}
    (e : RealHilbertEmbedding.{u, v} X K) :
    (embeddingGramMatrix.{u, v, w} e).PosSemidef := by
  classical
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro x y
    simp [embeddingGramMatrix, real_inner_comm]
  · intro c
    let g : ULift.{w, u} X → e.H := fun x => e.f x.down
    have hnorm :
        (∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * inner ℝ (g x) (g y)) =
          ‖∑ x ∈ c.support, c x • g x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (∑ x ∈ c.support, c x • g x)]
      simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
      simp [real_inner_comm, Finset.mul_sum, mul_comm, mul_left_comm]
    change 0 ≤ ∑ x ∈ c.support, ∑ y ∈ c.support,
      star (c x) * inner ℝ (e.f x.down) (e.f y.down) * c y
    rw [show (∑ x ∈ c.support, ∑ y ∈ c.support,
        star (c x) * inner ℝ (e.f x.down) (e.f y.down) * c y) =
        (∑ x ∈ c.support, ∑ y ∈ c.support,
          c x * c y * inner ℝ (g x) (g y)) by
      simp [g, mul_comm, mul_left_comm]]
    rw [hnorm]
    exact sq_nonneg _

private lemma realEmbedding_retarget
    {X : Type u} [PseudoMetricSpace X] {K : ℝ}
    (e : RealHilbertEmbedding.{u, v} X K) :
    Nonempty (RealHilbertEmbedding.{u, w} X K) := by
  classical
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  let G : Matrix (ULift.{w, u} X) (ULift.{w, u} X) ℝ := embeddingGramMatrix.{u, v, w} e
  have hG : G.PosSemidef := embeddingGramMatrix_posSemidef.{u, v, w} e
  letI : Fact (opKernel G).PosSemidef := ⟨opKernel_posSemidef hG⟩
  let H := RKHS.OfKernel (opKernel G)
  let f : X → H := fun x => (RKHS.kerFun H (ULift.up x : ULift.{w, u} X)) (1 : ℝ)
  have hnormsq (x y : X) : ‖f x - f y‖ ^ 2 = ‖e.f x - e.f y‖ ^ 2 := by
    have hrkhs := rkhs_norm_sq_eq_matrix_distSq hG
      (ULift.up x : ULift.{w, u} X) (ULift.up y : ULift.{w, u} X)
    have horig :
        inner ℝ (e.f x) (e.f x) + inner ℝ (e.f y) (e.f y) -
          2 * inner ℝ (e.f x) (e.f y) = ‖e.f x - e.f y‖ ^ 2 := by
      simpa using centered_inner_dist_sq (e.f x) (e.f y) (0 : e.H)
    calc
      ‖f x - f y‖ ^ 2 =
          G (ULift.up x : ULift.{w, u} X) (ULift.up x : ULift.{w, u} X) +
            G (ULift.up y : ULift.{w, u} X) (ULift.up y : ULift.{w, u} X) -
            2 * G (ULift.up x : ULift.{w, u} X) (ULift.up y : ULift.{w, u} X) := by
        simpa [f, H] using hrkhs
      _ = ‖e.f x - e.f y‖ ^ 2 := by
        simpa [G, embeddingGramMatrix] using horig
  refine ⟨⟨H, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩⟩
  · intro x y
    have hsq₀ : dist x y ^ 2 ≤ ‖e.f x - e.f y‖ ^ 2 :=
      dist_sq_le_of_le_norm dist_nonneg (norm_nonneg _) (e.lower x y)
    have hsq : dist x y ^ 2 ≤ ‖f x - f y‖ ^ 2 := by
      simpa [hnormsq x y] using hsq₀
    exact le_of_sq_le_sq_of_nonneg dist_nonneg (norm_nonneg _) hsq
  · intro x y
    have hKdist : 0 ≤ K * dist x y := le_trans (norm_nonneg _) (e.upper x y)
    have hsq₀ : ‖e.f x - e.f y‖ ^ 2 ≤ (K * dist x y) ^ 2 :=
      dist_sq_le_of_le_norm (norm_nonneg _) hKdist (e.upper x y)
    have hsq : ‖f x - f y‖ ^ 2 ≤ (K * dist x y) ^ 2 := by
      simpa [hnormsq x y] using hsq₀
    exact le_of_sq_le_sq_of_nonneg (norm_nonneg _) hKdist hsq

private lemma hilbertDistortion_le_of_realEmbedding
    {X : Type u} [PseudoMetricSpace X] {K : ℝ} (hK : 1 ≤ K)
    (e : RealHilbertEmbedding.{u, v} X K) :
    hilbertDistortion.{u, v} X ≤ ENNReal.ofReal K := by
  letI : NormedAddCommGroup e.H := e.normed
  letI : InnerProductSpace ℝ e.H := e.inner
  letI : CompleteSpace e.H := e.complete
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  unfold hilbertDistortion
  refine sInf_le ?_
  refine ⟨ENNReal.one_le_ofReal.mpr hK, e.H, e.normed, e.inner, e.complete, e.f, 1,
    by norm_num, ?_⟩
  intro x y
  constructor
  · exact ENNReal.ofReal_le_ofReal (by simpa using e.lower x y)
  · have hupper : ENNReal.ofReal ‖e.f x - e.f y‖ ≤ ENNReal.ofReal (K * dist x y) :=
      ENNReal.ofReal_le_ofReal (e.upper x y)
    rw [ENNReal.ofReal_mul hK0] at hupper
    simpa [one_mul] using hupper

private lemma one_le_hilbertDistortion
    {X : Type u} [PseudoMetricSpace X] : (1 : ENNReal) ≤ hilbertDistortion.{u, v} X := by
  unfold hilbertDistortion
  refine le_sInf ?_
  intro D hD
  exact hD.1

private lemma finite_hilbertDistortion_le_hilbertDistortion
    {X : Type u} [PseudoMetricSpace X] (F : Finset X) :
    hilbertDistortion.{u, v} {x : X // x ∈ F} ≤ hilbertDistortion.{u, v} X := by
  unfold hilbertDistortion
  refine le_sInf ?_
  intro D hD
  rcases hD with ⟨hDone, H, hNorm, hInner, hComplete, f, scale, hscale, hf⟩
  refine sInf_le ?_
  refine ⟨hDone, H, hNorm, hInner, hComplete, (fun x : {x : X // x ∈ F} => f x), scale,
    hscale, ?_⟩
  intro x y
  simpa using hf x y

private lemma iSup_finite_hilbertDistortion_le_hilbertDistortion
    {X : Type u} [PseudoMetricSpace X] :
    iSup (fun F : Finset X => hilbertDistortion.{u, v} {x : X // x ∈ F}) ≤
      hilbertDistortion.{u, v} X := by
  exact iSup_le fun F => finite_hilbertDistortion_le_hilbertDistortion F

private lemma hilbertDistortion_retarget_le
    {X : Type u} [PseudoMetricSpace X] :
    hilbertDistortion.{u, w} X ≤ hilbertDistortion.{u, v} X := by
  classical
  let B : ENNReal := hilbertDistortion.{u, v} X
  have hB1 : (1 : ENNReal) ≤ B := one_le_hilbertDistortion
  change hilbertDistortion.{u, w} X ≤ B
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro C hBC
  by_cases hCtop : C = ⊤
  · rw [hCtop]
    exact le_top
  · let K : ℝ := C.toReal
    have hCeq : ENNReal.ofReal K = C := ENNReal.ofReal_toReal hCtop
    have h1C : (1 : ENNReal) < C := lt_of_le_of_lt hB1 hBC
    have hKgt1 : 1 < K := by
      exact (ENNReal.one_lt_ofReal).mp (by simpa [K, hCeq] using h1C)
    obtain ⟨e⟩ := realEmbedding_of_hilbertDistortion_lt.{u, v} hKgt1
      (by simpa [B, K, hCeq] using hBC)
    obtain ⟨e'⟩ := realEmbedding_retarget.{u, v, w} e
    have hdist : hilbertDistortion.{u, w} X ≤ ENNReal.ofReal K :=
      hilbertDistortion_le_of_realEmbedding hKgt1.le e'
    simpa [K, hCeq] using hdist

private lemma iSup_finite_hilbertDistortion_le_hilbertDistortion_retarget
    {X : Type u} [PseudoMetricSpace X] :
    iSup (fun F : Finset X => hilbertDistortion.{u, v} {x : X // x ∈ F}) ≤
      hilbertDistortion.{u, w} X := by
  refine iSup_le ?_
  intro F
  exact (hilbertDistortion_retarget_le.{u, w, v}
    (X := {x : X // x ∈ F})).trans
    (finite_hilbertDistortion_le_hilbertDistortion.{u, w} F)

private lemma hilbertDistortion_le_iSup_finite_hilbertDistortion
    {X : Type u} [PseudoMetricSpace X] :
    hilbertDistortion.{u, w} X ≤
      iSup (fun F : Finset X => hilbertDistortion.{u, v} {x : X // x ∈ F}) := by
  classical
  let B : ENNReal :=
    iSup (fun F : Finset X => hilbertDistortion.{u, v} {x : X // x ∈ F})
  have hB1 : (1 : ENNReal) ≤ B := by
    exact le_iSup_of_le (∅ : Finset X) one_le_hilbertDistortion
  change hilbertDistortion.{u, w} X ≤ B
  refine le_of_forall_gt_imp_ge_of_dense ?_
  intro C hBC
  by_cases hCtop : C = ⊤
  · rw [hCtop]
    exact le_top
  · let K : ℝ := C.toReal
    have hCeq : ENNReal.ofReal K = C := ENNReal.ofReal_toReal hCtop
    have h1C : (1 : ENNReal) < C := lt_of_le_of_lt hB1 hBC
    have hKgt1 : 1 < K := by
      exact (ENNReal.one_lt_ofReal).mp (by simpa [K, hCeq] using h1C)
    have hfinite : ∀ F : Finset X,
        Nonempty (RealHilbertEmbedding.{u, v} {x : X // x ∈ F} K) := by
      intro F
      refine realEmbedding_of_hilbertDistortion_lt hKgt1 ?_
      have hFleB :
          hilbertDistortion.{u, v} {x : X // x ∈ F} ≤ B := by
        exact le_iSup
          (fun F : Finset X => hilbertDistortion.{u, v} {x : X // x ∈ F}) F
      exact lt_of_le_of_lt hFleB (by simpa [K, hCeq] using hBC)
    let emb : ∀ F : Finset X, RealHilbertEmbedding.{u, v} {x : X // x ∈ F} K :=
      fun F => Classical.choice (hfinite F)
    have hK0 : 0 ≤ K := le_trans zero_le_one hKgt1.le
    obtain ⟨global₀⟩ := realEmbedding_of_finite_realEmbeddings hK0 emb
    obtain ⟨global⟩ := realEmbedding_retarget.{u, u, w} global₀
    have hdist : hilbertDistortion.{u, w} X ≤ ENNReal.ofReal K :=
      hilbertDistortion_le_of_realEmbedding hKgt1.le global
    simpa [K, hCeq] using hdist

private theorem finiteDetermination_max (X : Type u) [PseudoMetricSpace X] :
    hilbertDistortion.{u, w} X =
      iSup (fun F : Finset X => hilbertDistortion.{u, v} {x : X // x ∈ F}) := by
  exact le_antisymm hilbertDistortion_le_iSup_finite_hilbertDistortion
    iSup_finite_hilbertDistortion_le_hilbertDistortion_retarget

/-- Hilbert distortion is determined by finite subsets. -/
theorem finiteDetermination (X : Type*) [PseudoMetricSpace X] :
    hilbertDistortion X =
      iSup (fun F : Finset X => hilbertDistortion {x : X // x ∈ F}) := by
  exact finiteDetermination_max X

end

end SphereObstructionHilbertShiftQuotient
