import SphereObstructionHilbertShiftQuotient.Basic

set_option linter.style.header false

open scoped FourierTransform ENNReal

/-!
Analytic summation input.

This file records the uniform lattice-summation estimate used to analyze the
Gaussian construction.
-/

namespace SphereObstructionHilbertShiftQuotient

noncomputable section

private noncomputable def summationIntegerPoint
    (n : Nat) (k : Fin n -> Int) : RealEuclideanSpace n :=
  WithLp.toLp 2 (fun i : Fin n => (k i : Real))

private noncomputable def complexSchwartz
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) :
    SchwartzMap (RealEuclideanSpace n) ℂ :=
  (SchwartzMap.postcompCLM Complex.ofRealCLM) G

private lemma complexSchwartz_apply
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (x : RealEuclideanSpace n) :
    complexSchwartz n G x = (G x : ℂ) := by
  rfl

private lemma fourier_decay_bound
    (n M : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) :
    ∃ C : Real, 0 < C ∧
      ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C := by
  simpa [norm_iteratedFDeriv_zero] using
    (SchwartzMap.decay (𝓕 (complexSchwartz n G)) M 0)

private lemma summationIntegerPoint_coe
    (n : Nat) (k : Fin n -> Int) :
    ((summationIntegerPoint n k : RealEuclideanSpace n) : Fin n -> Real) =
      fun i => (k i : Real) := by
  rfl

private lemma summationIntegerPoint_eq_zero_iff
    (n : Nat) (k : Fin n -> Int) :
    summationIntegerPoint n k = 0 ↔ k = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) h
    exact Int.cast_eq_zero.mp (by simpa [summationIntegerPoint] using hi)
  · intro h
    subst h
    ext i
    simp [summationIntegerPoint]

@[simp]
private lemma summationIntegerPoint_zero (n : Nat) :
    summationIntegerPoint n 0 = 0 := by
  ext i
  simp [summationIntegerPoint]

@[simp]
private lemma summationIntegerPoint_add
    (n : Nat) (k l : Fin n -> Int) :
    summationIntegerPoint n (k + l) =
      summationIntegerPoint n k + summationIntegerPoint n l := by
  ext i
  simp [summationIntegerPoint]

@[simp]
private lemma summationIntegerPoint_neg
    (n : Nat) (k : Fin n -> Int) :
    summationIntegerPoint n (-k) = -summationIntegerPoint n k := by
  ext i
  simp [summationIntegerPoint]

@[simp]
private lemma summationIntegerPoint_sub
    (n : Nat) (k l : Fin n -> Int) :
    summationIntegerPoint n (k - l) =
      summationIntegerPoint n k - summationIntegerPoint n l := by
  ext i
  simp [summationIntegerPoint, sub_eq_add_neg]

private instance integerPointAddAction (n : Nat) :
    AddAction (Fin n -> Int) (RealEuclideanSpace n) where
  vadd q x := summationIntegerPoint n q + x
  zero_vadd := by
    intro x
    change summationIntegerPoint n 0 + x = x
    simp
  add_vadd := by
    intro q r x
    change summationIntegerPoint n (q + r) + x =
      summationIntegerPoint n q + (summationIntegerPoint n r + x)
    rw [summationIntegerPoint_add]
    abel

private instance integerPointMeasurableConstVAdd (n : Nat) :
    MeasurableConstVAdd (Fin n -> Int) (RealEuclideanSpace n) where
  measurable_const_vadd q := by
    change Measurable fun x : RealEuclideanSpace n => summationIntegerPoint n q + x
    fun_prop

private instance integerPointVAddInvariantMeasure (n : Nat) :
    MeasureTheory.VAddInvariantMeasure (Fin n -> Int) (RealEuclideanSpace n)
      (MeasureTheory.volume : MeasureTheory.Measure (RealEuclideanSpace n)) where
  measure_preimage_vadd q {s} _hs := by
    change MeasureTheory.volume
        ((fun x : RealEuclideanSpace n => summationIntegerPoint n q + x) ⁻¹' s) =
      MeasureTheory.volume s
    exact MeasureTheory.measure_preimage_add MeasureTheory.volume (summationIntegerPoint n q) s

private noncomputable def unitCube (n : Nat) : Set (RealEuclideanSpace n) :=
  {x | ∀ i : Fin n, ((x : RealEuclideanSpace n) : Fin n -> Real) i ∈ Set.Ioc (0 : Real) 1}

private lemma unitCube_nullMeasurable (n : Nat) :
    MeasureTheory.NullMeasurableSet (unitCube n)
      (MeasureTheory.volume : MeasureTheory.Measure (RealEuclideanSpace n)) := by
  have hpi : MeasurableSet
      {x : Fin n -> Real | ∀ i : Fin n, x i ∈ Set.Ioc (0 : Real) 1} :=
    MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  have hpre : MeasurableSet (unitCube n) := by
    simpa [unitCube, RealEuclideanSpace] using
      hpi.preimage
        (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)).continuous.measurable
  exact hpre.nullMeasurableSet

private lemma unitCube_fundamentalDomain (n : Nat) :
    MeasureTheory.IsAddFundamentalDomain (Fin n -> Int) (unitCube n)
      (MeasureTheory.volume : MeasureTheory.Measure (RealEuclideanSpace n)) := by
  classical
  refine MeasureTheory.IsAddFundamentalDomain.mk' (unitCube_nullMeasurable n) ?_
  intro x
  have hcoord :
      ∀ i : Fin n, ∃! z : Int,
        ((x : RealEuclideanSpace n) : Fin n -> Real) i + z • (1 : Real) ∈
          Set.Ioc (0 : Real) (0 + 1) := by
    intro i
    exact existsUnique_add_zsmul_mem_Ioc zero_lt_one
      (((x : RealEuclideanSpace n) : Fin n -> Real) i) 0
  choose q hq hquniq using hcoord
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi := hq i
    simpa [unitCube, summationIntegerPoint, add_comm] using hi
  · intro r hr
    funext i
    exact hquniq i (r i) (by
      have hi := hr i
      simpa [unitCube, summationIntegerPoint, add_comm] using hi)

private noncomputable def piIntegerPoint
    (n : Nat) (k : Fin n -> Int) : Fin n -> Real :=
  fun i => (k i : Real)

private instance piIntegerPointAddAction (n : Nat) :
    AddAction (Fin n -> Int) (Fin n -> Real) where
  vadd q x := piIntegerPoint n q + x
  zero_vadd := by
    intro x
    change piIntegerPoint n 0 + x = x
    funext i
    simp [piIntegerPoint]
  add_vadd := by
    intro q r x
    change piIntegerPoint n (q + r) + x = piIntegerPoint n q + (piIntegerPoint n r + x)
    funext i
    simp [piIntegerPoint, add_comm, add_left_comm, add_assoc]

private instance piIntegerPointMeasurableConstVAdd (n : Nat) :
    MeasurableConstVAdd (Fin n -> Int) (Fin n -> Real) where
  measurable_const_vadd q := by
    change Measurable fun x : Fin n -> Real => piIntegerPoint n q + x
    fun_prop

private instance piIntegerPointVAddInvariantMeasure (n : Nat) :
    MeasureTheory.VAddInvariantMeasure (Fin n -> Int) (Fin n -> Real)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n -> Real)) where
  measure_preimage_vadd q {s} _hs := by
    change MeasureTheory.volume ((fun x : Fin n -> Real => piIntegerPoint n q + x) ⁻¹' s) =
      MeasureTheory.volume s
    exact MeasureTheory.measure_preimage_add MeasureTheory.volume (piIntegerPoint n q) s

private def piUnitCube (n : Nat) : Set (Fin n -> Real) :=
  {x | ∀ i : Fin n, x i ∈ Set.Ioc (0 : Real) 1}

private def piUnitCubeAt (n : Nat) (a : Fin n -> Real) : Set (Fin n -> Real) :=
  {x | ∀ i : Fin n, x i ∈ Set.Ioc (a i) (a i + 1)}

private lemma piUnitCube_nullMeasurable (n : Nat) :
    MeasureTheory.NullMeasurableSet (piUnitCube n)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n -> Real)) := by
  exact (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc).nullMeasurableSet

private lemma piUnitCubeAt_eq_preimage_add (n : Nat) (a : Fin n -> Real) :
    (fun x : Fin n -> Real => x + a) ⁻¹' piUnitCubeAt n a = piUnitCube n := by
  ext x
  simp only [Set.mem_preimage, piUnitCubeAt, piUnitCube, Set.mem_setOf_eq, Set.mem_Ioc,
    Pi.add_apply]
  constructor
  · intro hx i
    have hi := hx i
    constructor <;> linarith
  · intro hx i
    have hi := hx i
    constructor <;> linarith

private lemma piUnitCubeAt_nullMeasurable (n : Nat) (a : Fin n -> Real) :
    MeasureTheory.NullMeasurableSet (piUnitCubeAt n a)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n -> Real)) := by
  exact (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc).nullMeasurableSet

private lemma integral_piUnitCubeAt_eq_integral_add
    (n : Nat) (a : Fin n -> Real) (f : (Fin n -> Real) -> ℂ) :
    ∫ x in piUnitCubeAt n a, f x =
      ∫ x in piUnitCube n, f (x + a) := by
  rw [← MeasureTheory.integral_indicator₀ (piUnitCubeAt_nullMeasurable n a)]
  rw [← MeasureTheory.integral_indicator₀ (piUnitCube_nullMeasurable n)]
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun x : Fin n -> Real => (piUnitCubeAt n a).indicator f x) a]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ piUnitCube n
  · have hx' : x + a ∈ piUnitCubeAt n a := by
      have hxpre : x ∈ (fun x : Fin n -> Real => x + a) ⁻¹' piUnitCubeAt n a := by
        simpa [piUnitCubeAt_eq_preimage_add n a] using hx
      exact hxpre
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · have hx' : x + a ∉ piUnitCubeAt n a := by
      intro hmem
      apply hx
      have hxpre : x ∈ (fun x : Fin n -> Real => x + a) ⁻¹' piUnitCubeAt n a := hmem
      simpa [piUnitCubeAt_eq_preimage_add n a] using hxpre
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

private lemma piUnitCube_fundamentalDomain (n : Nat) :
    MeasureTheory.IsAddFundamentalDomain (Fin n -> Int) (piUnitCube n)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n -> Real)) := by
  classical
  refine MeasureTheory.IsAddFundamentalDomain.mk' (piUnitCube_nullMeasurable n) ?_
  intro x
  have hcoord :
      ∀ i : Fin n, ∃! z : Int, x i + z • (1 : Real) ∈ Set.Ioc (0 : Real) (0 + 1) := by
    intro i
    exact existsUnique_add_zsmul_mem_Ioc zero_lt_one (x i) 0
  choose q hq hquniq using hcoord
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi := hq i
    change (piIntegerPoint n q + x) i ∈ Set.Ioc (0 : Real) 1
    simpa [piIntegerPoint, add_comm] using hi
  · intro r hr
    funext i
    exact hquniq i (r i) (by
      change ∀ i : Fin n, (piIntegerPoint n r + x) i ∈ Set.Ioc (0 : Real) 1 at hr
      have hi := hr i
      simpa [piIntegerPoint, add_comm] using hi)

private noncomputable def torusMk (n : Nat) :
    RealEuclideanSpace n → UnitAddTorus (Fin n) :=
  fun x i => (((x : Fin n → ℝ) i : ℝ) : UnitAddCircle)

private noncomputable def piTorusMk (n : Nat) :
    (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => ((x i : ℝ) : UnitAddCircle)

private lemma piTorusMk_isOpenQuotientMap (n : Nat) :
    IsOpenQuotientMap (piTorusMk n) := by
  unfold piTorusMk
  simpa [Pi.map] using
    (IsOpenQuotientMap.piMap
      (fun _i : Fin n =>
        (QuotientAddGroup.isOpenQuotientMap_mk
          (N := AddSubgroup.zmultiples (1 : ℝ)))))

private lemma torusMk_isOpenQuotientMap (n : Nat) :
    IsOpenQuotientMap (torusMk n) := by
  have hpi : IsOpenQuotientMap (piTorusMk n) := piTorusMk_isOpenQuotientMap n
  have hhome :
      IsOpenQuotientMap (fun x : RealEuclideanSpace n => ((x : Fin n → ℝ))) := by
    simpa [RealEuclideanSpace] using
      (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)).isOpenQuotientMap
  have hcomp := hpi.comp hhome
  simpa [torusMk, piTorusMk, Function.comp_def] using hcomp

private noncomputable def torusRepr
    (n : Nat) (z : UnitAddTorus (Fin n)) : RealEuclideanSpace n :=
  WithLp.toLp 2 (fun i : Fin n => Quotient.out (z i))

private lemma torusMk_torusRepr (n : Nat) (z : UnitAddTorus (Fin n)) :
    torusMk n (torusRepr n z) = z := by
  funext i
  unfold torusMk torusRepr
  change (QuotientAddGroup.mk (Quotient.out (z i)) : UnitAddCircle) = z i
  exact Quotient.out_eq (z i)

private lemma addCircle_eq_iff_exists_int_add {x y : ℝ}
    (h : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    ∃ z : ℤ, y = x + z := by
  change (QuotientAddGroup.mk x :
      ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) = QuotientAddGroup.mk y at h
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h
  rcases h with ⟨z, hz⟩
  use z
  norm_num at hz
  linarith

private lemma torusMk_eq_iff_exists_int_add
    {n : Nat} {x y : RealEuclideanSpace n} (h : torusMk n x = torusMk n y) :
    ∃ q : Fin n → ℤ, y = x + summationIntegerPoint n q := by
  classical
  have hcoord :
      ∀ i : Fin n, ∃ z : ℤ, (y : Fin n → ℝ) i = (x : Fin n → ℝ) i + z := by
    intro i
    exact addCircle_eq_iff_exists_int_add (congr_fun h i)
  choose q hq using hcoord
  refine ⟨q, ?_⟩
  ext i
  simpa [summationIntegerPoint] using hq i

private noncomputable def torusDescend
    (n : Nat) (P : RealEuclideanSpace n → ℂ)
    (hP : Continuous P)
    (hper : ∀ x y, torusMk n x = torusMk n y → P x = P y) :
    C(UnitAddTorus (Fin n), ℂ) where
  toFun z := P (torusRepr n z)
  continuous_toFun := by
    have hq := torusMk_isOpenQuotientMap n
    rw [← hq.continuous_comp_iff]
    convert hP using 1
    funext x
    dsimp [Function.comp_def]
    exact hper _ _ (torusMk_torusRepr n (torusMk n x))

private lemma torusDescend_mk
    (n : Nat) (P : RealEuclideanSpace n → ℂ)
    (hP : Continuous P)
    (hper : ∀ x y, torusMk n x = torusMk n y → P x = P y)
    (x : RealEuclideanSpace n) :
    torusDescend n P hP hper (torusMk n x) = P x := by
  dsimp [torusDescend]
  exact hper _ _ (torusMk_torusRepr n (torusMk n x))

private def finSuccIntEquiv (m : Nat) : (Fin (m + 1) -> Int) ≃ Int × (Fin m -> Int) where
  toFun k := (k 0, fun i => k i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv k := by
    funext i
    cases i using Fin.cases <;> simp
  right_inv p := by
    ext i <;> simp

@[simp]
private lemma finSuccIntEquiv_fst (m : Nat) (k : Fin (m + 1) -> Int) :
    (finSuccIntEquiv m k).1 = k 0 := rfl

@[simp]
private lemma finSuccIntEquiv_snd (m : Nat) (k : Fin (m + 1) -> Int) :
    (finSuccIntEquiv m k).2 = fun i => k i.succ := rfl

@[simp]
private lemma finSuccIntEquiv_symm_zero (m : Nat) (p : Int × (Fin m -> Int)) :
    (finSuccIntEquiv m).symm p 0 = p.1 := by
  rfl

@[simp]
private lemma finSuccIntEquiv_symm_succ
    (m : Nat) (p : Int × (Fin m -> Int)) (i : Fin m) :
    (finSuccIntEquiv m).symm p i.succ = p.2 i := by
  rfl

private noncomputable def euclideanStdBasis (n : Nat) :
    Module.Basis (Fin n) ℝ (RealEuclideanSpace n) :=
  (Pi.basisFun ℝ (Fin n)).map (WithLp.linearEquiv 2 ℝ (Fin n -> ℝ)).symm

private noncomputable def standardIntegerLattice (n : Nat) :
    Submodule ℤ (RealEuclideanSpace n) :=
  Submodule.span ℤ (Set.range (euclideanStdBasis n))

private lemma standardIntegerLattice_finrank (n : Nat) :
    Module.finrank ℤ (standardIntegerLattice n) = n := by
  rw [standardIntegerLattice]
  rw [ZLattice.rank ℝ]
  simp

private lemma summationIntegerPoint_mem_standardIntegerLattice
    (n : Nat) (k : Fin n -> Int) :
    summationIntegerPoint n k ∈ standardIntegerLattice n := by
  classical
  rw [standardIntegerLattice]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨k, ?_⟩
  ext i
  simp [summationIntegerPoint, euclideanStdBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne]
    · simp
    · exact fun h => hj h.symm
  · intro hi
    simp at hi

private lemma summationIntegerPoint_latticeMap_injective (n : Nat) :
    Function.Injective
      (fun k : Fin n -> Int =>
        (⟨summationIntegerPoint n k,
          summationIntegerPoint_mem_standardIntegerLattice n k⟩ : standardIntegerLattice n)) := by
  intro k l h
  funext i
  have hp : summationIntegerPoint n k = summationIntegerPoint n l := congrArg Subtype.val h
  have hi := congrArg (fun x : RealEuclideanSpace n => (x : Fin n -> Real) i) hp
  exact Int.cast_injective (by simpa [summationIntegerPoint] using hi)

private lemma finite_integerPoint_norm_le (n : Nat) (A : ℝ) :
    Set.Finite {k : Fin n -> Int | ‖summationIntegerPoint n k‖ ≤ A} := by
  let i : (Fin n -> Int) -> standardIntegerLattice n := fun k =>
    ⟨summationIntegerPoint n k, summationIntegerPoint_mem_standardIntegerLattice n k⟩
  have hi : Function.Injective i := summationIntegerPoint_latticeMap_injective n
  refine Set.Finite.of_finite_image (f := i) ?_ hi.injOn
  have hfiniteTarget : Set.Finite
      {z : standardIntegerLattice n | ‖(z : RealEuclideanSpace n)‖ ≤ A} := by
    haveI : DiscreteTopology (standardIntegerLattice n) := by
      change DiscreteTopology (Submodule.span ℤ (Set.range (euclideanStdBasis n)))
      infer_instance
    by_cases hA : A < 0
    · rw [show {z : standardIntegerLattice n | ‖(z : RealEuclideanSpace n)‖ ≤ A} = ∅ by
        ext z
        simp [not_le.mpr (lt_of_lt_of_le hA (norm_nonneg (z : RealEuclideanSpace n)))]]
      exact Set.finite_empty
    · have hclosed : IsClosed (standardIntegerLattice n : Set (RealEuclideanSpace n)) := by
        exact @AddSubgroup.isClosed_of_discrete (RealEuclideanSpace n) _ _ _ _
          (standardIntegerLattice n).toAddSubgroup inferInstance
      have hfiniteInter : Set.Finite
          (Metric.closedBall (0 : RealEuclideanSpace n) A ∩
            (standardIntegerLattice n : Set (RealEuclideanSpace n))) := by
        exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
          Metric.isBounded_closedBall hclosed
      refine Set.Finite.of_finite_image
        (f := fun z : standardIntegerLattice n => (z : RealEuclideanSpace n)) ?_
        Subtype.val_injective.injOn
      refine hfiniteInter.subset ?_
      rintro y ⟨z, hz, rfl⟩
      exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, z.2⟩
  refine hfiniteTarget.subset ?_
  rintro z ⟨k, hk, rfl⟩
  exact hk

private lemma summable_integerPoint_norm_inv_pow {n M : Nat} (hM : n < M) :
    Summable fun k : Fin n -> Int => ‖summationIntegerPoint n k‖⁻¹ ^ M := by
  haveI : DiscreteTopology (standardIntegerLattice n) := by
    change DiscreteTopology (Submodule.span ℤ (Set.range (euclideanStdBasis n)))
    infer_instance
  have hrank : Module.finrank ℤ (standardIntegerLattice n) < M := by
    simpa [standardIntegerLattice_finrank n] using hM
  have hsL : Summable fun z : standardIntegerLattice n =>
      ‖(z : RealEuclideanSpace n)‖⁻¹ ^ M := by
    exact ZLattice.summable_norm_pow_inv (standardIntegerLattice n) M hrank
  let i : (Fin n -> Int) -> standardIntegerLattice n := fun k =>
    ⟨summationIntegerPoint n k, summationIntegerPoint_mem_standardIntegerLattice n k⟩
  have hi : Function.Injective i := summationIntegerPoint_latticeMap_injective n
  simpa [i] using hsL.comp_injective hi

private lemma summable_ne_zero_integerPoint_norm_inv_pow {n M : Nat} (hM : n < M) :
    Summable fun k : {k : Fin n -> Int // k ≠ 0} =>
      ‖summationIntegerPoint n k.1‖⁻¹ ^ M := by
  simpa [Function.comp_def] using
    (summable_integerPoint_norm_inv_pow (n := n) (M := M) hM).subtype (fun k => k ≠ 0)

private noncomputable def complexPeriodizedSum
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c x : RealEuclideanSpace n) : ℂ :=
  ((R ^ n)⁻¹ : ℂ) *
    ∑' k : Fin n -> Int,
      (complexSchwartz n G) ((R⁻¹ : Real) • (x + summationIntegerPoint n k - c))

private noncomputable def complexPeriodizedSummand
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) (k : Fin n -> Int) :
    C(RealEuclideanSpace n, ℂ) where
  toFun x :=
    ((R ^ n)⁻¹ : ℂ) *
      (complexSchwartz n G) ((R⁻¹ : Real) • (x + summationIntegerPoint n k - c))
  continuous_toFun := by
    fun_prop

@[simp]
private lemma complexPeriodizedSummand_apply
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c x : RealEuclideanSpace n) (k : Fin n -> Int) :
    complexPeriodizedSummand n G R c k x =
      ((R ^ n)⁻¹ : ℂ) *
        (complexSchwartz n G) ((R⁻¹ : Real) • (x + summationIntegerPoint n k - c)) := by
  rfl

private lemma complexPeriodizedSum_periodic
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c x : RealEuclideanSpace n) (q : Fin n -> Int) :
    complexPeriodizedSum n G R c (x + summationIntegerPoint n q) =
      complexPeriodizedSum n G R c x := by
  unfold complexPeriodizedSum
  congr 1
  let e : (Fin n -> Int) ≃ (Fin n -> Int) := Equiv.addRight q
  calc
    (∑' k : Fin n -> Int,
        (complexSchwartz n G)
          ((R⁻¹ : Real) • (x + summationIntegerPoint n q +
            summationIntegerPoint n k - c)))
        = ∑' k : Fin n -> Int,
            (complexSchwartz n G)
              ((R⁻¹ : Real) • (x + summationIntegerPoint n (k + q) - c)) := by
          congr with k
          congr 2
          rw [summationIntegerPoint_add]
          abel
    _ = ∑' k : Fin n -> Int,
        (complexSchwartz n G) ((R⁻¹ : Real) • (x + summationIntegerPoint n k - c)) := by
          simpa [e, add_comm] using
            (e.tsum_eq fun k : Fin n -> Int =>
              (complexSchwartz n G)
                ((R⁻¹ : Real) • (x + summationIntegerPoint n k - c)))

private lemma complexPeriodizedSum_respects_torus
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) :
    ∀ x y, torusMk n x = torusMk n y →
      complexPeriodizedSum n G R c x = complexPeriodizedSum n G R c y := by
  intro x y hxy
  rcases torusMk_eq_iff_exists_int_add hxy with ⟨q, rfl⟩
  exact (complexPeriodizedSum_periodic n G R c x q).symm

private lemma complexPeriodizedSummand_summable
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) :
    Summable fun k : Fin n -> Int => complexPeriodizedSummand n G R c k := by
  classical
  refine ContinuousMap.summable_of_locally_summable_norm ?_
  intro K
  let M : Nat := n + 1
  have hM : n < M := by
    dsimp [M]
    omega
  obtain ⟨C, hCpos, hCraw⟩ := (complexSchwartz n G).decay M 0
  have hC : ∀ x : RealEuclideanSpace n,
      x ≠ 0 → ‖(complexSchwartz n G) x‖ ≤ C / ‖x‖ ^ M := by
    intro x hx
    have hxpos : 0 < ‖x‖ ^ M := pow_pos (norm_pos_iff.mpr hx) M
    rw [le_div_iff₀ hxpos]
    simpa [norm_iteratedFDeriv_zero, mul_comm] using hCraw x
  obtain ⟨r, _hrpos, hr⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 (0 : RealEuclideanSpace n)
  let B : Real := r + ‖c‖
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  let D : Real := ‖((R ^ n)⁻¹ : ℂ)‖ * C * (2 * R) ^ M
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hs : Summable fun k : Fin n -> Int =>
      D * ‖summationIntegerPoint n k‖⁻¹ ^ M :=
    Summable.mul_left D (summable_integerPoint_norm_inv_pow (n := n) (M := M) hM)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(finite_integerPoint_norm_le n (2 * B)).compl_mem_cofinite] with k hk
  rw [norm_norm]
  refine (ContinuousMap.norm_le _ ?_).mpr ?_
  · exact mul_nonneg hDnonneg (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) M)
  intro x
  have hxK : (x : RealEuclideanSpace n) ∈ (K : Set (RealEuclideanSpace n)) := x.2
  have hxnorm : ‖(x : RealEuclideanSpace n)‖ ≤ r := by
    have hxball := hr hxK
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
  have hxc : ‖(x : RealEuclideanSpace n) - c‖ ≤ B := by
    calc
      ‖(x : RealEuclideanSpace n) - c‖ ≤ ‖(x : RealEuclideanSpace n)‖ + ‖c‖ :=
        norm_sub_le _ _
      _ ≤ r + ‖c‖ := by gcongr
      _ = B := rfl
  have hlarge : 2 * B < ‖summationIntegerPoint n k‖ := by
    exact not_le.mp hk
  have hp_half :
      ‖summationIntegerPoint n k‖ / 2 ≤
        ‖summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)‖ := by
    have htri :
        ‖summationIntegerPoint n k‖ ≤
          ‖summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)‖ +
            ‖(x : RealEuclideanSpace n) - c‖ := by
      calc
        ‖summationIntegerPoint n k‖ =
            ‖(summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)) +
              (-((x : RealEuclideanSpace n) - c))‖ := by
              congr 1
              abel
        _ ≤ ‖summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)‖ +
            ‖-((x : RealEuclideanSpace n) - c)‖ :=
          norm_add_le _ _
        _ = ‖summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)‖ +
            ‖(x : RealEuclideanSpace n) - c‖ := by
          rw [norm_neg]
    have : ‖summationIntegerPoint n k‖ ≤
        ‖summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)‖ + B :=
      htri.trans (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hxc
            ‖summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c)‖)
    linarith
  have harg :
      ‖summationIntegerPoint n k‖ / (2 * R) ≤
        ‖(R⁻¹ : Real) •
          ((x : RealEuclideanSpace n) + summationIntegerPoint n k - c)‖ := by
    have hrewrite :
        (x : RealEuclideanSpace n) + summationIntegerPoint n k - c =
          summationIntegerPoint n k + ((x : RealEuclideanSpace n) - c) := by
      abel
    rw [hrewrite, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    have hmul := mul_le_mul_of_nonneg_right hp_half (inv_nonneg.mpr hR.le)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have harg_ne :
      (R⁻¹ : Real) • ((x : RealEuclideanSpace n) + summationIntegerPoint n k - c) ≠ 0 := by
    intro hzero
    have hpos : 0 < ‖summationIntegerPoint n k‖ / (2 * R) := by
      have hp_pos : 0 < ‖summationIntegerPoint n k‖ := by linarith [hlarge, hBnonneg]
      positivity
    rw [hzero, norm_zero] at harg
    linarith
  calc
    ‖complexPeriodizedSummand n G R c k x‖
        = ‖((R ^ n)⁻¹ : ℂ)‖ *
            ‖(complexSchwartz n G)
              ((R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
                summationIntegerPoint n k - c))‖ := by
          simp [norm_mul]
    _ ≤ ‖((R ^ n)⁻¹ : ℂ)‖ *
        (C / ‖(R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
          summationIntegerPoint n k - c)‖ ^ M) := by
          gcongr
          exact hC _ harg_ne
    _ ≤ D * ‖summationIntegerPoint n k‖⁻¹ ^ M := by
      have hp_pos : 0 < ‖summationIntegerPoint n k‖ := by linarith [hlarge, hBnonneg]
      have hbase_pos : 0 < ‖summationIntegerPoint n k‖ / (2 * R) := by
        positivity
      have hinv_le : ‖(R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
            summationIntegerPoint n k - c)‖⁻¹ ≤
          (‖summationIntegerPoint n k‖ / (2 * R))⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hbase_pos harg
      have hinv_pow :
          ‖(R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
            summationIntegerPoint n k - c)‖⁻¹ ^ M ≤
          ((2 * R) ^ M) * ‖summationIntegerPoint n k‖⁻¹ ^ M := by
        calc
          ‖(R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
              summationIntegerPoint n k - c)‖⁻¹ ^ M
              ≤ (‖summationIntegerPoint n k‖ / (2 * R))⁻¹ ^ M := by
                exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hinv_le M
          _ = ((2 * R) ^ M) * ‖summationIntegerPoint n k‖⁻¹ ^ M := by
                field_simp [div_eq_mul_inv]
                ring
      have hmulC : C *
            (‖(R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
              summationIntegerPoint n k - c)‖⁻¹ ^ M) ≤
          C * (((2 * R) ^ M) * ‖summationIntegerPoint n k‖⁻¹ ^ M) := by
        exact mul_le_mul_of_nonneg_left hinv_pow hCpos.le
      have hmulA : ‖((R ^ n)⁻¹ : ℂ)‖ *
            (C * (‖(R⁻¹ : Real) • ((x : RealEuclideanSpace n) +
              summationIntegerPoint n k - c)‖⁻¹ ^ M)) ≤
          ‖((R ^ n)⁻¹ : ℂ)‖ *
            (C * (((2 * R) ^ M) * ‖summationIntegerPoint n k‖⁻¹ ^ M)) := by
        exact mul_le_mul_of_nonneg_left hmulC (norm_nonneg _)
      dsimp [D]
      rw [div_eq_mul_inv, inv_pow]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmulA

private noncomputable def complexPeriodizedMap
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) :
    C(RealEuclideanSpace n, ℂ) :=
  ∑' k : Fin n -> Int, complexPeriodizedSummand n G R c k

private lemma complexPeriodizedMap_apply
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c x : RealEuclideanSpace n) :
    complexPeriodizedMap n G hR c x = complexPeriodizedSum n G R c x := by
  unfold complexPeriodizedMap complexPeriodizedSum
  rw [← ContinuousMap.tsum_apply (complexPeriodizedSummand_summable n G hR c)]
  simp_rw [complexPeriodizedSummand_apply]
  rw [tsum_mul_left]

private lemma complexPeriodizedSum_continuous
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) :
    Continuous (complexPeriodizedSum n G R c) := by
  convert (complexPeriodizedMap n G hR c).continuous using 1
  funext x
  exact (complexPeriodizedMap_apply n G hR c x).symm

private noncomputable def periodizedTorus
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) :
    C(UnitAddTorus (Fin n), ℂ) :=
  torusDescend n (complexPeriodizedSum n G R c)
    (complexPeriodizedSum_continuous n G hR c)
    (complexPeriodizedSum_respects_torus n G R c)

private lemma periodizedTorus_mk
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c x : RealEuclideanSpace n) :
    periodizedTorus n G hR c (torusMk n x) = complexPeriodizedSum n G R c x := by
  exact torusDescend_mk n (complexPeriodizedSum n G R c)
    (complexPeriodizedSum_continuous n G hR c)
    (complexPeriodizedSum_respects_torus n G R c) x

private lemma periodizedTorus_apply_pi
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) (x : Fin n -> Real) :
    periodizedTorus n G hR c (fun i : Fin n => ((x i : Real) : UnitAddCircle)) =
      complexPeriodizedSum n G R c (WithLp.toLp 2 x) := by
  have hmk : (fun i : Fin n => ((x i : Real) : UnitAddCircle)) =
      torusMk n (WithLp.toLp 2 x) := by
    rfl
  rw [hmk, periodizedTorus_mk]

private lemma periodizedTorus_piTorusMk
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) (x : Fin n -> Real) :
    periodizedTorus n G hR c (piTorusMk n x) =
      complexPeriodizedSum n G R c (WithLp.toLp 2 x) := by
  change periodizedTorus n G hR c (fun i : Fin n => ((x i : Real) : UnitAddCircle)) =
    complexPeriodizedSum n G R c (WithLp.toLp 2 x)
  exact periodizedTorus_apply_pi n G hR c x

private lemma fourier_arg_add (m : Int) (x y : UnitAddCircle) :
    fourier m (x + y) = fourier m x * fourier m y := by
  rw [fourier_apply, zsmul_add, AddCircle.toCircle_add]
  rfl

private noncomputable def piMFourier
    (n : Nat) (m : Fin n -> Int) (x : Fin n -> Real) : ℂ :=
  UnitAddTorus.mFourier m (fun i : Fin n => ((x i : Real) : UnitAddCircle))

private lemma piMFourier_continuous
    (n : Nat) (m : Fin n -> Int) :
    Continuous (piMFourier n m) := by
  unfold piMFourier
  fun_prop

private lemma piMFourier_add
    (n : Nat) (m : Fin n -> Int) (x a : Fin n -> Real) :
    piMFourier n m (x + a) = piMFourier n m x * piMFourier n m a := by
  simp only [piMFourier, UnitAddTorus.mFourier, Pi.add_apply, ContinuousMap.coe_mk]
  simp_rw [show ∀ i : Fin n, (((x i + a i : Real) : UnitAddCircle)) =
      ((x i : Real) : UnitAddCircle) + ((a i : Real) : UnitAddCircle) by
    intro i
    rfl]
  simp_rw [fourier_arg_add]
  rw [Finset.prod_mul_distrib]

private lemma piMFourier_int_add
    (n : Nat) (m q : Fin n -> Int) (x : Fin n -> Real) :
    piMFourier n m (x + piIntegerPoint n q) = piMFourier n m x := by
  simp [piMFourier, UnitAddTorus.mFourier, piIntegerPoint]

private lemma mFourier_torusMk_eq_exp
    (n : Nat) (m : Fin n -> Int) (y : RealEuclideanSpace n) :
    UnitAddTorus.mFourier (-m) (torusMk n y) =
      Complex.exp (((-2 * Real.pi * inner ℝ y (summationIntegerPoint n m) : Real) : ℂ) *
        Complex.I) := by
  simp [UnitAddTorus.mFourier, torusMk, summationIntegerPoint, PiLp.inner_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [← map_prod]
  simp_rw [← Complex.exp_sum]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_sum, map_mul, map_ofNat, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  simp_rw [mul_neg, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring_nf

private lemma scaled_fourier_integral_eq
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (m : Fin n -> Int) :
    ((R ^ n)⁻¹ : ℂ) * ∫ y : RealEuclideanSpace n,
      UnitAddTorus.mFourier (-m) (torusMk n y) *
        (complexSchwartz n G) ((R⁻¹ : Real) • y) =
      (𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n m) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  let F : RealEuclideanSpace n → ℂ := fun y =>
    Complex.exp (((-2 * Real.pi * inner ℝ y (R • summationIntegerPoint n m) : Real) : ℂ) *
      Complex.I) * (complexSchwartz n G) y
  have hscale :=
    MeasureTheory.Measure.integral_comp_smul (MeasureTheory.volume) F (R⁻¹ : Real)
  have hleft :
      (∫ (y : RealEuclideanSpace n),
        (UnitAddTorus.mFourier (-m)) (torusMk n y) * (complexSchwartz n G) (R⁻¹ • y)) =
      ∫ (y : RealEuclideanSpace n), F (R⁻¹ • y) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    dsimp [F]
    rw [mFourier_torusMk_eq_exp]
    congr 1
    congr 1
    congr 1
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp [hR.ne']
  rw [hleft, hscale]
  have hfin : Module.finrank ℝ (RealEuclideanSpace n) = n := by
    simp [RealEuclideanSpace]
  rw [hfin]
  have hJac : |(R⁻¹ ^ n)⁻¹| = R ^ n := by
    rw [inv_pow, inv_inv, abs_of_pos]
    exact pow_pos hR n
  rw [hJac]
  simp [Complex.real_smul, hR.ne']
  field_simp [pow_ne_zero n hR.ne']
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  dsimp [F]
  congr 1
  norm_num

@[simp]
private lemma mFourier_apply_norm
    (n : Nat) (m : Fin n -> Int) (x : UnitAddTorus (Fin n)) :
    ‖UnitAddTorus.mFourier m x‖ = 1 := by
  simp [UnitAddTorus.mFourier]

@[simp]
private lemma mFourier_torusMk_zero
    (n : Nat) (m : Fin n -> Int) :
    UnitAddTorus.mFourier m (torusMk n 0) = 1 := by
  simp [UnitAddTorus.mFourier, torusMk]

private lemma piUnitCubeAt_volume (n : Nat) (a : Fin n -> Real) :
    (MeasureTheory.volume : MeasureTheory.Measure (Fin n -> Real)) (piUnitCubeAt n a) = 1 := by
  rw [show piUnitCubeAt n a =
      Set.pi Set.univ (fun i : Fin n => Set.Ioc (a i) (a i + 1)) by
    ext x
    simp [piUnitCubeAt]]
  rw [Real.volume_pi_Ioc]
  simp

private lemma pi_scaled_complexSchwartz_integrable
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) :
    MeasureTheory.Integrable
      (fun y : Fin n -> Real =>
        (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)) := by
  let F : RealEuclideanSpace n → ℂ := fun y =>
    (complexSchwartz n G) ((R⁻¹ : Real) • y)
  have hF : MeasureTheory.Integrable F := by
    have hbase : MeasureTheory.Integrable
        (fun y : RealEuclideanSpace n => (complexSchwartz n G) y) :=
      (complexSchwartz n G).integrable
    simpa [F] using MeasureTheory.Integrable.comp_smul hbase (inv_ne_zero hR.ne')
  simpa [F, Function.comp_def] using
    ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n -> Real)).measurableEmbedding).2 hF

private lemma pi_fourier_integrand_integrable
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (m : Fin n -> Int) :
    MeasureTheory.Integrable
      (fun y : Fin n -> Real => piMFourier n (-m) y *
        (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)) := by
  have hscaled := pi_scaled_complexSchwartz_integrable n G hR
  refine hscaled.norm.mono' ?_ ?_
  · exact ((piMFourier_continuous n (-m)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with y
    calc
      ‖piMFourier n (-m) y *
          (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)‖
          = ‖(complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)‖ := by
            simp [piMFourier, norm_mul]
      _ ≤ ‖(complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)‖ := le_rfl

private lemma pi_integral_tsum_vadd_eq_integral
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (m : Fin n -> Int) :
    (∫ x in piUnitCube n,
      (∑' k : Fin n -> Int,
        piMFourier n (-m) (piIntegerPoint n k + x) *
          (complexSchwartz n G)
            ((R⁻¹ : Real) • WithLp.toLp 2 (piIntegerPoint n k + x)))) =
      ∫ y : Fin n -> Real,
        piMFourier n (-m) y *
          (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y) := by
  let H : (Fin n -> Real) -> ℂ := fun y =>
    piMFourier n (-m) y *
      (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)
  have hH : MeasureTheory.Integrable H :=
    pi_fourier_integrand_integrable n G hR m
  change (∫ x in piUnitCube n,
      (∑' k : Fin n -> Int, H (piIntegerPoint n k + x))) = ∫ y, H y
  rw [MeasureTheory.integral_tsum]
  · exact ((piUnitCube_fundamentalDomain n).integral_eq_tsum'' H hH).symm
  · intro k
    exact (hH.1.comp_quasiMeasurePreserving
      (MeasureTheory.measurePreserving_vadd k
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n -> Real))).quasiMeasurePreserving).restrict
  · change (∑' i : Fin n -> Int,
      (∫⁻ (a : Fin n -> Real) in piUnitCube n, ‖H (i +ᵥ a)‖ₑ)) ≠ ∞
    rw [← (piUnitCube_fundamentalDomain n).lintegral_eq_tsum'' (fun y => ‖H y‖ₑ)]
    exact ne_of_lt hH.2

private lemma pi_periodized_integral_eq_fourier_integral
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (m : Fin n -> Int) :
    (∫ x in piUnitCube n,
      piMFourier n (-m) x *
        (∑' k : Fin n -> Int,
          (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k)))) =
      ∫ y : Fin n -> Real,
        piMFourier n (-m) y *
          (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y) := by
  calc
    (∫ x in piUnitCube n,
      piMFourier n (-m) x *
        (∑' k : Fin n -> Int,
          (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k))))
        = ∫ x in piUnitCube n,
          (∑' k : Fin n -> Int,
            piMFourier n (-m) x *
              (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [tsum_mul_left]
    _ = ∫ x in piUnitCube n,
        (∑' k : Fin n -> Int,
          piMFourier n (-m) (piIntegerPoint n k + x) *
            (complexSchwartz n G)
              ((R⁻¹ : Real) • WithLp.toLp 2 (piIntegerPoint n k + x))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          congr with k
          congr 1
          · rw [show piIntegerPoint n k + x = x + piIntegerPoint n k by
              funext i
              simp [add_comm]]
            exact (piMFourier_int_add n (-m) k x).symm
          · congr 2
            ext i
            simp [piIntegerPoint, add_comm]
    _ = ∫ y : Fin n -> Real,
        piMFourier n (-m) y *
          (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y) :=
          pi_integral_tsum_vadd_eq_integral n G hR m

private lemma shifted_periodized_cube_integral_eq
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) (m : Fin n -> Int) :
    (∫ x in piUnitCube n,
      piMFourier n (-m) (x + (c : Fin n -> Real)) *
        complexPeriodizedSum n G R c (WithLp.toLp 2 (x + (c : Fin n -> Real)))) =
      piMFourier n (-m) (c : Fin n -> Real) *
        (((R ^ n)⁻¹ : ℂ) *
          ∫ x in piUnitCube n,
            piMFourier n (-m) x *
              (∑' k : Fin n -> Int,
                (complexSchwartz n G)
                  ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k)))) := by
  unfold complexPeriodizedSum
  calc
    (∫ x in piUnitCube n,
      piMFourier n (-m) (x + (c : Fin n -> Real)) *
        (((R ^ n)⁻¹ : ℂ) *
          (∑' k : Fin n -> Int,
            (complexSchwartz n G)
              ((R⁻¹ : Real) •
                (WithLp.toLp 2 (x + (c : Fin n -> Real)) +
                  summationIntegerPoint n k - c)))))
        = ∫ x in piUnitCube n,
            piMFourier n (-m) (c : Fin n -> Real) *
              (((R ^ n)⁻¹ : ℂ) *
                (piMFourier n (-m) x *
                  (∑' k : Fin n -> Int,
                    (complexSchwartz n G)
                      ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k))))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          have hsum :
              (∑' k : Fin n -> Int,
                (complexSchwartz n G)
                  ((R⁻¹ : Real) •
                    (WithLp.toLp 2 (x + (c : Fin n -> Real)) +
                      summationIntegerPoint n k - c))) =
              ∑' k : Fin n -> Int,
                (complexSchwartz n G)
                  ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k)) := by
            congr with k
            congr 2
            ext i
            simp [summationIntegerPoint, piIntegerPoint]
            ring
          rw [hsum, piMFourier_add]
          ring
    _ = piMFourier n (-m) (c : Fin n -> Real) *
        (((R ^ n)⁻¹ : ℂ) *
          ∫ x in piUnitCube n,
            piMFourier n (-m) x *
              (∑' k : Fin n -> Int,
                (complexSchwartz n G)
                  ((R⁻¹ : Real) • WithLp.toLp 2 (x + piIntegerPoint n k)))) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

private lemma pi_fourier_integral_eq_real
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (m : Fin n -> Int) :
    (∫ y : Fin n -> Real,
      piMFourier n (-m) y *
        (complexSchwartz n G) ((R⁻¹ : Real) • WithLp.toLp 2 y)) =
      ∫ y : RealEuclideanSpace n,
        UnitAddTorus.mFourier (-m) (torusMk n y) *
          (complexSchwartz n G) ((R⁻¹ : Real) • y) := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n -> Real)).measurableEmbedding]
  rfl

private lemma periodizedTorus_fourierCoeff
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 0 < R) (c : RealEuclideanSpace n) (m : Fin n -> Int) :
    UnitAddTorus.mFourierCoeff (periodizedTorus n G hR c) m =
      UnitAddTorus.mFourier (-m) (torusMk n c) *
        (𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n m) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral
    (periodizedTorus n G hR c) m (fun i : Fin n => (c : Fin n -> Real) i)]
  change (∫ x in piUnitCubeAt n (c : Fin n -> Real),
      piMFourier n (-m) x * periodizedTorus n G hR c (piTorusMk n x)) =
    UnitAddTorus.mFourier (-m) (torusMk n c) *
      (𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n m)
  rw [integral_piUnitCubeAt_eq_integral_add]
  simp_rw [periodizedTorus_piTorusMk]
  rw [shifted_periodized_cube_integral_eq]
  have hphase :
      piMFourier n (-m) (c : Fin n -> Real) =
        UnitAddTorus.mFourier (-m) (torusMk n c) := rfl
  rw [hphase]
  rw [pi_periodized_integral_eq_fourier_integral n G hR m]
  rw [pi_fourier_integral_eq_real]
  rw [scaled_fourier_integral_eq n G hR m]

/-- The scaled lattice sum associated to a test function. -/
noncomputable def scaledLatticeSum
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) : Real :=
  (R ^ n)⁻¹ * ∑' k : Fin n -> Int, G ((R⁻¹ : Real) • (summationIntegerPoint n k - c))

/-- The Euclidean integral of a test function. -/
noncomputable def euclideanIntegral
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) : Real :=
  ∫ x : RealEuclideanSpace n, G x

private lemma complexPeriodizedSum_zero_eq_scaledLatticeSum
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    (R : Real) (c : RealEuclideanSpace n) :
    complexPeriodizedSum n G R c 0 = (scaledLatticeSum n G R c : ℂ) := by
  unfold complexPeriodizedSum scaledLatticeSum
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 1
  · simp
  · congr with k
    simp [complexSchwartz_apply]

private lemma fourier_complexSchwartz_zero
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) :
    (𝓕 (complexSchwartz n G)) (0 : RealEuclideanSpace n) =
      (euclideanIntegral n G : ℂ) := by
  rw [SchwartzMap.fourier_coe]
  rw [Real.fourier_eq']
  simp only [inner_zero_right, MulZeroClass.mul_zero, Complex.ofReal_zero]
  simpa [complexSchwartz, euclideanIntegral] using
    (integral_ofReal (f := fun x : RealEuclideanSpace n => G x) (𝕜 := ℂ))

private lemma fourier_norm_le_of_decay
    {n M : Nat} {G : SchwartzMap (RealEuclideanSpace n) Real} {C : Real}
    (hC : ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C)
    {ξ : RealEuclideanSpace n} (hξ : ξ ≠ 0) :
    ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C / ‖ξ‖ ^ M := by
  have hpos : 0 < ‖ξ‖ ^ M := pow_pos (norm_pos_iff.mpr hξ) M
  rw [le_div_iff₀ hpos]
  simpa [mul_comm] using hC ξ

private lemma fourier_norm_smul_integerPoint_le
    {n M : Nat} {G : SchwartzMap (RealEuclideanSpace n) Real} {C R : Real}
    (hC : ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C)
    (hR : 1 ≤ R) {k : Fin n -> Int} (hk : k ≠ 0) :
    ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k)‖ ≤
      C / (R ^ M * ‖summationIntegerPoint n k‖ ^ M) := by
  have hRpos : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
  have hp : summationIntegerPoint n k ≠ 0 := by
    intro hp0
    exact hk ((summationIntegerPoint_eq_zero_iff n k).mp hp0)
  have hsmul : R • summationIntegerPoint n k ≠ 0 := smul_ne_zero hRpos hp
  have h := fourier_norm_le_of_decay hC hsmul
  convert h using 2
  rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one hR), mul_pow]

private lemma fourier_norm_smul_integerPoint_le_inv
    {n M : Nat} {G : SchwartzMap (RealEuclideanSpace n) Real} {C R : Real}
    (hC : ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C)
    (hR : 1 ≤ R) {k : Fin n -> Int} (hk : k ≠ 0) :
    ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k)‖ ≤
      (C / R ^ M) * ‖summationIntegerPoint n k‖⁻¹ ^ M := by
  calc
    ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k)‖
        ≤ C / (R ^ M * ‖summationIntegerPoint n k‖ ^ M) :=
      fourier_norm_smul_integerPoint_le hC hR hk
    _ = (C / R ^ M) * ‖summationIntegerPoint n k‖⁻¹ ^ M := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_pow]
      ring

private lemma fourier_tail_norm_summable
    {n M : Nat} {G : SchwartzMap (RealEuclideanSpace n) Real} {C R : Real}
    (hM : n < M)
    (hC : ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C)
    (hR : 1 ≤ R) :
    Summable fun k : {k : Fin n -> Int // k ≠ 0} =>
      ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖ := by
  have hs : Summable fun k : {k : Fin n -> Int // k ≠ 0} =>
      (C / R ^ M) * ‖summationIntegerPoint n k.1‖⁻¹ ^ M :=
    Summable.mul_left (C / R ^ M) (summable_ne_zero_integerPoint_norm_inv_pow (n := n) hM)
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hs
  intro k
  exact fourier_norm_smul_integerPoint_le_inv hC hR k.2

private lemma periodizedTorus_mFourierCoeff_summable
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hRpos : 0 < R) (hR : 1 ≤ R) (c : RealEuclideanSpace n) :
    Summable (UnitAddTorus.mFourierCoeff (periodizedTorus n G hRpos c)) := by
  let M : Nat := n + 1
  have hM : n < M := by
    dsimp [M]
    omega
  obtain ⟨C, _hCpos, hC⟩ := fourier_decay_bound n M G
  have htailNorm : Summable fun k : {k : Fin n -> Int // k ≠ 0} =>
      ‖UnitAddTorus.mFourierCoeff (periodizedTorus n G hRpos c) k.1‖ := by
    convert fourier_tail_norm_summable (n := n) (M := M) (G := G) (C := C) (R := R)
      hM hC hR using 1
    ext k
    rw [periodizedTorus_fourierCoeff n G hRpos c k.1]
    simp [norm_mul]
  have htail : Summable fun k : {k : Fin n -> Int // k ≠ 0} =>
      UnitAddTorus.mFourierCoeff (periodizedTorus n G hRpos c) k.1 :=
    Summable.of_norm htailNorm
  have hsingle : Summable fun k : ({0} : Set (Fin n -> Int)) =>
      UnitAddTorus.mFourierCoeff (periodizedTorus n G hRpos c) k.1 :=
    Summable.of_finite
  have hcompl : Summable fun k : (↑(({0} : Set (Fin n -> Int))ᶜ)) =>
      UnitAddTorus.mFourierCoeff (periodizedTorus n G hRpos c) k.1 := by
    convert htail using 1
  exact (summable_subtype_and_compl (s := ({0} : Set (Fin n -> Int)))).1
    ⟨hsingle, hcompl⟩

private lemma fourier_tail_norm_tsum_le
    {n M : Nat} {G : SchwartzMap (RealEuclideanSpace n) Real} {C R : Real}
    (hM : n < M)
    (hC : ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C)
    (hR : 1 ≤ R) :
    (∑' k : {k : Fin n -> Int // k ≠ 0},
      ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖) ≤
      (∑' k : {k : Fin n -> Int // k ≠ 0},
        (C / R ^ M) * ‖summationIntegerPoint n k.1‖⁻¹ ^ M) := by
  have hs_left := fourier_tail_norm_summable (n := n) (M := M) (G := G) hM hC hR
  have hs_right : Summable fun k : {k : Fin n -> Int // k ≠ 0} =>
      (C / R ^ M) * ‖summationIntegerPoint n k.1‖⁻¹ ^ M :=
    Summable.mul_left (C / R ^ M) (summable_ne_zero_integerPoint_norm_inv_pow (n := n) hM)
  exact Summable.tsum_le_tsum
    (fun k => fourier_norm_smul_integerPoint_le_inv hC hR k.2) hs_left hs_right

private lemma fourier_tail_norm_tsum_le_decay
    {n M N : Nat} {G : SchwartzMap (RealEuclideanSpace n) Real} {C R : Real}
    (hM : n < M) (hNM : N ≤ M) (hCnonneg : 0 ≤ C)
    (hC : ∀ ξ : RealEuclideanSpace n, ‖ξ‖ ^ M * ‖(𝓕 (complexSchwartz n G)) ξ‖ ≤ C)
    (hR : 1 ≤ R) :
    (∑' k : {k : Fin n -> Int // k ≠ 0},
      ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖) ≤
      (C * (∑' k : {k : Fin n -> Int // k ≠ 0},
        ‖summationIntegerPoint n k.1‖⁻¹ ^ M)) / R ^ N := by
  have htail := fourier_tail_norm_tsum_le (n := n) (M := M) (G := G) hM hC hR
  have hs_norm := summable_ne_zero_integerPoint_norm_inv_pow (n := n) (M := M) hM
  have hsum_nonneg : 0 ≤ (∑' k : {k : Fin n -> Int // k ≠ 0},
      ‖summationIntegerPoint n k.1‖⁻¹ ^ M) := by
    exact tsum_nonneg fun k => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) M
  calc
    (∑' k : {k : Fin n -> Int // k ≠ 0},
      ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖)
        ≤ (∑' k : {k : Fin n -> Int // k ≠ 0},
          (C / R ^ M) * ‖summationIntegerPoint n k.1‖⁻¹ ^ M) := htail
    _ = (C / R ^ M) * (∑' k : {k : Fin n -> Int // k ≠ 0},
        ‖summationIntegerPoint n k.1‖⁻¹ ^ M) := by
      rw [Summable.tsum_mul_left]
      exact hs_norm
    _ = (C * (∑' k : {k : Fin n -> Int // k ≠ 0},
        ‖summationIntegerPoint n k.1‖⁻¹ ^ M)) / R ^ M := by
      ring
    _ ≤ (C * (∑' k : {k : Fin n -> Int // k ≠ 0},
        ‖summationIntegerPoint n k.1‖⁻¹ ^ M)) / R ^ N := by
      have hnum_nonneg : 0 ≤ C * (∑' k : {k : Fin n -> Int // k ≠ 0},
          ‖summationIntegerPoint n k.1‖⁻¹ ^ M) :=
        mul_nonneg hCnonneg hsum_nonneg
      have hRpowNpos : 0 < R ^ N := pow_pos (lt_of_lt_of_le zero_lt_one hR) N
      have hpow : R ^ N ≤ R ^ M := pow_le_pow_right₀ hR hNM
      exact div_le_div_of_nonneg_left hnum_nonneg hRpowNpos hpow

private lemma uniformSummationEstimate_zero
    (G : SchwartzMap (RealEuclideanSpace 0) Real) (N : Nat) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ R : Real, 1 ≤ R → ∀ c : RealEuclideanSpace 0,
        |scaledLatticeSum 0 G R c - euclideanIntegral 0 G| ≤ C / R ^ N := by
  refine ⟨0, le_rfl, ?_⟩
  intro R _hR c
  simp only [euclideanIntegral]
  rw [show (∫ x : RealEuclideanSpace 0, G x) = G 0 by
    rw [show (MeasureTheory.volume : MeasureTheory.Measure (RealEuclideanSpace 0)) =
        MeasureTheory.Measure.dirac 0 by
      simpa [RealEuclideanSpace] using (volume_euclideanSpace_eq_dirac (ι := Fin 0))]
    simp]
  simp [scaledLatticeSum]
  exact sub_eq_zero.mpr (congrArg G (Subsingleton.elim _ _))

private lemma poisson_tail_bound
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real)
    {R : Real} (hR : 1 ≤ R) (c : RealEuclideanSpace n) :
    |scaledLatticeSum n G R c - euclideanIntegral n G| ≤
      (∑' k : {k : Fin n -> Int // k ≠ 0},
        ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let f : C(UnitAddTorus (Fin n), ℂ) := periodizedTorus n G hRpos c
  let coeff : (Fin n -> Int) -> ℂ := UnitAddTorus.mFourierCoeff f
  have hcoeffSumm : Summable coeff := by
    dsimp [coeff, f]
    exact periodizedTorus_mFourierCoeff_summable n G hRpos hR c
  have hseries :=
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable hcoeffSumm (torusMk n 0)
  have htsum_f : (∑' k : Fin n -> Int, coeff k) = f (torusMk n 0) := by
    simpa [coeff, mFourier_torusMk_zero, smul_eq_mul] using hseries.tsum_eq
  have hscaled_complex : (scaledLatticeSum n G R c : ℂ) = f (torusMk n 0) := by
    dsimp [f]
    rw [periodizedTorus_mk]
    exact (complexPeriodizedSum_zero_eq_scaledLatticeSum n G R c).symm
  have hcoeff_zero : coeff 0 = (euclideanIntegral n G : ℂ) := by
    dsimp [coeff, f]
    rw [periodizedTorus_fourierCoeff n G hRpos c 0]
    simp [fourier_complexSchwartz_zero, UnitAddTorus.mFourier_zero]
  have hsplit := hcoeffSumm.sum_add_tsum_subtype_compl ({0} : Finset (Fin n -> Int))
  have htail_convert :
      (∑' x : {x : Fin n -> Int // x ∉ ({0} : Finset (Fin n -> Int))}, coeff x.1) =
        (∑' k : {k : Fin n -> Int // k ≠ 0}, coeff k.1) := by
    let e :
        {x : Fin n -> Int // x ∉ ({0} : Finset (Fin n -> Int))} ≃
          {x : Fin n -> Int // x ≠ 0} :=
      { toFun := fun x => ⟨x.1, by simpa using x.2⟩
        invFun := fun x => ⟨x.1, by simpa using x.2⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
    simpa using e.tsum_eq (fun k : {k : Fin n -> Int // k ≠ 0} => coeff k.1)
  have hsplit' :
      coeff 0 + (∑' k : {k : Fin n -> Int // k ≠ 0}, coeff k.1) =
        (∑' k : Fin n -> Int, coeff k) := by
    rw [← htail_convert]
    simpa using hsplit
  have htail_eq :
      (∑' k : {k : Fin n -> Int // k ≠ 0}, coeff k.1) =
        (scaledLatticeSum n G R c : ℂ) - (euclideanIntegral n G : ℂ) := by
    calc
      (∑' k : {k : Fin n -> Int // k ≠ 0}, coeff k.1)
          = (coeff 0 + (∑' k : {k : Fin n -> Int // k ≠ 0}, coeff k.1)) -
              coeff 0 := by
                abel
      _ = (∑' k : Fin n -> Int, coeff k) - coeff 0 := by rw [hsplit']
      _ = (scaledLatticeSum n G R c : ℂ) - (euclideanIntegral n G : ℂ) := by
        rw [htsum_f, ← hscaled_complex, hcoeff_zero]
  have htailSumm : Summable fun k : {k : Fin n -> Int // k ≠ 0} => coeff k.1 :=
    hcoeffSumm.subtype fun k => k ≠ 0
  have htailNormSumm : Summable fun k : {k : Fin n -> Int // k ≠ 0} => ‖coeff k.1‖ :=
    htailSumm.norm
  have hnorm_eq :
      (∑' k : {k : Fin n -> Int // k ≠ 0}, ‖coeff k.1‖) =
        (∑' k : {k : Fin n -> Int // k ≠ 0},
          ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖) := by
    congr with k
    dsimp [coeff, f]
    rw [periodizedTorus_fourierCoeff n G hRpos c k.1]
    simp [norm_mul]
  have habs_eq :
      |scaledLatticeSum n G R c - euclideanIntegral n G| =
        ‖((scaledLatticeSum n G R c : ℂ) - (euclideanIntegral n G : ℂ))‖ := by
    rw [← Complex.ofReal_sub]
    exact (RCLike.norm_ofReal (scaledLatticeSum n G R c - euclideanIntegral n G)).symm
  have hnorm_diff :
      ‖((scaledLatticeSum n G R c : ℂ) - (euclideanIntegral n G : ℂ))‖ ≤
        (∑' k : {k : Fin n -> Int // k ≠ 0},
          ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖) := by
    rw [← htail_eq]
    exact (norm_tsum_le_tsum_norm htailNormSumm).trans (le_of_eq hnorm_eq)
  rw [habs_eq]
  exact hnorm_diff

private lemma uniformSummationEstimate_of_fourier_tail_bound
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) (N : Nat)
    (hpoissonTail : ∀ R : Real, 1 ≤ R → ∀ c : RealEuclideanSpace n,
      |scaledLatticeSum n G R c - euclideanIntegral n G| ≤
        (∑' k : {k : Fin n -> Int // k ≠ 0},
          ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ R : Real, 1 ≤ R → ∀ c : RealEuclideanSpace n,
        |scaledLatticeSum n G R c - euclideanIntegral n G| ≤ C / R ^ N := by
  let M : Nat := N + n + 1
  have hM : n < M := by
    dsimp [M]
    omega
  have hNM : N ≤ M := by
    dsimp [M]
    omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ := fourier_decay_bound n M G
  let S : Real := ∑' k : {k : Fin n -> Int // k ≠ 0},
    ‖summationIntegerPoint n k.1‖⁻¹ ^ M
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun k => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) M
  refine ⟨C₀ * S, mul_nonneg hC₀pos.le hSnonneg, ?_⟩
  intro R hR c
  calc
    |scaledLatticeSum n G R c - euclideanIntegral n G|
        ≤ (∑' k : {k : Fin n -> Int // k ≠ 0},
          ‖(𝓕 (complexSchwartz n G)) (R • summationIntegerPoint n k.1)‖) :=
      hpoissonTail R hR c
    _ ≤ (C₀ * S) / R ^ N := by
      simpa [S] using
        fourier_tail_norm_tsum_le_decay (n := n) (M := M) (N := N) (G := G) (C := C₀)
          (R := R) hM hNM hC₀pos.le hC₀ hR

/-- A uniform Poisson-summation estimate for Schwartz functions. -/
theorem uniformSummationEstimate
    (n : Nat) (G : SchwartzMap (RealEuclideanSpace n) Real) (N : Nat) (hN : 1 <= N) :
    exists C : Real, 0 <= C /\
      forall R : Real, 1 <= R -> forall c : RealEuclideanSpace n,
        |scaledLatticeSum n G R c - euclideanIntegral n G| <= C / R ^ N := by
  rcases n with _ | n
  · exact uniformSummationEstimate_zero G N
  · refine uniformSummationEstimate_of_fourier_tail_bound (n + 1) G N ?_
    intro R hR c
    exact poisson_tail_bound (n + 1) G (R := R) hR c

end

end SphereObstructionHilbertShiftQuotient
