module

public import DedekindZetaZeroFree.Adeles.Approximation.FiniteStrongApproximation
public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.FullLatticesAndRationalLines
public import ClassFieldTheory.All

@[expose] public section

open scoped Pointwise

namespace DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers

abbrev Adeles (F : Type*) [Field F] [NumberField F] :=
  IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F
abbrev RationalGL (F : Type*) [Field F] := Matrix.GeneralLinearGroup (Fin 2) F
abbrev AdelicGL (F : Type*) [Field F] [NumberField F] :=
  Matrix.GeneralLinearGroup (Fin 2) (Adeles F)
abbrev RationalPG (F : Type*) [Field F] := Matrix.ProjGenLinGroup (Fin 2) F
abbrev AdelicPG (F : Type*) [Field F] [NumberField F] :=
  Matrix.ProjGenLinGroup (Fin 2) (Adeles F)

noncomputable def projectiveTopology (F : Type*) [Field F] [NumberField F] :
    TopologicalSpace (AdelicPG F) := by
  unfold AdelicPG Matrix.ProjGenLinGroup
  infer_instance

noncomputable def diagonalGL (F : Type*) [Field F] [NumberField F] :
    RationalGL F →* AdelicGL F :=
  Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F))
noncomputable def diagonalPG (F : Type*) [Field F] [NumberField F] :
    RationalPG F →* AdelicPG F :=
  Matrix.ProjGenLinGroup.map (algebraMap F (Adeles F))

def integralVectors (F : Type*) [Field F] [NumberField F] :
    Set (Matrix (Fin 2) (Fin 1) (Adeles F)) :=
  {x | ∀ i j v, x i j v ∈ v.adicCompletionIntegers F}
noncomputable def integralGL (F : Type*) [Field F] [NumberField F] :
    Subgroup (AdelicGL F) := MulAction.stabilizer (AdelicGL F) (integralVectors F)
noncomputable def integralPG (F : Type*) [Field F] [NumberField F] :
    Subgroup (AdelicPG F) := (integralGL F).map Matrix.ProjGenLinGroup.mk

noncomputable def diagonalVector (F : Type*) [Field F] [NumberField F] (x : F × F) :
    Matrix (Fin 2) (Fin 1) (Adeles F) :=
  fun i _ => algebraMap F (Adeles F) (if i = 0 then x.1 else x.2)

noncomputable def localVector (F : Type*) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : F × F) :
    Matrix (Fin 2) (Fin 1) (v.adicCompletion F) :=
  fun i _ => algebraMap F (v.adicCompletion F) (if i = 0 then x.1 else x.2)

def localTranslatedLattice (F : Type*) [Field F] [NumberField F]
    (g : AdelicGL F)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Set (Matrix (Fin 2) (Fin 1) (v.adicCompletion F)) :=
  (fun x : Matrix (Fin 2) (Fin 1) (v.adicCompletion F) =>
    (show Matrix (Fin 2) (Fin 2) (v.adicCompletion F) from
      fun i j => (g.val i j) v) * x) ''
      {x | ∀ i j, x i j ∈ v.adicCompletionIntegers F}

open IsDedekindDomain NumberField

section Topology

variable (F : Type*) [Field F] [NumberField F]

 def integralRing : Subring (Adeles F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  zero_mem' := by intro v; exact (v.adicCompletionIntegers F).zero_mem
  one_mem' := by intro v; exact (v.adicCompletionIntegers F).one_mem
  add_mem' := by intro a b ha hb v; exact (v.adicCompletionIntegers F).toSubring.add_mem (ha v) (hb v)
  mul_mem' := by intro a b ha hb v; exact (v.adicCompletionIntegers F).toSubring.mul_mem (ha v) (hb v)
  neg_mem' := by intro a ha v; exact (v.adicCompletionIntegers F).toSubring.neg_mem (ha v)

private theorem integral_action (a : AdelicGL F)
    (ha : ∀ i j v, a.val i j v ∈ v.adicCompletionIntegers F)
    (x : Matrix (Fin 2) (Fin 1) (Adeles F)) (hx : x ∈ integralVectors F) :
    a • x ∈ integralVectors F := by
  intro i j v
  change ((a.val * x) i j) v ∈ v.adicCompletionIntegers F
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  change (a.val i 0 v * x 0 j v + a.val i 1 v * x 1 j v) ∈ v.adicCompletionIntegers F
  exact (v.adicCompletionIntegers F).toSubring.add_mem
    ((v.adicCompletionIntegers F).toSubring.mul_mem (ha i 0 v) (hx 0 j v))
    ((v.adicCompletionIntegers F).toSubring.mul_mem (ha i 1 v) (hx 1 j v))

private theorem integralGL_eq : integralGL F = (integralRing F).matrix.toSubmonoid.units := by
  ext a
  constructor
  · intro ha
    have h (b : AdelicGL F) (hb : b ∈ integralGL F) :
        ∀ i j v, b.val i j v ∈ v.adicCompletionIntegers F := by
      intro i j v
      have he : Matrix.single j (0 : Fin 1) (1 : Adeles F) ∈ integralVectors F := by
        intro k l w
        simp only [Matrix.single, Matrix.of_apply]
        split_ifs <;> first | exact (w.adicCompletionIntegers F).one_mem | exact (w.adicCompletionIntegers F).zero_mem
      have hh : b • Matrix.single j (0 : Fin 1) (1 : Adeles F) ∈ integralVectors F := by
        rw [← MulAction.mem_stabilizer_iff.mp hb]
        exact Set.smul_mem_smul_set he
      have := hh i 0 v
      fin_cases j <;> simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply,
        Matrix.single, Matrix.of_apply] using this
    exact ⟨h a ha, h a⁻¹ ((integralGL F).inv_mem ha)⟩
  · rintro ⟨ha, hi⟩
    apply MulAction.mem_stabilizer_iff.mpr
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact integral_action F a ha x hx
    · intro x hx
      exact ⟨a⁻¹ • x, integral_action F a⁻¹ hi x hx, by simp⟩
private theorem integralRing_compact : IsCompact (integralRing F : Set (Adeles F)) := by
  letI : ∀ v : HeightOneSpectrum (RingOfIntegers F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => isCompact_iff_compactSpace.mp (isCompact_iff_compactSpace.mpr
      (Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance))
  change IsCompact {a : RestrictedProduct
    (fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set _)) Filter.cofinite |
    ∀ v, a.1 v ∈ v.adicCompletionIntegers F}
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set _)) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

private theorem integralRing_open : IsOpen (integralRing F : Set (Adeles F)) := by
  exact RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem integralGL_compact_open : IsCompact (integralGL F : Set (AdelicGL F)) ∧
    IsOpen (integralGL F : Set (AdelicGL F)) := by
  letI : T2Space (Adeles F) := inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (RingOfIntegers F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set _)) Filter.cofinite))
  rw [integralGL_eq]
  exact ⟨Submonoid.units_isCompact (integralRing_compact F).matrix,
    Submonoid.isOpen_units (integralRing_open F).matrix⟩

theorem integralPG_compact_open : (letI := projectiveTopology F
    IsCompact (integralPG F : Set (AdelicPG F)) ∧
    IsOpen (integralPG F : Set (AdelicPG F))) := by
  letI := projectiveTopology F
  change IsCompact (Matrix.ProjGenLinGroup.mk '' (integralGL F : Set (AdelicGL F))) ∧
    IsOpen (Matrix.ProjGenLinGroup.mk '' (integralGL F : Set (AdelicGL F)))
  exact ⟨(integralGL_compact_open F).1.image continuous_quot_mk,
    QuotientGroup.isOpenMap_coe _ (integralGL_compact_open F).2⟩

end Topology

section Arithmetic

variable (F : Type*) [Field F] [NumberField F]

noncomputable def integralVectorModule : Submodule (RingOfIntegers F)
    (Matrix (Fin 2) (Fin 1) (Adeles F)) where
  carrier := integralVectors F
  zero_mem' := by intro i j v; exact (v.adicCompletionIntegers F).zero_mem
  add_mem' := by intro x y hx hy i j v; exact (v.adicCompletionIntegers F).toSubring.add_mem (hx i j v) (hy i j v)
  smul_mem' := by
    intro a x hx i j v
    change (algebraMap (RingOfIntegers F) (v.adicCompletion F) a * x i j v) ∈ _
    exact (v.adicCompletionIntegers F).toSubring.mul_mem (v.coe_mem_adicCompletionIntegers a) (hx i j v)

noncomputable def diagonalVectorLinear : (F × F) →ₗ[RingOfIntegers F]
    Matrix (Fin 2) (Fin 1) (Adeles F) where
  toFun := diagonalVector F
  map_add' := by
    intro x y; ext i j; fin_cases i <;> simp [diagonalVector]
  map_smul' := by
    intro a x; ext i j; fin_cases i <;>
      simp [diagonalVector, Algebra.smul_def, IsScalarTower.algebraMap_apply (RingOfIntegers F) F (Adeles F)]

noncomputable def adelicVectorLinear (g : AdelicGL F) :
    Matrix (Fin 2) (Fin 1) (Adeles F) →ₗ[RingOfIntegers F]
      Matrix (Fin 2) (Fin 1) (Adeles F) where
  toFun := fun x => g.val * x
  map_add' := Matrix.mul_add _
  map_smul' := by intro a x; exact Matrix.mul_smul _ _ _

noncomputable def rationalIntersectionModule (g : AdelicGL F) :
    Submodule (RingOfIntegers F) (F × F) :=
  (integralVectorModule F).comap ((adelicVectorLinear F g⁻¹).comp
      (diagonalVectorLinear F))

theorem rationalIntersectionModule_mem (g : AdelicGL F) (x : F × F) :
    x ∈ rationalIntersectionModule F g ↔ diagonalVector F x ∈ g • integralVectors F := by
  change g⁻¹ • diagonalVector F x ∈ integralVectors F ↔ _
  exact Set.mem_smul_set_iff_inv_smul_mem.symm

theorem localVector_mem_translated (g : AdelicGL F) (x : F × F)
    (hx : x ∈ rationalIntersectionModule F g)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    localVector F v x ∈ localTranslatedLattice F g v := by
  obtain ⟨y, hy, he⟩ := (rationalIntersectionModule_mem F g x).mp hx
  refine ⟨fun i j => y i j v, fun i j => hy i j v, ?_⟩
  apply Matrix.ext
  intro i j
  have h := congrArg (fun z : Matrix (Fin 2) (Fin 1) (Adeles F) => z i j v) he
  change ((g.val * y) i j) v = _ at h
  change (Matrix.of (fun k l => g.val k l v) *
    Matrix.of (fun k l => y k l v)) i j = _
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h ⊢
  exact h

theorem localTranslatedLattice_compact (g : AdelicGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    IsCompact (localTranslatedLattice F g v) := by
  letI : CompactSpace (v.adicCompletionIntegers F) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  letI : CompactSpace (Matrix (Fin 2) (Fin 1) (v.adicCompletionIntegers F)) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 1 → v.adicCompletionIntegers F))
  have hc : IsCompact {x : Matrix (Fin 2) (Fin 1) (v.adicCompletion F) |
      ∀ i j, x i j ∈ v.adicCompletionIntegers F} := by
    have hh := isCompact_range (show Continuous
        (fun x : Matrix (Fin 2) (Fin 1) (v.adicCompletionIntegers F) =>
          Matrix.of (fun i j => (x i j : v.adicCompletion F))) from
        continuous_matrix fun i j => continuous_subtype_val.comp (continuous_apply j |>.comp (continuous_apply i)))
    convert hh using 1
    ext x
    constructor
    · intro hx
      exact ⟨fun i j => ⟨x i j, hx i j⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact fun i j => (y i j).property
  exact hc.image (continuous_const.matrix_mul continuous_id)

theorem localTranslatedLattice_closed (g : AdelicGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    IsClosed (localTranslatedLattice F g v) :=
  (localTranslatedLattice_compact F g v).isClosed

theorem rationalIntersectionModule_local_closure_subset (g : AdelicGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    closure (localVector F v '' (rationalIntersectionModule F g : Set (F × F))) ⊆
      localTranslatedLattice F g v := by
  apply closure_minimal _ (localTranslatedLattice_closed F g v)
  rintro _ ⟨x, hx, rfl⟩
  exact localVector_mem_translated F g x hx v

theorem local_clear_denominator (v : HeightOneSpectrum (RingOfIntegers F))
    (a : v.adicCompletion F) :
    ∃ d : RingOfIntegers F, d ≠ 0 ∧
      algebraMap (RingOfIntegers F) (v.adicCompletion F) d * a ∈ v.adicCompletionIntegers F := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  have hp0 : p ≠ 0 := by
    intro h
    have hh : (0 : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := by simpa [h] using hp
    exact WithZero.exp_ne_zero hh.symm
  by_cases ha : a = 0
  · exact ⟨1, one_ne_zero, by simp [ha]⟩
  have hval0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt (inv_ne_zero hval0)
  refine ⟨p ^ n, pow_ne_zero _ hp0, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers (RingOfIntegers F) F v, map_mul]
  have hv : Valued.v (algebraMap (RingOfIntegers F) (v.adicCompletion F) (p ^ n)) =
      v.intValuation (p ^ n) :=
    (v.valuedAdicCompletion_eq_valuation (K := F) (p ^ n)).trans (v.valuation_of_algebraMap _)
  rw [hv, map_pow, hp]
  have he : WithZero.exp (-1 : ℤ) ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [← WithZero.exp_nsmul]; congr 1; simp
  rw [he]
  calc
    WithZero.exp (-(n : ℤ)) * Valued.v a ≤ (Valued.v a)⁻¹ * Valued.v a :=
      mul_le_mul_of_nonneg_right hn.le zero_le
    _ = 1 := inv_mul_cancel₀ hval0

theorem adelic_clear_denominator (a : Adeles F) :
    ∃ d : RingOfIntegers F, d ≠ 0 ∧ ∀ v,
      algebraMap (RingOfIntegers F) (v.adicCompletion F) d * a v ∈ v.adicCompletionIntegers F := by
  classical
  let T := (Filter.eventually_cofinite.mp a.cofinite_mem_adicCompletionIntegers).toFinset
  have hT : ∀ v ∉ T, a v ∈ v.adicCompletionIntegers F := by
    intro v hv
    simpa [T] using hv
  choose d hd hint using (fun v : T => local_clear_denominator F v (a v))
  refine ⟨∏ v : T, d v, Finset.prod_ne_zero_iff.mpr (fun v _ => hd v), ?_⟩
  intro v
  by_cases hv : v ∈ T
  · let w : T := ⟨v, hv⟩
    rw [← Finset.mul_prod_erase (Finset.univ (α := T)) d (Finset.mem_univ w), map_mul, mul_assoc]
    rw [mul_left_comm]
    exact (v.adicCompletionIntegers F).toSubring.mul_mem
      (v.coe_mem_adicCompletionIntegers _) (hint w)
  · exact (v.adicCompletionIntegers F).toSubring.mul_mem
      (v.coe_mem_adicCompletionIntegers _) (hT v hv)

end Arithmetic

section CRT

set_option backward.isDefEq.respectTransparency false

variable (F : Type*) [Field F] [NumberField F]

private theorem matrix_clear (g : AdelicGL F) : ∃ d : RingOfIntegers F, d ≠ 0 ∧
    ∀ i j v, algebraMap (RingOfIntegers F) (v.adicCompletion F) d * g.val i j v ∈ v.adicCompletionIntegers F := by
  classical
  choose d hd hint using (fun p : Fin 2 × Fin 2 => adelic_clear_denominator F (g.val p.1 p.2))
  refine ⟨∏ p, d p, Finset.prod_ne_zero_iff.mpr (fun p _ => hd p), ?_⟩
  intro i j v
  rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ (i,j)), map_mul, mul_assoc, mul_left_comm]
  exact (v.adicCompletionIntegers F).toSubring.mul_mem (v.coe_mem_adicCompletionIntegers _) (hint (i,j) v)

private theorem integral_rational (x : F) (h : ∀ v : HeightOneSpectrum (RingOfIntegers F),
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F) :
    ∃ a : RingOfIntegers F, algebraMap (RingOfIntegers F) F a = x := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one F x
  intro v
  have hv := h v
  rw [congrFun (HeightOneSpectrum.algebraMap_adicCompletion (RingOfIntegers F) F (S := F) v) x] at hv
  simpa [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hv

private theorem scaled_action_integral (g : AdelicGL F) (d : RingOfIntegers F)
    (hd : ∀ i j v, algebraMap (RingOfIntegers F) (v.adicCompletion F) d * g.val i j v ∈ v.adicCompletionIntegers F)
    (x : Matrix (Fin 2) (Fin 1) (Adeles F)) (hx : x ∈ integralVectors F) :
    d • (g • x) ∈ integralVectors F := by
  intro i j v
  change (algebraMap (RingOfIntegers F) (v.adicCompletion F) d * ((g.val * x) i j) v) ∈ _
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  change algebraMap (RingOfIntegers F) (v.adicCompletion F) d *
    (g.val i 0 v * x 0 j v + g.val i 1 v * x 1 j v) ∈ _
  rw [mul_add, ← mul_assoc, ← mul_assoc]
  exact (v.adicCompletionIntegers F).toSubring.add_mem
    ((v.adicCompletionIntegers F).toSubring.mul_mem (hd i 0 v) (hx 0 j v))
    ((v.adicCompletionIntegers F).toSubring.mul_mem (hd i 1 v) (hx 1 j v))

private theorem rationalIntersection_fg (g : AdelicGL F) : (rationalIntersectionModule F g).FG := by
  obtain ⟨d, hd, hint⟩ := matrix_clear F g
  have hi (x : rationalIntersectionModule F g) : ∃ a b : RingOfIntegers F,
      (algebraMap (RingOfIntegers F) F a, algebraMap (RingOfIntegers F) F b) = d • (x : F × F) := by
    have hx := (rationalIntersectionModule_mem F g x).mp x.property
    obtain ⟨y, hy, he⟩ := hx
    have hh := scaled_action_integral F g d hint y hy
    change g • y = diagonalVector F x at he
    rw [he] at hh
    obtain ⟨a, ha⟩ := integral_rational F (d • (x : F × F)).1 (fun v => by
      have h := hh 0 0 v
      change algebraMap (RingOfIntegers F) (v.adicCompletion F) d * algebraMap F (v.adicCompletion F) (x : F × F).1 ∈ _ at h
      simpa [diagonalVector, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (RingOfIntegers F) F (v.adicCompletion F)] using h)
    obtain ⟨b, hb⟩ := integral_rational F (d • (x : F × F)).2 (fun v => by
      have h := hh 1 0 v
      change algebraMap (RingOfIntegers F) (v.adicCompletion F) d * algebraMap F (v.adicCompletion F) (x : F × F).2 ∈ _ at h
      simpa [diagonalVector, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (RingOfIntegers F) F (v.adicCompletion F)] using h)
    exact ⟨a, b, Prod.ext ha hb⟩
  let f : rationalIntersectionModule F g →ₗ[RingOfIntegers F] (RingOfIntegers F × RingOfIntegers F) :=
    { toFun := fun x => (Classical.choose (hi x), Classical.choose (Classical.choose_spec (hi x)))
      map_add' := by
        intro x y
        have hf (z : rationalIntersectionModule F g) := Classical.choose_spec (Classical.choose_spec (hi z))
        have hh : (algebraMap (RingOfIntegers F) F (Classical.choose (hi (x+y))),
            algebraMap (RingOfIntegers F) F (Classical.choose (Classical.choose_spec (hi (x+y))))) =
            (algebraMap (RingOfIntegers F) F (Classical.choose (hi x)),
            algebraMap (RingOfIntegers F) F (Classical.choose (Classical.choose_spec (hi x)))) +
            (algebraMap (RingOfIntegers F) F (Classical.choose (hi y)),
            algebraMap (RingOfIntegers F) F (Classical.choose (Classical.choose_spec (hi y)))) := by
          rw [hf, hf, hf, Submodule.coe_add, smul_add]
        apply Prod.ext <;> apply (IsFractionRing.injective (RingOfIntegers F) F)
        · simpa using congrArg Prod.fst hh
        · simpa using congrArg Prod.snd hh
      map_smul' := by
        intro a x
        have hf (z : rationalIntersectionModule F g) := Classical.choose_spec (Classical.choose_spec (hi z))
        have hh : (algebraMap (RingOfIntegers F) F (Classical.choose (hi (a • x))),
            algebraMap (RingOfIntegers F) F (Classical.choose (Classical.choose_spec (hi (a • x))))) =
            a • (algebraMap (RingOfIntegers F) F (Classical.choose (hi x)),
            algebraMap (RingOfIntegers F) F (Classical.choose (Classical.choose_spec (hi x)))) := by
          rw [hf, hf, Submodule.coe_smul, smul_comm d a]
        apply Prod.ext <;> apply (IsFractionRing.injective (RingOfIntegers F) F)
        · simpa [Algebra.smul_def] using congrArg Prod.fst hh
        · simpa [Algebra.smul_def] using congrArg Prod.snd hh }
  have hfi : Function.Injective f := by
    intro x y h
    have hf (z : rationalIntersectionModule F g) := Classical.choose_spec (Classical.choose_spec (hi z))
    have hh : d • (x : F × F) = d • (y : F × F) := by
      rw [← hf x, ← hf y]
      exact congrArg (fun p : RingOfIntegers F × RingOfIntegers F =>
        (algebraMap (RingOfIntegers F) F p.1, algebraMap (RingOfIntegers F) F p.2)) h
    apply Subtype.ext
    exact smul_right_injective _ hd hh
  haveI := isNoetherian_of_injective f hfi
  exact (Module.Finite.iff_fg).mp inferInstance

private theorem rationalIntersection_span (g : AdelicGL F) :
    Submodule.span F (rationalIntersectionModule F g : Set (F × F)) = ⊤ := by
  obtain ⟨d, hd, hint⟩ := matrix_clear F g⁻¹
  have hm (x : F × F) (hx : diagonalVector F x ∈ integralVectors F) : d • x ∈ rationalIntersectionModule F g := by
    change g⁻¹ • diagonalVector F (d • x) ∈ integralVectors F
    have hh := scaled_action_integral F g⁻¹ d hint (diagonalVector F x) hx
    have he : diagonalVector F (d • x) = d • diagonalVector F x := (diagonalVectorLinear F).map_smul d x
    rw [he]
    change g⁻¹.val * (d • diagonalVector F x) ∈ _
    rw [Matrix.mul_smul]
    exact hh
  have h1 := hm (1,0) (by intro i j v; change (algebraMap F (v.adicCompletion F) (if i = 0 then _ else _)) ∈ _; split_ifs <;> simp only [map_zero, map_one] <;> first | exact (v.adicCompletionIntegers F).one_mem | exact (v.adicCompletionIntegers F).zero_mem)
  have h2 := hm (0,1) (by intro i j v; change (algebraMap F (v.adicCompletion F) (if i = 0 then _ else _)) ∈ _; split_ifs <;> simp only [map_zero, map_one] <;> first | exact (v.adicCompletionIntegers F).one_mem | exact (v.adicCompletionIntegers F).zero_mem)
  have hdF : algebraMap (RingOfIntegers F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (RingOfIntegers F) F)).mpr hd
  apply top_unique
  intro x _
  have hx := (Submodule.span F (rationalIntersectionModule F g : Set (F × F))).add_mem
    (Submodule.smul_mem _ (x.1 / algebraMap (RingOfIntegers F) F d) (Submodule.subset_span h1))
    (Submodule.smul_mem _ (x.2 / algebraMap (RingOfIntegers F) F d) (Submodule.subset_span h2))
  simpa [Algebra.smul_def, div_mul_cancel₀ _ hdF] using hx

private theorem integralVectors_open : IsOpen (integralVectors F) := by
  have h : IsOpen {a : Adeles F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)
  have he : integralVectors F = (Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 1 => {a : Adeles F | ∀ v, a v ∈ v.adicCompletionIntegers F}))) := by
    ext x
    change (∀ i j v, x i j v ∈ v.adicCompletionIntegers F) ↔ _
    constructor
    · intro hx i _ j _; exact hx i j
    · intro hx i j; exact hx i (Set.mem_univ _) j (Set.mem_univ _)
  rw [he]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_set_pi Set.finite_univ (fun _ _ => h))

private theorem translated_open (g : AdelicGL F) : IsOpen (g • integralVectors F) := by
  have he : g • integralVectors F = (fun x : Matrix (Fin 2) (Fin 1) (Adeles F) => g⁻¹.val * x) ⁻¹' integralVectors F := by
    ext x
    exact Set.mem_smul_set_iff_inv_smul_mem
  rw [he]
  exact (integralVectors_open F).preimage (continuous_const.matrix_mul continuous_id)

private theorem diagonalVector_dense : DenseRange (diagonalVector F) := by
  have hd : DenseRange (fun x : Fin 2 → Fin 1 → F => fun i j => algebraMap F (Adeles F) (x i j)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => finiteAdele_dense F
  apply hd.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨(x 0 0, x 1 0), by ext i j; fin_cases i <;> fin_cases j <;> simp [diagonalVector]⟩

private theorem local_closure (g : AdelicGL F) (v : HeightOneSpectrum (RingOfIntegers F)) :
    closure (localVector F v '' (rationalIntersectionModule F g : Set (F × F))) = localTranslatedLattice F g v := by
  classical
  apply Set.Subset.antisymm (rationalIntersectionModule_local_closure_subset F g v)
  let ev : Matrix (Fin 2) (Fin 1) (Adeles F) → Matrix (Fin 2) (Fin 1) (v.adicCompletion F) := fun x i j => x i j v
  have hev : Continuous ev := continuous_matrix fun i j => (RestrictedProduct.continuous_eval v).comp (continuous_apply j |>.comp (continuous_apply i))
  have hden := (diagonalVector_dense F).open_subset_closure_inter (translated_open F g)
  have hi : ev '' ((g • integralVectors F) ∩ Set.range (diagonalVector F)) =
      localVector F v '' (rationalIntersectionModule F g : Set (F × F)) := by
    ext z
    constructor
    · rintro ⟨x, ⟨hx, a, rfl⟩, rfl⟩
      exact ⟨a, (rationalIntersectionModule_mem F g a).mpr hx, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨diagonalVector F a, ⟨(rationalIntersectionModule_mem F g a).mp ha, a, rfl⟩, rfl⟩
  rintro z ⟨x, hx, rfl⟩
  let y : Matrix (Fin 2) (Fin 1) (Adeles F) := fun i j =>
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (RingOfIntegers F) => w.adicCompletion F)
      (fun w => w.adicCompletionIntegers F) Filter.cofinite (fun w => if h : w = v then (show w.adicCompletionIntegers F from ⟨h.symm ▸ x i j, by subst w; exact hx i j⟩) else 0)
  have hy : y ∈ integralVectors F := by intro i j w; exact (if h : w = v then (show w.adicCompletionIntegers F from ⟨h.symm ▸ x i j, by subst w; exact hx i j⟩) else (0 : w.adicCompletionIntegers F)).property
  have hey : ev (g • y) = (Matrix.of (fun i j => g.val i j v)) * x := by
    apply Matrix.ext
    intro i j
    change ((g.val * y) i j) v = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    change g.val i 0 v * y 0 j v + g.val i 1 v * y 1 j v = _
    have hyv (i : Fin 2) : y i j v = x i j := by
      dsimp only [y]
      rw [RestrictedProduct.structureMap_apply]
      simp
    rw [hyv, hyv]
    rfl
  change ((Matrix.of (fun i j => g.val i j v)) * x) ∈ _
  rw [← hey, ← hi]
  exact image_closure_subset_closure_image hev ⟨g • y, hden (Set.smul_mem_smul_set hy), rfl⟩

end CRT

theorem bounded_crt_lattice_and_projective_compact
    (F : Type*) [Field F] [NumberField F] :
    (letI := projectiveTopology F
     IsCompact (integralPG F : Set (AdelicPG F)) ∧
       IsOpen (integralPG F : Set (AdelicPG F))) ∧
    ∀ g : AdelicGL F,
      ∃ M : FullLattice (NumberField.RingOfIntegers F) F,
        (∀ x : F × F, x ∈ M.val ↔ diagonalVector F x ∈ g • integralVectors F) ∧
        (∀ v, closure (localVector F v '' (M.val : Set (F × F))) =
          localTranslatedLattice F g v) := by
  refine ⟨integralPG_compact_open F, ?_⟩
  intro g
  refine ⟨⟨rationalIntersectionModule F g, ⟨rationalIntersection_fg F g, rationalIntersection_span F g⟩⟩, ?_, ?_⟩
  · exact rationalIntersectionModule_mem F g
  · exact local_closure F g

noncomputable def intersectionLattice (F : Type*) [Field F] [NumberField F]
    (g : AdelicGL F) : FullLattice (NumberField.RingOfIntegers F) F :=
  Classical.choose ((bounded_crt_lattice_and_projective_compact F).2 g)

end DedekindZetaZeroFree.KPFiniteAdelicLatticeStabilizers
