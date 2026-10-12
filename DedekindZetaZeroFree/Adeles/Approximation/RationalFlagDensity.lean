module

public import DedekindZetaZeroFree.Metaplectic.Kubota.PGL.LocalCover

@[expose] public section

section

namespace DedekindZetaZeroFree
namespace KPRationalFlag
noncomputable section
open scoped NumberField Pointwise

def borel (R : Type*) [CommRing R] : Subgroup (Matrix.GeneralLinearGroup (Fin 2) R) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change a 1 0 = 0 at ha
    change b 1 0 = 0 at hb
    change ((a : Matrix (Fin 2) (Fin 2) R) * (b : Matrix (Fin 2) (Fin 2) R)) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' := by
    intro a ha
    change a 1 0 = 0 at ha
    change ((a⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, ha]

end
end KPRationalFlag

end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree.KPRationalFlagCylinderApproximation
noncomputable section
open scoped NumberField

abbrev LocalScalarProduct (F : Type) [Field F] [NumberField F] :=
  NumberField.InfiniteAdeleRing F ×
    ((v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) →
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)

def scalarDiagonal (F : Type) [Field F] [NumberField F] (x : F) :
    LocalScalarProduct F :=
  (algebraMap F (NumberField.InfiniteAdeleRing F) x,
    fun v => algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) x)

def affineRepresentative {K : Type*} [Field K] (x : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1]
    (by simp [Matrix.det_fin_two])

end
end DedekindZetaZeroFree.KPRationalFlagCylinderApproximation

end

section

namespace DedekindZetaZeroFree.KPRationalFlagCylinderApproximation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Topology
open IsDedekindDomain

private abbrev Place (F : Type) [Field F] [NumberField F] :=
  NumberField.InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

private abbrev abv (F : Type) [Field F] [NumberField F] : Place F → AbsoluteValue F ℝ :=
  Sum.elim (fun v => v.1) (fun v => NumberField.HeightOneSpectrum.adicAbv F v)

private theorem abv_nontrivial (F : Type) [Field F] [NumberField F] (i : Place F) :
    (abv F i).IsNontrivial := by
  cases i with
  | inl v => exact v.isNontrivial
  | inr v =>
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine ⟨algebraMap (𝓞 F) F x, ?_, ne_of_lt ?_⟩
    · exact (IsFractionRing.injective (𝓞 F) F).ne (by simpa using hx0)
    · exact (v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) x).mpr hx

private theorem abv_inequivalent (F : Type) [Field F] [NumberField F] :
    Pairwise (fun i j : Place F => ¬ (abv F i).IsEquiv (abv F j)) := by
  intro i j hij he
  cases i with
  | inl v =>
    cases j with
    | inl w => exact hij (congrArg Sum.inl (NumberField.InfinitePlace.eq_iff_isEquiv.mpr he))
    | inr w =>
      have h := he.le_one_iff (x := (2 : F))
      have hw : abv F (Sum.inr w) (2 : F) ≤ 1 := by
        simpa only [abv, Sum.elim_inr, NumberField.HeightOneSpectrum.adicAbv, map_ofNat] using w.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w) (2 : 𝓞 F)
      have hv : abv F (Sum.inl v) (2 : F) = 2 := by
        simpa [abv, NumberField.InfinitePlace.coe_apply] using v.map_natCast 2
      have := h.mpr hw
      rw [hv] at this
      norm_num at this
  | inr v =>
    cases j with
    | inl w =>
      have h := he.one_lt_iff (x := (2 : F))
      have hv : abv F (Sum.inr v) (2 : F) ≤ 1 := by
        simpa only [abv, Sum.elim_inr, NumberField.HeightOneSpectrum.adicAbv, map_ofNat] using v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) (2 : 𝓞 F)
      have hw : abv F (Sum.inl w) (2 : F) = 2 := by
        simpa [abv, NumberField.InfinitePlace.coe_apply] using w.map_natCast 2
      have hh : 1 < abv F (Sum.inl w) (2 : F) := by rw [hw]; norm_num
      exact (not_lt_of_ge hv) (h.mpr hh)
    | inr w =>
      apply hij
      apply congrArg Sum.inr
      apply HeightOneSpectrum.ext
      apply Ideal.ext
      intro x
      exact (v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) x).symm.trans
        (he.lt_one_iff.trans (w.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w) x))

private theorem denseRange_abv_pi (F : Type) [Field F] [NumberField F] :
    DenseRange (algebraMap F ((i : Place F) → WithAbs (abv F i))) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨z, hz⟩ := hne
  obtain ⟨I, V, hV, hsub⟩ := isOpen_pi_iff.mp hU z hz
  have hd := AbsoluteValue.denseRange_algebraMap_pi
    (fun i : I => abv_nontrivial F i)
    (fun i j hij => abv_inequivalent F (fun h => hij (Subtype.ext h)))
  obtain ⟨x, hx⟩ := hd.exists_mem_open
    (isOpen_set_pi Set.finite_univ (fun i _ => (hV i i.property).1))
    (show (Set.pi Set.univ (fun i : I => V i)).Nonempty from
      ⟨fun i => z i, fun i _ => (hV i i.property).2⟩)
  refine ⟨algebraMap F _ x, hsub ?_, ⟨x, rfl⟩⟩
  intro i hi
  exact hx ⟨i, hi⟩ (Set.mem_univ _)

private def localMap (F : Type) [Field F] [NumberField F] :
    ((i : Place F) → WithAbs (abv F i)) → LocalScalarProduct F :=
  fun x => (fun v => ((show WithAbs v.1 from x (Sum.inl v)) : v.Completion),
    fun v => NumberField.FinitePlace.embedding v (WithAbs.equiv (abv F (Sum.inr v)) (x (Sum.inr v))))

private theorem finiteMap_isometry (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Isometry ((NumberField.FinitePlace.embedding v).comp
      (WithAbs.equiv (abv F (Sum.inr v))).toRingHom) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rw [RingHom.comp_apply, NumberField.FinitePlace.norm_embedding]
  rfl

private theorem localMap_continuous (F : Type) [Field F] [NumberField F] :
    Continuous (localMap F) := by
  apply Continuous.prodMk
  · exact continuous_pi (fun v => (NumberField.InfinitePlace.Completion.continuous_coe v).comp (continuous_apply (Sum.inl v)))
  · exact continuous_pi (fun v => (finiteMap_isometry F v).continuous.comp
      (continuous_apply (Sum.inr v)))

private theorem localMap_denseRange (F : Type) [Field F] [NumberField F] :
    DenseRange (localMap F) := by
  have hinf : DenseRange (fun x : (v : NumberField.InfinitePlace F) → WithAbs v.1 =>
      fun v => (x v : v.Completion)) := DenseRange.piMap (fun v => NumberField.InfinitePlace.Completion.denseRange_coe v)
  have hfin : DenseRange (fun x : (v : HeightOneSpectrum (𝓞 F)) →
      WithAbs (abv F (Sum.inr v)) => fun v =>
        NumberField.FinitePlace.embedding v (WithAbs.equiv (abv F (Sum.inr v)) (x v))) := by
    apply DenseRange.piMap (f := fun v (x : WithAbs (abv F (Sum.inr v))) =>
      NumberField.FinitePlace.embedding v (WithAbs.equiv (abv F (Sum.inr v)) x))
    intro v
    have hr : Set.range (fun x : WithAbs (abv F (Sum.inr v)) =>
        NumberField.FinitePlace.embedding v (WithAbs.equiv (abv F (Sum.inr v)) x)) =
        Set.range (algebraMap F (v.adicCompletion F)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨WithAbs.equiv (abv F (Sum.inr v)) x, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨(WithAbs.equiv (abv F (Sum.inr v))).symm x, rfl⟩
    change Dense _
    rw [hr]
    exact v.denseRange_algebraMap F
  exact (hinf.prodMap hfin).comp
    (Homeomorph.sumPiEquivProdPi (NumberField.InfinitePlace F)
      (HeightOneSpectrum (𝓞 F)) (fun i => WithAbs (abv F i))).surjective.denseRange
    (Continuous.prodMap (continuous_pi (fun v => (NumberField.InfinitePlace.Completion.continuous_coe v).comp (continuous_apply v)))
      (continuous_pi (fun v => (finiteMap_isometry F v).continuous.comp (continuous_apply v))))

theorem scalarDiagonal_denseRange (F : Type) [Field F] [NumberField F] :
    DenseRange (scalarDiagonal F) := by
  have hd := (localMap_denseRange F).comp (denseRange_abv_pi F) (localMap_continuous F)
  convert hd using 1
  rfl

end
end DedekindZetaZeroFree.KPRationalFlagCylinderApproximation

end

section

namespace DedekindZetaZeroFree.KPRationalFlagCylinderApproximation
noncomputable section
open scoped NumberField

namespace PrimitiveColumn

private lemma affine_val {K : Type*} [Field K] (x : K) :
    (affineRepresentative x).val = !![1, 0; x, 1] := rfl

private lemma affine_mul_neg {K : Type*} [Field K] (x : K) :
    affineRepresentative x * affineRepresentative (-x) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affine_val, Matrix.mul_apply, Fin.sum_univ_two]

private lemma affine_inv {K : Type*} [Field K] (x : K) :
    (affineRepresentative x)⁻¹ = affineRepresentative (-x) := by
  apply inv_eq_of_mul_eq_one_left
  simpa using affine_mul_neg (-x)

theorem affine_integral_completion {K : Type*} [Field K]
    (A : ValuationSubring K) (x : K) :
    ∃ k b : GL (Fin 2) K,
      (∀ i j, k i j ∈ A) ∧ (∀ i j, k⁻¹ i j ∈ A) ∧
      b 1 0 = 0 ∧ affineRepresentative x * b = k := by
  by_cases hx : x ∈ A
  · refine ⟨affineRepresentative x, 1, ?_, ?_, ?_, by simp⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [affine_val, hx]
    · intro i j
      rw [affine_inv]
      fin_cases i <;> fin_cases j <;> simp [affine_val, hx]
    · simp
  · have hx0 : x ≠ 0 := by
      intro h
      exact hx (h ▸ A.zero_mem)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    let k : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![x⁻¹, -1; 1, 0] (by simp [Matrix.det_fin_two])
    let l : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![0, 1; -1, x⁻¹] (by simp [Matrix.det_fin_two])
    have hkl : k * l = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [k, l, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.mul_apply, Fin.sum_univ_two]
    have hkinv : k⁻¹ = l := inv_eq_of_mul_eq_one_right hkl
    refine ⟨k, affineRepresentative (-x) * k, ?_, ?_, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [k, Matrix.GeneralLinearGroup.mkOfDetNeZero, hxi]
    · intro i j
      rw [hkinv]
      fin_cases i <;> fin_cases j <;>
        simp [l, Matrix.GeneralLinearGroup.mkOfDetNeZero, hxi]
    · simp [affine_val, k, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two, hx0]
    · rw [← mul_assoc, affine_mul_neg, one_mul]

theorem factor_affine {K : Type*} [Field K] (g : GL (Fin 2) K)
    (h : g 0 0 ≠ 0) :
    ∃ x : K, ∃ b : GL (Fin 2) K, b 1 0 = 0 ∧ affineRepresentative x * b = g := by
  let x := g 1 0 / g 0 0
  refine ⟨x, affineRepresentative (-x) * g, ?_, ?_⟩
  · simp [affine_val, Matrix.mul_apply, Fin.sum_univ_two, x, h]
  · rw [← mul_assoc, affine_mul_neg, one_mul]

theorem local_affine_chart_hits_open {K : Type*} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [PerfectSpace K]
    (U : Set (GL (Fin 2) K)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x : K, ∃ b : GL (Fin 2) K, b 1 0 = 0 ∧ affineRepresentative x * b ∈ U := by
  obtain ⟨g, hg⟩ := hne
  by_cases ha : g 0 0 ≠ 0
  · obtain ⟨x, b, hb, he⟩ := factor_affine g ha
    exact ⟨x, b, hb, he ▸ hg⟩
  · have ha' : g 0 0 = 0 := not_ne_iff.mp ha
    have hc : g 1 0 ≠ 0 := by
      intro hc
      have hd := (Matrix.GeneralLinearGroup.det g).ne_zero
      apply hd
      change Matrix.det g.val = 0
      simp [Matrix.det_fin_two, ha', hc]
    let f : K → GL (Fin 2) K := fun t => Matrix.GeneralLinearGroup.upperRightHom t * g
    have hf : Continuous f := by
      exact Matrix.GeneralLinearGroup.continuous_upperRightHom.mul continuous_const
    have hV : IsOpen (f ⁻¹' U) := hU.preimage hf
    have hnV : (f ⁻¹' U).Nonempty := ⟨0, by
      change Matrix.GeneralLinearGroup.upperRightHom 0 * g ∈ U
      rw [Matrix.GeneralLinearGroup.upperRightHom.map_zero_eq_one, one_mul]
      exact hg⟩
    obtain ⟨t, ht, ht0⟩ := (dense_compl_singleton (0 : K)).inter_open_nonempty _ hV hnV
    have ht0' : t ≠ 0 := by simpa using ht0
    have hft : f t 0 0 ≠ 0 := by
      simpa [f, Matrix.mul_apply, Fin.sum_univ_two, ha'] using mul_ne_zero ht0' hc
    obtain ⟨x, b, hb, he⟩ := factor_affine (f t) hft
    exact ⟨x, b, hb, he ▸ ht⟩

end PrimitiveColumn

open IsDedekindDomain NumberField Matrix Topology Filter
open scoped RestrictedProduct

namespace CylinderAssembly
variable (F : Type) [Field F] [NumberField F]
abbrev V := HeightOneSpectrum (𝓞 F)
abbrev KF (v : V F) := HeightOneSpectrum.adicCompletion F v
abbrev LF := ((v : InfinitePlace F) → GL (Fin 2) v.Completion) × ((v : V F) → GL (Fin 2) (KF F v))
def Good (S : Finset (V F)) (g : LF F) : Prop :=
  ∀ v, v ∉ S → (∀ i j, g.2 v i j ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, (g.2 v)⁻¹ i j ∈ v.adicCompletionIntegers F)
abbrev Domain (S : Finset (V F)) := {g : LF F // Good F S g}
variable {F}
lemma ev {S : Finset (V F)} (g : Domain F S) (i j : Fin 2) :
    ∀ᶠ v in cofinite, g.val.2 v i j ∈ v.adicCompletionIntegers F := by
  filter_upwards [(Finset.finite_toSet S).compl_mem_cofinite] with v hv
  exact (g.property v hv).1 i j
lemma evi {S : Finset (V F)} (g : Domain F S) (i j : Fin 2) :
    ∀ᶠ v in cofinite, (g.val.2 v)⁻¹ i j ∈ v.adicCompletionIntegers F := by
  filter_upwards [(Finset.finite_toSet S).compl_mem_cofinite] with v hv
  exact (g.property v hv).2 i j
def val {S : Finset (V F)} (g : Domain F S) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => (fun v => g.val.1 v i j, ⟨fun v => g.val.2 v i j, ev g i j⟩)
def inv {S : Finset (V F)} (g : Domain F S) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => (fun v => (g.val.1 v)⁻¹ i j, ⟨fun v => (g.val.2 v)⁻¹ i j, evi g i j⟩)
set_option backward.isDefEq.respectTransparency false in
def assemble {S : Finset (V F)} (g : Domain F S) : GL (Fin 2) (AdeleRing (𝓞 F) F) where
  val := val g
  inv := inv g
  val_inv := by
    ext i j
    apply Prod.ext
    · funext v
      have hh := congrFun (congrFun (g.val.1 v).val_inv i) j
      fin_cases i <;> fin_cases j <;>
        simpa [AdeleRing, InfiniteAdeleRing, FiniteAdeleRing, val, inv, Matrix.mul_apply, Fin.sum_univ_two, Prod.fst_add, Prod.fst_mul, Prod.snd_add, Prod.snd_mul, Pi.add_apply, Pi.mul_apply, Matrix.one_apply] using hh
    · apply FiniteAdeleRing.ext F
      intro v
      have hh := congrFun (congrFun (g.val.2 v).val_inv i) j
      fin_cases i <;> fin_cases j <;>
        simpa [AdeleRing, InfiniteAdeleRing, FiniteAdeleRing, val, inv, Matrix.mul_apply, Fin.sum_univ_two, Prod.fst_add, Prod.fst_mul, Prod.snd_add, Prod.snd_mul, Pi.add_apply, Pi.mul_apply, Matrix.one_apply] using hh
  inv_val := by
    ext i j
    apply Prod.ext
    · funext v
      have hh := congrFun (congrFun (g.val.1 v).inv_val i) j
      fin_cases i <;> fin_cases j <;>
        simpa [AdeleRing, InfiniteAdeleRing, FiniteAdeleRing, val, inv, Matrix.mul_apply, Fin.sum_univ_two, Prod.fst_add, Prod.fst_mul, Prod.snd_add, Prod.snd_mul, Pi.add_apply, Pi.mul_apply, Matrix.one_apply] using hh
    · apply FiniteAdeleRing.ext F
      intro v
      have hh := congrFun (congrFun (g.val.2 v).inv_val i) j
      fin_cases i <;> fin_cases j <;>
        simpa [AdeleRing, InfiniteAdeleRing, FiniteAdeleRing, val, inv, Matrix.mul_apply, Fin.sum_univ_two, Prod.fst_add, Prod.fst_mul, Prod.snd_add, Prod.snd_mul, Pi.add_apply, Pi.mul_apply, Matrix.one_apply] using hh

set_option backward.isDefEq.respectTransparency false in
lemma continuous_assemble {S : Finset (V F)} : Continuous (assemble (F := F) (S := S)) := by
  rw [Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    apply Continuous.prodMk
    · exact continuous_pi fun v => by fun_prop
    · let f : Domain F S → Πʳ v : V F, [KF F v, v.adicCompletionIntegers F]_[𝓟 (↑S)ᶜ] :=
        fun g => ⟨fun v => g.val.2 v i j, fun v hv => (g.property v hv).1 i j⟩
      have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr <|
        continuous_pi fun v => by change Continuous (fun a : Domain F S => a.val.2 v i j); fun_prop
      exact (RestrictedProduct.continuous_inclusion
        ((Finset.finite_toSet S).compl_mem_cofinite |> le_principal_iff.mpr)).comp hf
  · apply continuous_matrix
    intro i j
    apply Continuous.prodMk
    · exact continuous_pi fun v => by fun_prop
    · let f : Domain F S → Πʳ v : V F, [KF F v, v.adicCompletionIntegers F]_[𝓟 (↑S)ᶜ] :=
        fun g => ⟨fun v => (g.val.2 v)⁻¹ i j, fun v hv => (g.property v hv).2 i j⟩
      have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr <|
        continuous_pi fun v => by change Continuous (fun a : Domain F S => (a.val.2 v)⁻¹ i j); fun_prop
      exact (RestrictedProduct.continuous_inclusion
        ((Finset.finite_toSet S).compl_mem_cofinite |> le_principal_iff.mpr)).comp hf

def arch (v : InfinitePlace F) : AdeleRing (𝓞 F) F →+* v.Completion :=
  (Pi.evalRingHom _ v).comp (RingHom.fst _ _)
def fin (v : V F) : AdeleRing (𝓞 F) F →+* KF F v :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)
def localize (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : LF F :=
  (fun v => GeneralLinearGroup.map (arch v) g, fun v => GeneralLinearGroup.map (fin v) g)
set_option backward.isDefEq.respectTransparency false in
lemma localize_good (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    ∃ S : Finset (V F), Good F S (localize g) := by
  have h : ∀ᶠ v in cofinite, ∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F ∧
      (g⁻¹ i j).2 v ∈ v.adicCompletionIntegers F := by
    apply (Filter.eventually_all).mpr
    intro i
    apply (Filter.eventually_all).mpr
    intro j
    exact (g i j).2.property.and (g⁻¹ i j).2.property
  classical
  let S := Filter.eventually_cofinite.mp h
  refine ⟨S.toFinset, ?_⟩
  intro v hv
  have hh := (not_not.mp (show ¬ ¬ (∀ i j, (g i j).2 v ∈ v.adicCompletionIntegers F ∧
    (g⁻¹ i j).2 v ∈ v.adicCompletionIntegers F) from by simpa using hv))
  constructor <;> intro i j
  · exact (hh i j).1
  · exact (hh i j).2
set_option backward.isDefEq.respectTransparency false in
lemma assemble_localize (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (S : Finset (V F)) (h : Good F S (localize g)) : assemble ⟨localize g, h⟩ = g := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
lemma integral_open (v : V F) : IsOpen {g : GL (Fin 2) (KF F v) |
    (∀ i j, g i j ∈ v.adicCompletionIntegers F) ∧
    (∀ i j, g⁻¹ i j ∈ v.adicCompletionIntegers F)} := by
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact (Valued.isOpen_valuationSubring _).preimage (by fun_prop)
  · apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact (Valued.isOpen_valuationSubring _).preimage (by fun_prop)
set_option backward.isDefEq.respectTransparency false in
lemma continuous_affine {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous (affineRepresentative (K := K)) := by
  rw [Units.continuous_iff]
  constructor <;> apply continuous_matrix <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [affineRepresentative, GeneralLinearGroup.mkOfDetNeZero, Matrix.inv_def, Matrix.adjugate_fin_two] <;> fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma assemble_arch {S : Finset (V F)} (r : Domain F S) (v : InfinitePlace F) :
    GeneralLinearGroup.map (arch v) (assemble r) = r.val.1 v := by
  apply Units.ext
  rfl
set_option backward.isDefEq.respectTransparency false in
lemma assemble_fin {S : Finset (V F)} (r : Domain F S) (v : V F) :
    GeneralLinearGroup.map (fin v) (assemble r) = r.val.2 v := by
  apply Units.ext
  rfl
end CylinderAssembly

open CylinderAssembly

set_option backward.isDefEq.respectTransparency false in

theorem affine_flag_cylinder
    (F : Type) [Field F] [NumberField F]
    (U : Set (GL (Fin 2) (NumberField.AdeleRing (𝓞 F) F)))
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ W : Set (LocalScalarProduct F), IsOpen W ∧ W.Nonempty ∧
      ∀ x : F, scalarDiagonal F x ∈ W →
        ∃ b : GL (Fin 2) (NumberField.AdeleRing (𝓞 F) F),
          b 1 0 = 0 ∧
            Matrix.GeneralLinearGroup.map
                (algebraMap F (NumberField.AdeleRing (𝓞 F) F))
                (affineRepresentative x) * b ∈ U := by
  classical
  obtain ⟨g, hg⟩ := hne
  obtain ⟨S, hS⟩ := localize_good g
  let p : Domain F S := ⟨localize g, hS⟩
  obtain ⟨T, hT, hTe⟩ := IsInducing.subtypeVal.isOpen_iff.mp
    (hU.preimage (continuous_assemble (F := F) (S := S)))
  have hpT : p.val ∈ T := by
    change p ∈ (Subtype.val ⁻¹' T : Set (Domain F S))
    exact (Set.ext_iff.mp hTe p).mpr (by change assemble p ∈ U; simpa [p, assemble_localize] using hg)
  obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ := isOpen_prod_iff.mp hT _ _ hpT
  obtain ⟨I, a, ha, hIa⟩ := isOpen_pi_iff.mp hA _ hpA
  obtain ⟨J, c, hc, hJc⟩ := isOpen_pi_iff.mp hB _ hpB
  let ao : (v : InfinitePlace F) → Set (GL (Fin 2) v.Completion) :=
    fun v => if v ∈ I then a v else Set.univ
  have hao : ∀ v, IsOpen (ao v) ∧ (localize g).1 v ∈ ao v := by
    intro v
    by_cases hv : v ∈ I
    · simpa [ao, localize, p, hv] using ha v hv
    · simp [ao, hv]
  let co : (v : V F) → Set (GL (Fin 2) (KF F v)) := fun v =>
    (if v ∈ J then c v else Set.univ) ∩
      (if v ∈ S then Set.univ else {k | (∀ i j, k i j ∈ v.adicCompletionIntegers F) ∧
        (∀ i j, k⁻¹ i j ∈ v.adicCompletionIntegers F)})
  have hco : ∀ v, IsOpen (co v) ∧ (localize g).2 v ∈ co v := by
    intro v
    have h1 : IsOpen (if v ∈ J then c v else Set.univ) ∧
        (localize g).2 v ∈ (if v ∈ J then c v else Set.univ) := by
      by_cases hv : v ∈ J
      · simpa [localize, p, hv] using hc v hv
      · simp [hv]
    have h2 : IsOpen (if v ∈ S then (Set.univ : Set (GL (Fin 2) (KF F v))) else
        {k | (∀ i j, k i j ∈ v.adicCompletionIntegers F) ∧
          (∀ i j, k⁻¹ i j ∈ v.adicCompletionIntegers F)}) ∧
        (localize g).2 v ∈ (if v ∈ S then Set.univ else
        {k | (∀ i j, k i j ∈ v.adicCompletionIntegers F) ∧
          (∀ i j, k⁻¹ i j ∈ v.adicCompletionIntegers F)}) := by
      by_cases hv : v ∈ S
      · simp [hv]
      · exact ⟨by simpa [hv] using integral_open v, by simpa [hv] using hS v hv⟩
    exact ⟨h1.1.inter h2.1, h1.2, h2.2⟩
  letI (v : InfinitePlace F) : ConnectedSpace v.Completion := by
    rcases v.isReal_or_isComplex with hv | hv
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.connectedSpace_iff.mpr inferInstance
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.connectedSpace_iff.mpr inferInstance
  letI (v : V F) : NontriviallyNormedField (KF F v) := Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  choose z d hd he using fun v => PrimitiveColumn.local_affine_chart_hits_open
    (ao v) (hao v).1 ⟨_, (hao v).2⟩
  choose w e he0 hec using fun v => PrimitiveColumn.local_affine_chart_hits_open
    (co v) (hco v).1 ⟨_, (hco v).2⟩
  let Q := S ∪ J
  let W : Set (LocalScalarProduct F) := {y |
    (∀ v, affineRepresentative (y.1 v) * d v ∈ ao v) ∧
    (∀ v ∈ Q, affineRepresentative (y.2 v) * e v ∈ co v)}
  have hW : IsOpen W := by
    simp only [W, Set.setOf_and, Set.setOf_forall]
    apply IsOpen.inter
    · apply isOpen_iInter_of_finite
      intro v
      exact (hao v).1.preimage ((continuous_affine.comp (by fun_prop)).mul continuous_const)
    · apply isOpen_biInter_finset
      intro v hv
      exact (hco v).1.preimage ((continuous_affine.comp (by fun_prop)).mul continuous_const)
  refine ⟨W, hW, ⟨(z, w), ?_⟩, ?_⟩
  · exact ⟨he, fun v hv => hec v⟩
  intro x hx
  change (∀ v, affineRepresentative ((scalarDiagonal F x).1 v) * d v ∈ ao v) ∧
    (∀ v ∈ Q, affineRepresentative ((scalarDiagonal F x).2 v) * e v ∈ co v) at hx
  choose k b hk hki hb hkb using fun v => PrimitiveColumn.affine_integral_completion
    (v.adicCompletionIntegers F) (algebraMap F (KF F v) x)
  let q : LF F :=
    (fun v => affineRepresentative ((scalarDiagonal F x).1 v) * d v,
     fun v => if v ∈ Q then affineRepresentative ((scalarDiagonal F x).2 v) * e v else k v)
  have hq : Good F S q := by
    intro v hv
    by_cases hvQ : v ∈ Q
    · have hh := (hx.2 v hvQ).2
      change (∀ i j, _ ∈ _) ∧ (∀ i j, _ ∈ _)
      simpa only [q, if_pos hvQ, if_neg hv, Set.mem_setOf_eq] using hh
    · simpa [q, hvQ] using And.intro (hk v) (hki v)
  let r : Domain F S := ⟨q, hq⟩
  have hqT : q ∈ T := by
    apply hAB
    constructor
    · apply hIa
      intro v hv
      have hh := hx.1 v
      simpa only [q, ao, if_pos (show v ∈ I from hv)] using hh
    · apply hJc
      intro v hv
      have hvQ : v ∈ Q := Finset.mem_union_right S hv
      have hh := (hx.2 v hvQ).1
      simpa only [q, if_pos hvQ, if_pos (show v ∈ J from hv)] using hh
  have hrU : assemble r ∈ U := by
    change r ∈ assemble ⁻¹' U
    rw [← hTe]
    exact hqT
  let ax := GeneralLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F)) (affineRepresentative x)
  refine ⟨ax⁻¹ * assemble r, ?_, by simpa [ax, ← mul_assoc] using hrU⟩
  apply Prod.ext
  · funext v
    have hh : GeneralLinearGroup.map (arch v) (ax⁻¹ * assemble r) = d v := by
      rw [map_mul, map_inv, assemble_arch]
      have hax : GeneralLinearGroup.map (arch v) ax =
          affineRepresentative ((scalarDiagonal F x).1 v) := by
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ax, arch, scalarDiagonal, affineRepresentative,
            GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.map_apply] <;> rfl
      rw [hax]
      change (affineRepresentative _)⁻¹ * (affineRepresentative _ * d v) = d v
      simp
    have hentry := congrArg (fun k : GL (Fin 2) v.Completion => k 1 0) hh
    exact hentry.trans (hd v)
  · apply FiniteAdeleRing.ext F
    intro v
    have hax : GeneralLinearGroup.map (fin v) ax =
        affineRepresentative ((scalarDiagonal F x).2 v) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ax, fin, scalarDiagonal, affineRepresentative,
          GeneralLinearGroup.mkOfDetNeZero, GeneralLinearGroup.map_apply] <;> rfl
    by_cases hv : v ∈ Q
    · have hh : GeneralLinearGroup.map (fin v) (ax⁻¹ * assemble r) = e v := by
        rw [map_mul, map_inv, assemble_fin, hax]
        change (affineRepresentative _)⁻¹ * (if v ∈ Q then _ else _) = e v
        rw [if_pos hv]
        simp
      have hentry := congrArg (fun k : GL (Fin 2) (KF F v) => k 1 0) hh
      exact hentry.trans (he0 v)
    · have hh : GeneralLinearGroup.map (fin v) (ax⁻¹ * assemble r) = b v := by
        rw [map_mul, map_inv, assemble_fin, hax]
        change (affineRepresentative _)⁻¹ * (if v ∈ Q then _ else _) = b v
        rw [if_neg hv, ← hkb v]
        simp [scalarDiagonal]
      have hentry := congrArg (fun k : GL (Fin 2) (KF F v) => k 1 0) hh
      exact hentry.trans (hb v)

end
end DedekindZetaZeroFree.KPRationalFlagCylinderApproximation

end

section

namespace DedekindZetaZeroFree
namespace KPRationalFlag
noncomputable section
open scoped NumberField Pointwise

abbrev AdelicGL (F : Type) [Field F] [NumberField F] :=
  Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (𝓞 F) F)

noncomputable def rationalMap (F : Type) [Field F] [NumberField F] :
    Matrix.GeneralLinearGroup (Fin 2) F →* AdelicGL F :=
  Matrix.GeneralLinearGroup.map (algebraMap F (NumberField.AdeleRing (𝓞 F) F))

def mirabolic (R : Type*) [CommRing R] : Subgroup (Matrix.GeneralLinearGroup (Fin 2) R) where
  carrier := {g | g 1 0 = 0 ∧ g 1 1 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (((a : Matrix (Fin 2) (Fin 2) R) * (b : Matrix (Fin 2) (Fin 2) R)) 1 0 = 0 ∧
      ((a : Matrix (Fin 2) (Fin 2) R) * (b : Matrix (Fin 2) (Fin 2) R)) 1 1 = 1)
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2, hb.1, hb.2]
  inv_mem' := by
    intro a ha
    have h₁ : a⁻¹ 1 0 = 0 := (borel R).inv_mem ha.1
    refine ⟨h₁, ?_⟩
    have hh := congrArg (fun m : Matrix (Fin 2) (Fin 2) R => m 1 1) a.inv_val
    simp only [Matrix.GeneralLinearGroup.coe_inv] at h₁ ⊢
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h₁, ha.2] using hh

abbrev scalars (F : Type) [Field F] [NumberField F] :
    (NumberField.AdeleRing (𝓞 F) F)ˣ →* AdelicGL F :=
  Matrix.GeneralLinearGroup.scalar (Fin 2)

def fullBorelPreimage (F : Type) [Field F] [NumberField F]
    {G : Type*} [Group G] (π : G →* AdelicGL F) : Subgroup G :=
  (borel (NumberField.AdeleRing (𝓞 F) F)).comap π

end
end KPRationalFlag
open KPRationalFlag
open scoped NumberField Pointwise

private theorem borel_eq_mirabolic_mul_scalar (R : Type*) [CommRing R] :
    (KPRationalFlag.borel R : Set (GL (Fin 2) R)) =
      (KPRationalFlag.mirabolic R : Set (GL (Fin 2) R)) *
        Set.range (Matrix.GeneralLinearGroup.scalar (Fin 2) : Rˣ →* GL (Fin 2) R) := by
  ext g
  constructor
  · intro hg
    change g 1 0 = 0 at hg
    have hdet : (g : Matrix (Fin 2) (Fin 2) R).det = g 0 0 * g 1 1 := by
      rw [Matrix.det_fin_two]; simp [hg]
    have hunit : IsUnit (g 1 1) := by
      have h1 : IsUnit ((g : Matrix (Fin 2) (Fin 2) R).det) :=
        (Matrix.GeneralLinearGroup.det g).isUnit
      rw [hdet] at h1
      exact isUnit_of_mul_isUnit_right h1
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, (↑u : R) = g 1 1 := hunit
    refine Set.mem_mul.mpr
      ⟨g * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹,
      ⟨?_, ?_⟩, Matrix.GeneralLinearGroup.scalar (Fin 2) u, ⟨_, rfl⟩, ?_⟩
    · show (((↑g : Matrix (Fin 2) (Fin 2) R) *
        (↑(Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹) :
          Matrix (Fin 2) (Fin 2) R))) 1 0 = 0
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, hg]
    · show (((↑g : Matrix (Fin 2) (Fin 2) R) *
        (↑(Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹) :
          Matrix (Fin 2) (Fin 2) R))) 1 1 = 1
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, hg, ← hu,
        Units.val_inv u]
    · show (g * Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u = g
      rw [map_inv (Matrix.GeneralLinearGroup.scalar (Fin 2)) u, mul_assoc,
        inv_mul_cancel, mul_one]
  · intro hg
    obtain ⟨p, hp, z, ⟨u, rfl⟩, rfl⟩ := Set.mem_mul.mp hg
    have hp10 : (p : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := hp.1
    have hp11 : (p : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := hp.2
    show (((↑p : Matrix (Fin 2) (Fin 2) R) *
      (↑(Matrix.GeneralLinearGroup.scalar (Fin 2) u) : Matrix (Fin 2) (Fin 2) R))) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, hp10, hp11]

theorem kp_adelic_borel_eq_mirabolic_scalars
    (F : Type) [Field F] [NumberField F] :
    (borel (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F)) =
      (mirabolic (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F)) *
        Set.range (scalars F) := by
  exact borel_eq_mirabolic_mul_scalar (NumberField.AdeleRing (𝓞 F) F)

private lemma dense_preimage_of_dense_image {G H : Type*} [TopologicalSpace G]
    [TopologicalSpace H] {π : G → H} (hπopen : IsOpenMap π) {T : Set H} (hT : Dense T) :
    Dense (π ⁻¹' T) := by
  rw [dense_iff_inter_open] at hT ⊢
  intro U hU hUne
  obtain ⟨z, hzU, hzT⟩ := hT (π '' U) (hπopen U hU) (hUne.image π)
  obtain ⟨y, hyU, hyz⟩ := hzU
  refine ⟨y, hyU, ?_⟩
  show π y ∈ T
  rwa [hyz]

theorem kp_rational_adelic_flag_density
    (F : Type) [Field F] [NumberField F] :
    Dense (Set.range (rationalMap F) *
      (borel (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F))) ∧
    Set.range (rationalMap F) *
        (borel (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F)) =
      Set.range (rationalMap F) *
        (mirabolic (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F)) *
        Set.range (scalars F) := by
  constructor
  · rw [dense_iff_inter_open]
    intro U hU hUne
    obtain ⟨W, hW, hWne, hflags⟩ :=
      KPRationalFlagCylinderApproximation.affine_flag_cylinder F U hU hUne
    have hdiag := KPRationalFlagCylinderApproximation.scalarDiagonal_denseRange F
    rw [DenseRange, dense_iff_inter_open] at hdiag
    obtain ⟨w, hwW, x, hxw⟩ := hdiag W hW hWne
    have hxW : KPRationalFlagCylinderApproximation.scalarDiagonal F x ∈ W := by
      rwa [hxw]
    obtain ⟨b, hb, hmem⟩ := hflags x hxW
    refine ⟨rationalMap F (KPRationalFlagCylinderApproximation.affineRepresentative x) * b, hmem, ?_⟩
    exact Set.mul_mem_mul
      ⟨KPRationalFlagCylinderApproximation.affineRepresentative x, rfl⟩ hb
  · rw [kp_adelic_borel_eq_mirabolic_scalars F, mul_assoc]

theorem kp_rational_adelic_cover_flag_density
    (F : Type) [Field F] [NumberField F]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (π : G →* AdelicGL F) (hπcont : Continuous π) (hπopen : IsOpenMap π)
    (hπsurj : Function.Surjective π)
    (sF : Matrix.GeneralLinearGroup (Fin 2) F →* G)
    (hsF : π.comp sF = rationalMap F) :
    Dense (Set.range sF * (fullBorelPreimage F π : Set G)) := by
  have hS : (Set.range sF * (fullBorelPreimage F π : Set G)) =
      π ⁻¹' (Set.range (rationalMap F) *
        (KPRationalFlag.borel (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F))) := by
    ext x
    constructor
    · rintro ⟨a, ⟨γ, rfl⟩, c, hc, rfl⟩
      show π (sF γ * c) ∈ Set.range (rationalMap F) *
        (KPRationalFlag.borel (NumberField.AdeleRing (𝓞 F) F) : Set (AdelicGL F))
      rw [map_mul]
      have h1 : π (sF γ) = rationalMap F γ := DFunLike.congr_fun hsF γ
      rw [h1]
      exact Set.mul_mem_mul ⟨γ, rfl⟩ hc
    · intro hx
      obtain ⟨y, ⟨γ, rfl⟩, b, hb, hxb⟩ := Set.mem_mul.mp hx
      refine Set.mem_mul.mpr ⟨sF γ, ⟨γ, rfl⟩, (sF γ)⁻¹ * x, ?_, by group⟩
      show π ((sF γ)⁻¹ * x) ∈ KPRationalFlag.borel (NumberField.AdeleRing (𝓞 F) F)
      rw [map_mul, map_inv]
      have h1 : π (sF γ) = rationalMap F γ := DFunLike.congr_fun hsF γ
      rw [h1, ← hxb, inv_mul_cancel_left]
      exact hb
  rw [hS]
  exact dense_preimage_of_dense_image hπopen (kp_rational_adelic_flag_density F).1

theorem kp_rational_adelic_cover_borel_vanishing
    (F : Type) [Field F] [NumberField F]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (π : G →* AdelicGL F) (hπcont : Continuous π) (hπopen : IsOpenMap π)
    (hπsurj : Function.Surjective π)
    (sF : Matrix.GeneralLinearGroup (Fin 2) F →* G)
    (hsF : π.comp sF = rationalMap F)
    (f : G → ℂ) (hf : Continuous f)
    (hleft : ∀ γ g, f (sF γ * g) = f g)
    (hB : ∀ b ∈ fullBorelPreimage F π, f b = 0) :
    f = 0 := by
  refine Continuous.ext_on (kp_rational_adelic_cover_flag_density F π hπcont hπopen hπsurj sF hsF)
    hf continuous_const ?_
  rintro x ⟨a, ⟨γ, rfl⟩, b, hb, rfl⟩
  rw [hleft γ b, hB b hb]
  rfl

end DedekindZetaZeroFree

end
