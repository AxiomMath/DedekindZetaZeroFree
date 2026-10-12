module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators TensorProduct Topology

namespace DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices

 def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

theorem finite_interpolation {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (n : ℕ) (x : Fin n → X) (b : Fin n → S),
      ∀ (f : S) (y : X), f.val y = ∑ i, f.val (x i) * (b i).val y := by
  have htop : Submodule.span ℂ (Set.range (pointEvaluation S)) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro f hf
    have hx : ∃ x, f.val x ≠ 0 := by
      by_contra! hn
      exact hf (Subtype.ext (funext hn))
    obtain ⟨x, hx⟩ := hx
    exact ⟨pointEvaluation S x, ⟨x, rfl⟩, hx⟩
  have hfg : (Submodule.span ℂ (Set.range (pointEvaluation S))).FG := by
    rw [htop]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  choose x hx using fun e : s => hs e.property
  let E := Fintype.equivFin s
  let p : Fin (Fintype.card s) → X := fun i => x (E.symm i)
  have hr : Set.range (fun i => pointEvaluation S (p i)) =
      (s : Set (Module.Dual ℂ S)) := by
    ext e
    constructor
    · rintro ⟨i, rfl⟩
      dsimp [p]
      rw [hx]
      exact (E.symm i).property
    · intro he
      exact ⟨E ⟨e, he⟩, by simpa [p] using hx ⟨e, he⟩⟩
  have hp : Submodule.span ℂ (Set.range (fun i => pointEvaluation S (p i))) = ⊤ := by
    rw [hr, ← he, htop]
  let B := Module.finBasis ℂ S
  have hc : ∀ j, ∃ c : Fin (Fintype.card s) → ℂ,
      ∑ i, c i • pointEvaluation S (p i) = B.coord j := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    rw [hp]
    exact Submodule.mem_top
  choose c hc using hc
  refine ⟨Fintype.card s, p, fun i => ∑ j, c j i • B j, ?_⟩
  intro f y
  have hb := congrArg (fun z : S => z.val y) (B.sum_repr f)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hb
  rw [← hb]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hj := congrArg (fun l : Module.Dual ℂ S => l f) (hc j)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    pointEvaluation, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, Module.Basis.coord_apply] at hj
  rw [← hj, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

 def partialProducts {ι X : Type*} [Fintype ι] (S : ι → Submodule ℂ (X → ℂ))
    (s : Finset ι) : Submodule ℂ ((ι → X) → ℂ) :=
  Submodule.span ℂ (Set.range (fun f : ∀ i, S i => fun a => ∏ i ∈ s, (f i).val (a i)))

private theorem partialProducts_mul {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule ℂ (X → ℂ)) (s : Finset ι) (w : ι) (hw : w ∉ s)
    (f : S w) (h : (ι → X) → ℂ) (hh : h ∈ partialProducts S s) :
    (fun a => f.val (a w) * h a) ∈ partialProducts S (insert w s) := by
  refine Submodule.span_induction
    (p := fun h _ => (fun a => f.val (a w) * h a) ∈ partialProducts S (insert w s))
    ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    refine ⟨Function.update g w f, ?_⟩
    funext a
    dsimp only
    rw [Finset.prod_insert hw]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hw)]
  · simpa only [Pi.zero_def, mul_zero] using
      (Submodule.zero_mem (partialProducts S (insert w s)))
  · intro h k _ _ hh hk
    simpa only [Pi.add_def, mul_add] using Submodule.add_mem _ hh hk
  · intro c h _ hh
    simpa only [Pi.smul_def, smul_eq_mul, mul_left_comm] using Submodule.smul_mem _ c hh

private theorem tensor_interpolation {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule ℂ (X → ℂ)) (n : ι → ℕ)
    (x : ∀ i, Fin (n i) → X) (b : ∀ i, Fin (n i) → S i)
    (s : Finset ι) (h : (ι → X) → ℂ) (a₀ : ι → X)
    (hh : ∀ w ∈ s, ∀ a, h a = ∑ j, h (Function.update a w (x w j)) * (b w j).val (a w))
    (hd : ∀ a, h a = h (fun i => if i ∈ s then a i else a₀ i)) :
    h ∈ partialProducts S s := by
  induction s using Finset.induction_on generalizing h with
  | empty =>
    have he : h = fun _ => h a₀ := by funext a; simpa using hd a
    rw [he]
    have h1 : (fun _ : ι → X => (1 : ℂ)) ∈ partialProducts S ∅ :=
      Submodule.subset_span ⟨fun _ => 0, by simp⟩
    simpa only [Pi.smul_def, smul_eq_mul, mul_one] using Submodule.smul_mem _ (h a₀) h1
  | @insert w s hw ih =>
    have hqi : ∀ j : Fin (n w), (fun a => h (Function.update a w (x w j))) ∈ partialProducts S s := by
      intro j
      apply ih
      · intro v hv a
        have hne : v ≠ w := ne_of_mem_of_not_mem hv hw
        have hi := hh v (Finset.mem_insert_of_mem hv) (Function.update a w (x w j))
        simpa only [Function.update_of_ne hne, Function.update_comm hne] using hi
      · intro a
        have hi := hd (Function.update a w (x w j))
        have hj := hd (Function.update (fun i => if i ∈ s then a i else a₀ i) w (x w j))
        rw [hi, hj]
        congr 1
        funext i
        by_cases hi : i = w
        · subst i; simp
        · by_cases his : i ∈ s <;> simp [hi, his]
    have he : h = ∑ j, (fun a => (b w j).val (a w) * h (Function.update a w (x w j))) := by
      funext a
      simpa only [Finset.sum_apply, mul_comm] using hh w (Finset.mem_insert_self w s) a
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => partialProducts_mul S s w hw (b w j) _ (hqi j))

theorem independent_slices_mem_product_span
    {ι X : Type*} [Fintype ι] [DecidableEq ι] [Nonempty X]
    (S : ι → Submodule ℂ (X → ℂ)) [∀ i, FiniteDimensional ℂ (S i)]
    (h : (ι → X) → ℂ)
    (hh : ∀ i a, (fun x => h (Function.update a i x)) ∈ S i) :
    h ∈ Submodule.span ℂ (Set.range (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i))) := by
  choose n x b hb using fun i => finite_interpolation (S i)
  apply tensor_interpolation S n x b Finset.univ h (fun _ => Classical.choice ‹Nonempty X›)
  · intro i _ a
    have hi := hb i ⟨_, hh i a⟩ (a i)
    simpa only [Function.update_eq_self] using hi
  · intro a
    simp only [Finset.mem_univ, ite_true]

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

abbrev harmonicBand (s : ℝ) (N : ℕ) : Submodule ℂ (PrincipalSeries s) :=
  (Finset.range (N + 1)).sup (harmonicKType s)

theorem harmonicBand_finite (s : ℝ) (N : ℕ) :
    Module.Finite ℂ (harmonicBand s N) := by
  have h (I : Finset ℕ) : Module.Finite ℂ ↥(I.sup (harmonicKType s)) := by
    induction I using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty]
      infer_instance
    | @insert i I hi ih =>
      let : Module.Finite ℂ (harmonicKType s i) :=
        KPCplxHarmonicIntertwinerSpectrum.harmonicKType_finite s i
      let : Module.Finite ℂ ↥(I.sup (harmonicKType s)) := ih
      rw [Finset.sup_insert]
      infer_instance
  exact h _

def harmonicBandEvaluation (s : ℝ) (N : ℕ) :
    harmonicBand s N →ₗ[ℂ] (KPCplxCharacterHaar.ComplexGL2 → ℂ) :=
  (principalSeriesSubmodule s).subtype.comp (harmonicBand s N).subtype

end DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices

namespace DedekindZetaZeroFree.KPLiteralScalarArchUniformBands
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open KPLiteralScalarArchIndependentSlices

theorem invariant_subspace_le_band (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s)) [FiniteDimensional ℂ U]
    (hU : IsKInvariant s U) :
    U ≤ harmonicBand s (Module.finrank ℂ U) := by
  intro f hf
  let : T2Space (PrincipalSeries s) := principalSeries_t2 s
  let : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  have hclosed : IsClosed (U : Set (PrincipalSeries s)) := U.closed_of_finiteDimensional
  obtain ⟨μ, hhaar, hprob⟩ := KPCplxHarmonicExtraction.exists_su2_probability_haar
  obtain ⟨a, hint, havg, htype, hlim⟩ :=
    KPCplxHarmonicExtraction.character_average_harmonic_expansion s μ hhaar hprob f
  have horbit : Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f)) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hU k f hf
  have haU (ℓ : ℕ) : a ℓ ∈ U := by
    have h := KPCplxHarmonicExtraction.character_average_mem_orbit_closure
      s μ hhaar hprob ℓ f (a ℓ) (hint ℓ) (havg ℓ)
    have h' : a ℓ ∈ closure (U : Set (PrincipalSeries s)) := closure_mono horbit h
    rwa [hclosed.closure_eq] at h'
  have hbound (ℓ : ℕ) (hne : a ℓ ≠ 0) : ℓ < Module.finrank ℂ U := by
    have ht := harmonicKType_multiplicity_one s ℓ
    have hi : IsKInvariant s (U ⊓ harmonicKType s ℓ) := by
      intro k v hv
      exact ⟨hU k v hv.1, ht.1 k v hv.2⟩
    have hn : U ⊓ harmonicKType s ℓ ≠ ⊥ := by
      intro he
      have hm : a ℓ ∈ U ⊓ harmonicKType s ℓ := ⟨haU ℓ, htype ℓ⟩
      rw [he] at hm
      exact hne (by simpa using hm)
    have he := (ht.2.2.1 (U ⊓ harmonicKType s ℓ) inf_le_right hi).resolve_left hn
    have hle : harmonicKType s ℓ ≤ U := by
      rw [← he]
      exact inf_le_left
    have hd := Submodule.finrank_mono hle
    rw [ht.2.1] at hd
    omega
  have hzero (ℓ : ℕ) (hℓ : Module.finrank ℂ U ≤ ℓ) : a ℓ = 0 := by
    by_contra hn
    exact (not_lt.mpr hℓ) (hbound ℓ hn)
  have hsum (N : ℕ) (hN : Module.finrank ℂ U ≤ N) :
      (∑ ℓ ∈ Finset.range N, a ℓ) = ∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ := by
    symm
    apply Finset.sum_subset (Finset.range_mono hN)
    intro ℓ hℓ hnot
    exact hzero ℓ (by simpa using hnot)
  have hevent : (fun N => ∑ ℓ ∈ Finset.range N, a ℓ) =ᶠ[Filter.atTop]
      (fun _ : ℕ => ∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ) := by
    filter_upwards [Filter.eventually_ge_atTop (Module.finrank ℂ U)] with N hN
    exact hsum N hN
  have heq : (∑ ℓ ∈ Finset.range (Module.finrank ℂ U), a ℓ) = f :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hevent.symm) hlim
  rw [← heq]
  apply Submodule.sum_mem
  intro ℓ hℓ
  exact (Finset.le_sup (Finset.mem_range_succ_iff.mpr
    (Nat.le_of_lt (Finset.mem_range.mp hℓ))) :
    harmonicKType s ℓ ≤ harmonicBand s (Module.finrank ℂ U)) (htype ℓ)

end DedekindZetaZeroFree.KPLiteralScalarArchUniformBands

namespace DedekindZetaZeroFree.KPLiteralScalarArchCoefficientGeneration
open KPLiteralScalarArchIndependentSlices

def tensorEvaluation {ι X : Type*} [Fintype ι] (S : ι → Submodule ℂ (X → ℂ)) :
    PiTensorProduct ℂ (fun i => S i) →ₗ[ℂ] ((ι → X) → ℂ) :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ((ι → X) → ℂ)).compLinearMap
      (fun i =>
        { toFun := fun f a => f.val (a i)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }))

@[simp] theorem tensorEvaluation_pure {ι X : Type*} [Fintype ι]
    (S : ι → Submodule ℂ (X → ℂ)) (f : ∀ i, S i) (a : ι → X) :
    tensorEvaluation S (PiTensorProduct.tprod ℂ f) a = ∏ i, (f i).val (a i) := by
  simp [tensorEvaluation]

private theorem product_span_eq_range {ι X : Type*} [Fintype ι]
    (S : ι → Submodule ℂ (X → ℂ)) :
    Submodule.span ℂ (Set.range (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i))) =
      (tensorEvaluation S).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ f, funext (tensorEvaluation_pure S f)⟩
  · rintro h ⟨t, rfl⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      rw [map_smul]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨f, (funext (tensorEvaluation_pure S f)).symm⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem uniform_pure_sampling
    {ι X : Type*} [Fintype ι]
    (S : ι → Submodule ℂ (X → ℂ)) [∀ i, FiniteDimensional ℂ (S i)] :
    ∃ (n : ℕ) (p : Fin n → (ι → X)) (c : Fin n → ℂ) (f : Fin n → ∀ i, S i),
      ∀ h ∈ Submodule.span ℂ (Set.range
        (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i))),
        ∀ a, h a = ∑ j, c j * h (p j) * ∏ i, (f j i).val (a i) := by
  let R : Submodule ℂ ((ι → X) → ℂ) := Submodule.span ℂ (Set.range
    (fun f : ∀ i, S i => fun a => ∏ i, (f i).val (a i)))
  have hfin : Module.Finite ℂ R := by
    rw [show R = (tensorEvaluation S).range from product_span_eq_range S]
    infer_instance
  let : Module.Finite ℂ R := hfin
  obtain ⟨m, p, b, hb⟩ := finite_interpolation R
  have hx (i : Fin m) : ∃ d : (∀ j, S j) →₀ ℂ,
      d.sum (fun f c => c • (fun a => ∏ j, (f j).val (a j))) = (b i).val :=
    Finsupp.mem_span_range_iff_exists_finsupp.mp (b i).property
  choose d hd using hx
  let J := (i : Fin m) × (d i).support
  let E := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => p (E.symm j).1,
    fun j => d (E.symm j).1 (E.symm j).2.val,
    fun j => (E.symm j).2.val, ?_⟩
  intro h hh a
  have hbase := hb (⟨h, hh⟩ : R) a
  change h a = _ at hbase
  rw [hbase]
  have he (i : Fin m) : (b i).val a =
      ∑ f ∈ (d i).support, d i f * ∏ j, (f j).val (a j) := by
    have hi := congrFun (hd i) a
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hi.symm
  simp_rw [he, Finset.mul_sum]
  have hs : (∑ i : Fin m, ∑ f ∈ (d i).support,
      h (p i) * (d i f * ∏ j, (f j).val (a j))) =
      ∑ j : J, d j.1 j.2.val * h (p j.1) * ∏ i, (j.2.val i).val (a i) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro f _
    ring
  rw [hs]
  exact Fintype.sum_equiv E _ _ (fun j => by
    exact (congrArg (fun u : J => d u.1 u.2.val * h (p u.1) *
      ∏ i, (u.2.val i).val (a i)) (E.symm_apply_apply j)).symm)

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

theorem harmonic_band_uniform_sampling
    {ι : Type*} [Fintype ι] (N : ι → ℕ) :
    ∃ (n : ℕ) (p : Fin n → (ι → KPCplxCharacterHaar.ComplexGL2))
      (c : Fin n → ℂ) (f : Fin n → ι → KPLiteralTensor.harmonicPlus),
      ∀ h : (ι → KPCplxCharacterHaar.ComplexGL2) → ℂ,
        h ∈ Submodule.span ℂ (Set.range
          (fun f : ∀ i, (harmonicBandEvaluation positiveParameter (N i)).range =>
            fun a => ∏ i, (f i).val (a i))) →
        ∀ a, h a = ∑ j, c j * h (p j) * ∏ i, (f j i).val (a i) := by
  let : ∀ i, Module.Finite ℂ (harmonicBand positiveParameter (N i)) :=
    fun i => harmonicBand_finite _ _
  obtain ⟨n, p, c, f, hp⟩ := uniform_pure_sampling
    (fun i => (harmonicBandEvaluation positiveParameter (N i)).range)
  choose b hb using fun j i => (f j i).property
  have hle (i : ι) : harmonicBand positiveParameter (N i) ≤
      KPLiteralTensor.harmonicPlus := by
    apply Finset.sup_le
    intro k _
    exact le_iSup _ k
  refine ⟨n, p, c, fun j i => ⟨(b j i).val, hle i (b j i).property⟩, ?_⟩
  intro h hh a
  rw [hp h hh a]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (congrFun (hb j i) (a i)).symm

theorem harmonic_family_sampling
    {ι Y : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ)
    (h : Y → (ι → KPCplxCharacterHaar.ComplexGL2) → ℂ)
    (hh : ∀ y i a, (fun x => h y (Function.update a i x)) ∈
      (harmonicBandEvaluation positiveParameter (N i)).range) :
    ∃ (n : ℕ) (p : Fin n → (ι → KPCplxCharacterHaar.ComplexGL2))
      (c : Fin n → ℂ) (f : Fin n → ι → KPLiteralTensor.harmonicPlus),
      ∀ y a, h y a = ∑ j, c j * h y (p j) * ∏ i, (f j i).val (a i) := by
  let : ∀ i, Module.Finite ℂ (harmonicBand positiveParameter (N i)) :=
    fun i => harmonicBand_finite _ _
  obtain ⟨n, p, c, f, hp⟩ := harmonic_band_uniform_sampling N
  exact ⟨n, p, c, f, fun y => hp (h y)
    (independent_slices_mem_product_span _ (h y) (hh y))⟩

end DedekindZetaZeroFree.KPLiteralScalarArchCoefficientGeneration

end
