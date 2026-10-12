module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.AdelicFiniteLevelTorus
public import DedekindZetaZeroFree.Adeles.Quotients.AdditiveCompactness
public import DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness
public import DedekindZetaZeroFree.Adeles.Characters.AdditiveQuotient

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaRationalFourierSummation

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical

def rationalFrequency (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F)
    (q : KPAdditiveQuotient F) : ℂ :=
  ψ.toAddChar (QuotientAddGroup.mk
    (-(algebraMap F (KPAdeles F) ν * Quotient.out q)))

theorem rationalFrequency_mk (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) (x : KPAdeles F) :
    rationalFrequency F ψ ν (QuotientAddGroup.mk x) =
      ψ.toAddChar (QuotientAddGroup.mk (-(algebraMap F (KPAdeles F) ν * x))) := by
  unfold rationalFrequency
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add
    (NumberField.AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨s, hs⟩ := r.property
  rw [hr]
  apply congrArg ψ.toAddChar
  apply QuotientAddGroup.eq.mpr
  refine ⟨ν * s, ?_⟩
  rw [map_mul, hs]
  ring

theorem rationalFrequency_add (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F)
    (q r : KPAdditiveQuotient F) :
    rationalFrequency F ψ ν (q + r) =
      rationalFrequency F ψ ν q * rationalFrequency F ψ ν r := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
  rw [← QuotientAddGroup.mk_add, rationalFrequency_mk, rationalFrequency_mk,
    rationalFrequency_mk, mul_add, neg_add, QuotientAddGroup.mk_add,
    ψ.toAddChar.map_add_eq_mul]

theorem rationalFrequency_continuous (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F)) (ν : F) :
    Continuous (rationalFrequency F ψ ν) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  change Continuous (fun x : KPAdeles F => rationalFrequency F ψ ν (QuotientAddGroup.mk x))
  simp_rw [rationalFrequency_mk]
  exact ψ.continuous_toFun.comp (QuotientAddGroup.continuous_mk.comp
    ((continuous_const.mul continuous_id).neg))

theorem compactTorus_family_derivative_bound {d P : Type*} [Fintype d]
    [TopologicalSpace P] [CompactSpace P]
    (f : P → C(UnitAddTorus d, ℂ)) (N : ℕ)
    (hderivatives : ∀ k ≤ N, Continuous (fun z : P × (d → ℝ) =>
      iteratedFDeriv ℝ k (compactTorusLift (f z.1)) z.2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p k, k ≤ N → ∀ x : d → ℝ,
      ‖iteratedFDeriv ℝ k (compactTorusLift (f p)) x‖ ≤ C := by
  classical
  have htranslate (p : P) (m : d → ℤ) :
      (fun x : d → ℝ => compactTorusLift (f p) (x + fun i => (m i : ℝ))) =
        compactTorusLift (f p) := by
    funext x
    apply congrArg (f p)
    funext i
    simp only [Pi.add_apply, AddCircle.coe_add]
    have hz : ((m i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨m i, by simp⟩
    simp [hz]
  have hjettranslate (p : P) (m : d → ℤ) (k : ℕ) (x : d → ℝ) :
      iteratedFDeriv ℝ k (compactTorusLift (f p)) (x + fun i => (m i : ℝ)) =
        iteratedFDeriv ℝ k (compactTorusLift (f p)) x := by
    rw [← iteratedFDeriv_comp_add_right, htranslate]
  have hc : IsCompact ((Set.univ : Set P) ×ˢ Set.Icc (0 : d → ℝ) 1) :=
    isCompact_univ.prod isCompact_Icc
  have hb : ∀ k : Fin (N + 1), ∃ C : ℝ, ∀ z ∈
      ((Set.univ : Set P) ×ˢ Set.Icc (0 : d → ℝ) 1),
      ‖iteratedFDeriv ℝ k (compactTorusLift (f z.1)) z.2‖ ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := hc.bddAbove_image
      ((hderivatives k (Nat.le_of_lt_succ k.isLt)).norm.continuousOn)
    exact ⟨C, fun z hz => hC (Set.mem_image_of_mem _ hz)⟩
  choose B hB using hb
  refine ⟨max 0 (Finset.univ.sup' Finset.univ_nonempty B), le_max_left _ _, ?_⟩
  intro p k hk x
  let y : d → ℝ := fun i => Int.fract (x i)
  have hy : y ∈ Set.Icc (0 : d → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have hx : x = y + fun i => (Int.floor (x i) : ℝ) := by
    funext i
    exact (Int.fract_add_floor (x i)).symm
  rw [hx, hjettranslate]
  exact (hB ⟨k, Nat.lt_succ_of_le hk⟩ (p, y) ⟨Set.mem_univ _, hy⟩).trans
    ((Finset.le_sup' B (Finset.mem_univ _)).trans (le_max_right _ _))

private theorem majorant_lattice_coordinates {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {d : Type*} [Fintype d] (b : Module.Basis d ℤ L) :
    ∃ (c : E ≃L[ℝ] (d → ℝ)) (t : (E ⧸ L.toAddSubgroup) ≃ₜ+ UnitAddTorus d),
      ∀ x, t (QuotientAddGroup.mk x) = fun i => (c x i : UnitAddCircle) := by
  let c := b.ofZLatticeBasis ℝ
  let f : E →+ UnitAddTorus d :=
    { toFun := fun x i => (c.equivFun x i : UnitAddCircle)
      map_zero' := by ext i; simp
      map_add' := by intros x y; ext i; simp }
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    exact QuotientAddGroup.continuous_mk.comp
      ((continuous_apply i).comp c.equivFun.toContinuousLinearEquiv.continuous)
  have hs : Function.Surjective f := by
    intro y
    have hy (i : d) : ∃ r : ℝ, (r : UnitAddCircle) = y i :=
      QuotientAddGroup.mk_surjective (y i)
    choose r hr using hy
    refine ⟨c.equivFun.symm r, ?_⟩
    ext i
    change (c.equivFun (c.equivFun.symm r) i : UnitAddCircle) = y i
    rw [LinearEquiv.apply_symm_apply]
    exact hr i
  have hk : L.toAddSubgroup = f.ker := by
    ext x
    change x ∈ L ↔ f x = 0
    rw [← b.ofZLatticeBasis_span ℝ, c.mem_span_iff_repr_mem ℤ]
    constructor
    · intro hx
      ext i
      obtain ⟨n, hn⟩ := hx i
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨n, by simpa [c, f, Module.Basis.equivFun_apply] using hn⟩
    · intro hx i
      have hi : (c.equivFun x i : UnitAddCircle) = 0 := congrFun hx i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
      exact ⟨n, by simpa [Module.Basis.equivFun_apply] using hn⟩
  let e := QuotientAddGroup.liftEquiv L.toAddSubgroup hs hk
  have he : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk L.toAddSubgroup).continuous_iff.mpr
    exact hf
  have hcomp : CompactSpace (E ⧸ L.toAddSubgroup) := by
    apply isCompact_univ_iff.mp
    have hp := IsZLattice.isCompact_range_of_periodic L
      (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup)
      QuotientAddGroup.continuous_mk (by
        intro z w hw
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
    simpa only [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] using hp
  letI := hcomp
  exact ⟨c.equivFun.toContinuousLinearEquiv,
    { e with continuous_toFun := he
             continuous_invFun := he.homeoOfEquivCompactToT2.continuous_invFun }, fun x => rfl⟩

set_option backward.isDefEq.respectTransparency false in
open ThetaAdditiveFourier.FiniteLevelDescent in
theorem exists_uniform_smooth_coordinates
    (F : Type) [Field F] [NumberField F]
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hc : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ho : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (f : P × KPAdditiveQuotient F → ℂ)
    (hl : ∀ p, HasSmoothAdditiveLevel K (fun q => f (p, q)))
    (B : (n : ℕ) → (Fin n → mixedEmbedding.mixedSpace F) → ℝ)
    (hs : IsUniformArchSmoothFamily f B) :
    ∃ e : finiteLevelAdditiveQuotient K ≃ₜ+ UnitAddTorus (Fin (Module.finrank ℚ F)),
      (∀ p, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (compactTorusLift (torusFamily K e f p))) ∧
      ∀ n, Continuous (fun z : P × (Fin (Module.finrank ℚ F) → ℝ) =>
        iteratedFDeriv ℝ n (compactTorusLift (torusFamily K e f z.1)) z.2) := by
  letI := finiteLevelLattice_discrete K hc ho
  obtain ⟨hL, hrank⟩ := finiteLevelLattice_full_rank K hc ho
  letI := hL
  letI := ZLattice.module_finite ℝ (finiteLevelLattice K)
  letI := ZLattice.module_free ℝ (finiteLevelLattice K)
  obtain ⟨c, t, ht⟩ := majorant_lattice_coordinates (finiteLevelLattice K)
    (Module.finBasisOfFinrankEq ℤ (finiteLevelLattice K) hrank)
  obtain ⟨a, ha⟩ := finiteLevel_torus_homeomorph K hc ho
  let e := a.symm.trans t
  have heq (p : P) : compactTorusLift (torusFamily K e f p) =
      (fun x => f (p, smoothArchInclusion F (c.symm x))) := by
    funext x
    have hx := ht (c.symm x)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hx
    change descend K (fun q => f (p, q)) (e.symm (fun i => (x i : UnitAddCircle))) = _
    rw [← hx]
    change descend K (fun q => f (p, q))
      (a (t.symm (t (QuotientAddGroup.mk (c.symm x))))) = _
    rw [t.symm_apply_apply, ha]
    exact descend_mk K _ (hl p) _
  have hf (p : P) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => f (p, smoothArchInclusion F x)) := by
    simpa only [zero_add] using (hs.2.1 p).2.1 0
  have hjet (p : P) (n : ℕ) (x : mixedEmbedding.mixedSpace F) :
      iteratedFDeriv ℝ n (fun x => f (p, smoothArchInclusion F x)) x =
        smoothArchJet n (fun q => f (p, q)) (smoothArchInclusion F x) := by
    unfold smoothArchJet
    have hi (y : mixedEmbedding.mixedSpace F) :
        smoothArchInclusion F (x + y) = smoothArchInclusion F x + smoothArchInclusion F y := by
      let i : mixedEmbedding.mixedSpace F →+ KPAdeles F :=
        { toFun := fun x => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 0)
          map_zero' := by
            change (_, _) = ((0, 0) : InfiniteAdeleRing F × _)
            exact Prod.ext (map_zero _) rfl
          map_add' := by
            intro x y
            change (_, _) = ((_, _) + (_, _) : InfiniteAdeleRing F × _)
            exact Prod.ext (map_add _ x y) (zero_add _).symm }
      exact ((QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)).comp i).map_add x y
    simp_rw [← hi]
    simpa only [add_zero] using (iteratedFDeriv_comp_add_left n x 0
      (f := fun x => f (p, smoothArchInclusion F x))).symm
  have hinc : Continuous (smoothArchInclusion F) := by
    let m : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
      (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => InfinitePlace.IsReal v)
        (fun v => v.Completion)).trans
        ((Homeomorph.prodCongr
          (Homeomorph.piCongrRight (fun v =>
            (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
          ((Homeomorph.piCongrRight (fun v =>
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
            (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
              (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex))))))
    exact QuotientAddGroup.continuous_mk.comp
      ((m.symm.continuous.congr (fun _ => rfl)).prodMk continuous_const)
  refine ⟨e, ?_, ?_⟩
  · intro p
    rw [heq]
    exact (hf p).comp c.symm.contDiff
  · intro n
    simp_rw [heq]
    have hj : Continuous (fun z : P × (Fin (Module.finrank ℚ F) → ℝ) =>
        iteratedFDeriv ℝ n (fun x => f (z.1, smoothArchInclusion F x)) (c.symm z.2)) := by
      simp_rw [hjet]
      exact (hs.2.2.1 n).comp
        (continuous_fst.prodMk (hinc.comp (c.symm.continuous.comp continuous_snd)))
    have he (p : P) (x) := c.symm.toContinuousLinearMap.iteratedFDeriv_comp_right
      (hf p) x (i := n) (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
    convert (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => c.symm.toContinuousLinearMap)).continuous.comp hj using 1
    funext z
    exact he z.1 z.2

theorem rationalFrequency_injective (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ) :
    Function.Injective (rationalFrequency F ψ) := by
  intro ν η h
  by_contra hne
  obtain ⟨q, hq⟩ := hψ
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hd : ν - η ≠ 0 := sub_ne_zero.mpr hne
  let y : KPAdeles F := -(algebraMap F (KPAdeles F) (ν - η)⁻¹ * x)
  have hh := congrFun h (QuotientAddGroup.mk y)
  simp only [rationalFrequency_mk] at hh
  have hz : ψ.toAddChar (QuotientAddGroup.mk
      (-(algebraMap F (KPAdeles F) (ν - η) * y))) = 1 := by
    have he : -(algebraMap F (KPAdeles F) (ν - η) * y) =
        -(algebraMap F (KPAdeles F) ν * y) -
          -(algebraMap F (KPAdeles F) η * y) := by rw [map_sub]; ring
    rw [he, QuotientAddGroup.mk_sub, ψ.toAddChar.map_sub_eq_div, hh]
    exact div_self (by
      intro hz
      have hn := ψ.unitary (QuotientAddGroup.mk (-(algebraMap F (KPAdeles F) η * y)))
      change ‖ψ.toAddChar _‖ = 1 at hn
      rw [hz, norm_zero] at hn
      norm_num at hn)
  have he : -(algebraMap F (KPAdeles F) (ν - η) * y) = x := by
    dsimp [y]
    rw [mul_neg, neg_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
  rw [he] at hz
  exact hq hz

private theorem unitary_character_integral {Q : Type*} [AddCommGroup Q]
    [TopologicalSpace Q] [IsTopologicalAddGroup Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (χ : Q → ℂ) (hadd : ∀ q r, χ (q + r) = χ q * χ r) :
    (∫ q, χ q ∂μ) = if (∀ q, χ q = 1) then 1 else 0 := by
  classical
  split_ifs with h
  · simp_rw [h]
    simp
  · obtain ⟨q, hq⟩ := not_forall.mp h
    have hi := integral_add_right_eq_self (μ := μ) χ q
    simp_rw [hadd] at hi
    rw [integral_mul_const] at hi
    by_contra hn
    exact hq ((mul_eq_left₀ hn).mp hi)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem mFourier_add_point {d : Type*} [Fintype d]
    (n : d → ℤ) (q r : UnitAddTorus d) :
    UnitAddTorus.mFourier n (q + r) =
      UnitAddTorus.mFourier n q * UnitAddTorus.mFourier n r := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

private theorem mFourier_norm_point {d : Type*} [Fintype d]
    (n : d → ℤ) (q : UnitAddTorus d) : ‖UnitAddTorus.mFourier n q‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

theorem uniform_majorant_partial_matching {I J P : Type*}
    (R : I → J → Prop) (hunique : ∀ i j k, R i j → R i k → j = k)
    (c : P → I → ℂ) (b : I → ℝ) (hb : Summable b)
    (hpos : ∀ i, 0 ≤ b i) (hbound : ∀ p i, ‖c p i‖ ≤ b i) :
    ∃ B : J → ℝ, Summable B ∧ (∀ j, 0 ≤ B j) ∧
      ∀ p j, ‖∑' i, if R i j then c p i else 0‖ ≤ B j := by
  classical
  let g : I → Option J := fun i => if h : ∃ j, R i j then some h.choose else none
  have hg (i : I) (j : J) : g i = some j ↔ R i j := by
    dsimp [g]
    split_ifs with h
    · constructor
      · intro he
        have hh := Option.some.inj he
        exact hh ▸ h.choose_spec
      · intro hr
        exact congrArg some (hunique i _ _ h.choose_spec hr)
    · simp only [Option.noConfusion, false_iff]
      exact fun hr => h ⟨j, hr⟩
  have hp := (summable_partition (show 0 ≤ b from hpos)
    (s := fun j : Option J => g ⁻¹' {j}) (by
      intro i
      exact ⟨g i, rfl, fun j hj => hj.symm⟩)).mp hb
  let B : J → ℝ := fun j => ∑' i : {i // g i = some j}, b i
  refine ⟨B, hp.2.comp_injective (Option.some_injective J), ?_, ?_⟩
  · intro j
    exact tsum_nonneg (fun _ => hpos _)
  · intro p j
    have hi : Summable (fun i => if R i j then b i else 0) :=
      hb.of_nonneg_of_le (fun i => by split_ifs; exact hpos i; rfl)
        (fun i => by split_ifs; rfl; exact hpos i)
    have hn : Summable (fun i => ‖if R i j then c p i else 0‖) :=
      hi.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by
        split_ifs; exact hbound p i; simp)
    have he : B j = ∑' i, if R i j then b i else 0 := by
      change (∑' i : ({i | g i = some j} : Set I), b i) = _
      rw [tsum_subtype]
      congr 1
      funext i
      simp only [Set.indicator, Set.mem_setOf_eq, hg]
    rw [he]
    exact (norm_tsum_le_tsum_norm hn).trans
      (hn.tsum_le_tsum (fun i => by split_ifs; exact hbound p i; simp) hi)

theorem rational_fourier_uniform_majorant
    (F : Type) [Field F] [NumberField F]
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    [MeasurableSpace (KPAdditiveQuotient F)] [BorelSpace (KPAdditiveQuotient F)]
    (μ : Measure (KPAdditiveQuotient F))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))
    (hKcompact : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (hKopen : IsOpen (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (f : P × KPAdditiveQuotient F → ℂ)
    (hlevel : ∀ p, HasSmoothAdditiveLevel K (fun q => f (p, q)))
    (B : (n : ℕ) → (Fin n → mixedEmbedding.mixedSpace F) → ℝ)
    (hsmooth : IsUniformArchSmoothFamily f B) :
    ∃ b : F → ℝ, Summable b ∧ (∀ ν, 0 ≤ b ν) ∧
      ∀ p ν, ‖∫ q, f (p, q) *
        ψ.toAddChar (QuotientAddGroup.mk
          (-(algebraMap F (KPAdeles F) ν * Quotient.out q))) ∂μ‖ ≤ b ν := by
  classical
  open ThetaAdditiveFourier.FiniteLevelDescent in
  obtain ⟨e, he, hj⟩ := exists_uniform_smooth_coordinates F K hKcompact hKopen f hlevel B hsmooth
  let d := Fin (Module.finrank ℚ F)
  let π : KPAdditiveQuotient F →+ UnitAddTorus d :=
    ThetaAdditiveFourier.FiniteLevelDescent.coordinateMap K e
  have hπ : Continuous π := e.continuous.comp QuotientAddGroup.continuous_mk
  have hπsur : Function.Surjective π := e.surjective.comp QuotientAddGroup.mk_surjective
  let u : P → C(UnitAddTorus d, ℂ) := fun p =>
    ⟨ThetaAdditiveFourier.FiniteLevelDescent.torusFamily K e f p,
      (ThetaAdditiveFourier.FiniteLevelDescent.continuous_torusFamily K e f hlevel
        hsmooth.1).comp (continuous_const.prodMk continuous_id)⟩
  have hu : ∀ p q, u p (π q) = f (p, q) := by
    intro p q
    exact ThetaAdditiveFourier.FiniteLevelDescent.torusFamily_mk K e f hlevel p q
  have huc : Continuous (fun z : P × UnitAddTorus d => u z.1 z.2) :=
    ThetaAdditiveFourier.FiniteLevelDescent.continuous_torusFamily K e f hlevel hsmooth.1
  have hreg : ∀ p, ContDiff ℝ (2 * (Fintype.card d + 1) : ℕ) (compactTorusLift (u p)) := by
    intro p
    let N : ℕ := 2 * (Fintype.card d + 1)
    have hn : (N : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (show (N : ℕ∞) ≤ ⊤ from le_top)
    exact (he p).of_le hn
  have hder : ∀ k ≤ 2 * (Fintype.card d + 1), Continuous
      (fun z : P × (d → ℝ) => iteratedFDeriv ℝ k (compactTorusLift (u z.1)) z.2) :=
    fun k _ => hj k
  obtain ⟨⟨b, hb, hbpos, hbnd⟩, hs, _, _, _⟩ := compactTorus_parametric_mFourier
    u huc hreg hder (compactTorus_family_derivative_bound u _ hder)
  let c : P → (d → ℤ) → ℂ := fun p n => UnitAddTorus.mFourierCoeff (u p) n
  let a : (d → ℤ) → KPAdditiveQuotient F → ℂ :=
    fun n q => UnitAddTorus.mFourier n (π q)
  have ha (n : d → ℤ) : Continuous (a n) :=
    (UnitAddTorus.mFourier n).continuous.comp hπ
  have han (n : d → ℤ) (q) : ‖a n q‖ = 1 := mFourier_norm_point n _
  let R : (d → ℤ) → F → Prop :=
    fun n ν => ∀ q, a n q * rationalFrequency F ψ ν q = 1
  have hR : ∀ n ν η, R n ν → R n η → ν = η := by
    intro n ν η hν hη
    apply rationalFrequency_injective F ψ hψ
    funext q
    have hh := (hν q).trans (hη q).symm
    exact mul_left_cancel₀ (by
      intro hz
      have hn := han n q
      rw [hz, norm_zero] at hn
      norm_num at hn) hh
  have hcoeff (p : P) (ν : F) :
      (∫ q, f (p, q) * rationalFrequency F ψ ν q ∂μ) =
        ∑' n, if R n ν then c p n else 0 := by
    let t : (d → ℤ) → KPAdditiveQuotient F → ℂ :=
      fun n q => c p n * a n q * rationalFrequency F ψ ν q
    have ht (n : d → ℤ) : Integrable (t n) μ := by
      apply integrableOn_univ.mp
      exact ((continuous_const.mul (ha n)).mul
        (rationalFrequency_continuous F ψ ν)).continuousOn.integrableOn_compact isCompact_univ
    have htn (n : d → ℤ) (q) : ‖t n q‖ = ‖c p n‖ := by
      simp only [t, norm_mul, han, mul_one]
      have hr : ‖rationalFrequency F ψ ν q‖ = 1 := ψ.unitary _
      rw [hr, mul_one]
    have hsn : Summable (fun n => ‖c p n‖) := (hs p).norm
    have hti : Summable (fun n => ∫ q, ‖t n q‖ ∂μ) := by
      simpa only [htn, integral_const, probReal_univ, one_smul] using hsn
    have hsum (q : KPAdditiveQuotient F) :
        (∑' n, t n q) = f (p, q) * rationalFrequency F ψ ν q := by
      exact ((UnitAddTorus.hasSum_mFourier_series_apply_of_summable (hs p) (π q)).mul_right
        (rationalFrequency F ψ ν q)).tsum_eq.trans (by rw [hu])
    rw [← integral_congr_ae (Filter.Eventually.of_forall hsum),
      ← integral_tsum_of_summable_integral_norm ht hti]
    apply tsum_congr
    intro n
    simp only [t, mul_assoc]

    rw [integral_const_mul, unitary_character_integral μ
      (fun q => a n q * rationalFrequency F ψ ν q) (by
        intro q r
        dsimp [a]
        rw [map_add, mFourier_add_point, rationalFrequency_add]
        ring)]
    change c p n * (if R n ν then 1 else 0) = _
    split_ifs <;> simp
  obtain ⟨b', hb', hbpos', hbnd'⟩ := uniform_majorant_partial_matching R hR c b hb hbpos hbnd
  refine ⟨b', hb', hbpos', ?_⟩
  intro p ν
  change ‖∫ q, f (p, q) * rationalFrequency F ψ ν q ∂μ‖ ≤ b' ν
  rw [hcoeff]
  exact hbnd' p ν

end DedekindZetaZeroFree.ThetaRationalFourierSummation

end
