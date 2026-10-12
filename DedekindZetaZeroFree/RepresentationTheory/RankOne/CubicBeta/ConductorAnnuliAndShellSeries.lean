module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.CubicCharacterExpansion
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SecondCountability

@[expose] public section

section

namespace DedekindZetaZeroFree.KPRamifiedBetaShell

open scoped ValuativeRel Topology

def puncturedUnitRegion (K : Type*) [Field K] [ValuativeRel K] : Set K :=
  {x | ValuativeRel.valuation K x = 1 ∧ x ≠ 1}

def unitAnnulus (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (j : ℕ) : Set K :=
  {x | ∃ u : (𝒪[K])ˣ, (u : K) = x ∧
    u ∈ CubicUnitCharacters.unitFiltration K j ∧
    u ∉ CubicUnitCharacters.unitFiltration K (j + 1)}

private lemma unit_coe_injective
    (K : Type*) [Field K] [ValuativeRel K] :
    Function.Injective (fun u : (𝒪[K])ˣ => (u : K)) := by
  intro u v h
  apply Units.ext
  exact Subtype.ext h

private lemma unit_value_one
    (K : Type*) [Field K] [ValuativeRel K] (u : (𝒪[K])ˣ) :
    ValuativeRel.valuation K (u : K) = 1 := by
  exact (Valuation.integer.integers (ValuativeRel.valuation K)).one_of_isUnit u.isUnit

private lemma exists_unit
    (K : Type*) [Field K] [ValuativeRel K] {x : K}
    (hx : ValuativeRel.valuation K x = 1) : ∃ u : (𝒪[K])ˣ, (u : K) = x := by
  let a : 𝒪[K] := ⟨x, by change ValuativeRel.valuation K x ≤ 1; rw [hx]⟩
  have ha : IsUnit a :=
    ((Valuation.integer.integers (ValuativeRel.valuation K)).isUnit_iff_valuation_eq_one).mpr hx
  exact ⟨ha.unit, congrArg (fun z : 𝒪[K] => (z : K)) ha.unit_spec⟩

private lemma filtration_separates
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : (𝒪[K])ˣ) (hu : u ≠ 1) :
    ∃ j, u ∉ CubicUnitCharacters.unitFiltration K j := by
  by_contra! h
  have hm : (u : 𝒪[K]) - 1 ∈ ⨅ j : ℕ, 𝓂[K] ^ j := by
    simp only [Submodule.mem_iInf]
    intro j
    exact (CubicUnitCharacters.unitFiltration_mem_iff K j u).mp (h j)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hm
  apply hu
  apply Units.ext
  simpa only [Ideal.mem_bot, sub_eq_zero, Units.val_one] using hm

theorem unit_annuli_partition
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] :
    MeasurableSet (puncturedUnitRegion K) ∧
    (∀ j : ℕ, MeasurableSet (unitAnnulus K j)) ∧
    Pairwise (Function.onFun Disjoint (unitAnnulus K)) ∧
    (⋃ j : ℕ, unitAnnulus K j) = puncturedUnitRegion K := by
  classical
  haveI : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
  let f : (𝒪[K])ˣ → K := fun u => (u : K)
  have hf : Function.Injective f := unit_coe_injective K
  have hc : Continuous f := by fun_prop
  have hm (j : ℕ) : MeasurableSet (f '' (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ)) := by
    exact ((((CubicUnitCharacters.unitFiltration K j).isClosed_of_isOpen
      (CubicUnitCharacters.isOpen_unitFiltration K j)).isCompact).image hc).measurableSet
  have he (j : ℕ) : unitAnnulus K j =
      f '' (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ) \
      f '' (CubicUnitCharacters.unitFiltration K (j + 1) : Set (𝒪[K])ˣ) := by
    rw [← Set.image_diff hf]
    ext x
    simp only [unitAnnulus, Set.mem_setOf_eq, Set.mem_image, Set.mem_diff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨u, hux, hu, hnu⟩
      exact ⟨u, ⟨hu, hnu⟩, hux⟩
    · rintro ⟨u, ⟨hu, hnu⟩, hux⟩
      exact ⟨u, hux, hu, hnu⟩
  have hmeas (j : ℕ) : MeasurableSet (unitAnnulus K j) := by
    rw [he]
    exact (hm j).diff (hm (j + 1))
  have hcover : (⋃ j : ℕ, unitAnnulus K j) = puncturedUnitRegion K := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, u, hux, hu, hnu⟩ := Set.mem_iUnion.mp hx
      refine ⟨?_, ?_⟩
      · rw [← hux]
        exact unit_value_one K u
      · intro hx1
        have hu1 : u = 1 := hf (by simpa [f, hux] using hx1)
        exact hnu (hu1 ▸ (CubicUnitCharacters.unitFiltration K (j + 1)).one_mem)
    · rintro ⟨hx, hx1⟩
      obtain ⟨u, hux⟩ := exists_unit K hx
      have hu1 : u ≠ 1 := by
        intro hu
        apply hx1
        simpa [hu] using hux.symm
      have hn := filtration_separates K u hu1
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.find hn ≠ 0 from by
        intro hz
        have hnot := Nat.find_spec hn
        rw [hz] at hnot
        exact hnot (by simp [CubicUnitCharacters.unitFiltration]))
      apply Set.mem_iUnion.mpr
      refine ⟨j, u, hux, ?_, ?_⟩
      · exact not_not.mp (Nat.find_min hn (by omega))
      · simpa [hj, Nat.succ_eq_add_one] using Nat.find_spec hn
  refine ⟨?_, hmeas, ?_, hcover⟩
  · rw [← hcover]
    exact MeasurableSet.iUnion hmeas
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨u, hux, hu, hnu⟩ := hxi
    obtain ⟨v, hvx, hv, hnv⟩ := hxj
    have huv : u = v := hf (hux.trans hvx.symm)
    subst v
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hnu (CubicUnitCharacters.unitFiltration_antitone K (by omega) hv)
    · exact hnv (CubicUnitCharacters.unitFiltration_antitone K (by omega) hu)

end DedekindZetaZeroFree.KPRamifiedBetaShell

end

section

namespace DedekindZetaZeroFree.KPRamifiedBetaShell

open scoped Classical ValuativeRel Topology
open MeasureTheory

noncomputable section
open scoped ENNReal

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

local instance : T2Space K := CubicUnitCharacters.t2Space_of_isValuativeTopology K
local instance : MeasurableSpace (𝒪[K])ˣ := borel _
local instance : BorelSpace (𝒪[K])ˣ := ⟨rfl⟩
private lemma emb : Topology.IsClosedEmbedding (fun u : (𝒪[K])ˣ => (u : K)) := by
 apply Continuous.isClosedEmbedding
 · fun_prop
 · intro u v huv
   apply Units.ext
   exact Subtype.ext huv
private lemma unit_abs (u : (𝒪[K])ˣ) : KPCubicHaar.abs K (u : K) = 1 := by
 have hv : ValuativeRel.valuation K (u : K) = 1 :=
   (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (ValuativeRel.valuation K))).mp u.isUnit
 have hu : (u : K) ≠ 0 := by
   intro h; simp [h] at hv
 simp [KPCubicHaar.abs, hu, hv]
private lemma units_invariant (μ : Measure K) [μ.IsAddHaarMeasure] :
 (μ.comap (fun u : (𝒪[K])ˣ => (u : K))).IsMulLeftInvariant := by
 let e := fun u : (𝒪[K])ˣ => (u : K)
 have he := (emb K).measurableEmbedding
 constructor
 intro u
 apply Measure.ext
 intro s hs
 rw [Measure.map_apply (by fun_prop) hs, he.comap_apply, he.comap_apply]
 have hset : e '' ((u * ·) ⁻¹' s) = (fun x : K => (u : K) * x) ⁻¹' (e '' s) := by
   ext x
   constructor
   · rintro ⟨v, hv, rfl⟩
     exact ⟨u*v, hv, rfl⟩
   · rintro ⟨v, hv, heq⟩
     refine ⟨u⁻¹*v, ?_, ?_⟩
     · simpa using hv
     · dsimp [e]
       have hinv : (↑↑u⁻¹ : K) = (u : K)⁻¹ := by
         apply eq_inv_of_mul_eq_one_left
         rw [← Subring.coe_mul]
         change (↑((u⁻¹ * u : (𝒪[K])ˣ) : 𝒪[K]) : K) = 1
         simp
       rw [hinv]
       have hu : (u : K) ≠ 0 := by
         have := unit_abs K u
         intro h; simp [h, KPCubicHaar.abs] at this
       change (v : K) = (u : K) * x at heq
       simpa [heq, ← mul_assoc, hu]
 rw [hset, ← Measure.map_apply (by fun_prop) (he.measurableSet_image.mpr hs)]
 rw [NonarchimedeanHaarScaling.map_mul K μ _ (by
   have := unit_abs K u
   intro h; simp [h, KPCubicHaar.abs] at this), unit_abs K u]
 simp
private lemma units_finite (μ : Measure K) [μ.IsAddHaarMeasure] :
 IsFiniteMeasure (μ.comap (fun u : (𝒪[K])ˣ => (u : K))) := by
 constructor
 rw [(emb K).measurableEmbedding.comap_apply]
 exact ((isCompact_univ : IsCompact (Set.univ : Set (𝒪[K])ˣ)).image (by fun_prop)).measure_lt_top
private lemma ideal_mass (μ : Measure K) [μ.IsAddHaarMeasure] (n : ℕ) :
 μ ((𝒪[K]).subtype '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) =
   μ (𝒪[K] : Set K) / (CubicUnitCharacters.residueCard K : ℝ≥0∞) ^ n := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 letI := isUniformAddGroup_of_addCommGroup (G := K)
 have hR : MeasurableSet (𝒪[K] : Set K) := (Valued.isClosed_integer K).measurableSet
 let ν : Measure 𝒪[K] := μ.comap (𝒪[K]).subtype
 haveI : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ
   (f := (𝒪[K]).subtype.toAddMonoidHom) (MeasurableEmbedding.subtype_coe hR)
 have hi : (𝓂[K] ^ n).toAddSubgroup.index = CubicUnitCharacters.residueCard K ^ n := by
   change (𝓂[K] ^ n : Submodule 𝒪[K] 𝒪[K]).cardQuot = _
   rw [cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field _)]
   rfl
 have hq : CubicUnitCharacters.residueCard K ≠ 0 := Nat.card_pos.ne'
 haveI : (𝓂[K] ^ n).toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr (by
   rw [hi]; exact pow_ne_zero _ hq)
 have h := AddSubgroup.index_mul_measure (𝓂[K] ^ n).toAddSubgroup
   (IsNoetherianRing.isClosed_ideal _).measurableSet ν
 rw [hi] at h
 have hm : ν ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = μ ((𝒪[K]).subtype '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) :=
   comap_subtype_coe_apply hR μ _
 have hu : ν Set.univ = μ (𝒪[K] : Set K) := by
   calc
     ν Set.univ = μ (Subtype.val '' (Set.univ : Set 𝒪[K])) :=
       comap_subtype_coe_apply hR μ Set.univ
     _ = μ (𝒪[K] : Set K) := by congr 1; ext x; simp
 rw [Nat.cast_pow] at h
 change (CubicUnitCharacters.residueCard K : ℝ≥0∞) ^ n *
   ν ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = ν Set.univ at h
 rw [hm, hu] at h
 apply (ENNReal.eq_div_iff (pow_ne_zero _ (by exact_mod_cast hq)) (by simp)).mpr
 exact h
private lemma filtration_image_pos (n : ℕ) (hn : 1 ≤ n) :
 (fun u : (𝒪[K])ˣ => (u : K)) '' (CubicUnitCharacters.unitFiltration K n : Set (𝒪[K])ˣ) =
 (fun x : K => 1 + x) '' ((𝒪[K]).subtype '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) := by
 ext x
 constructor
 · rintro ⟨u, hu, rfl⟩
   change u ∈ CubicUnitCharacters.unitFiltration K n at hu
   rw [CubicUnitCharacters.unitFiltration_mem_iff] at hu
   refine ⟨((u : 𝒪[K]) - 1 : 𝒪[K]), ⟨(u : 𝒪[K]) - 1, hu, rfl⟩, ?_⟩
   simp
 · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
   have hp : a ∈ 𝓂[K] := by simpa using (Ideal.pow_le_pow_right hn ha)
   have hunit : IsUnit (1 + a) := by
     have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a)
       ((IsLocalRing.mem_maximalIdeal _).mp ((𝓂[K]).neg_mem hp))
     simpa using h
   refine ⟨hunit.unit, ?_, ?_⟩
   · change hunit.unit ∈ CubicUnitCharacters.unitFiltration K n
     rw [CubicUnitCharacters.unitFiltration_mem_iff, hunit.unit_spec]
     simpa using ha
   · simp [hunit.unit_spec]
private lemma filtration_mass_pos (μ : Measure K) [μ.IsAddHaarMeasure] (n : ℕ) (hn : 1 ≤ n) :
 ((μ.comap (fun u : (𝒪[K])ˣ => (u : K)))
   (CubicUnitCharacters.unitFiltration K n : Set (𝒪[K])ˣ)).toReal =
 (μ (𝒪[K] : Set K)).toReal * ((CubicUnitCharacters.residueCard K : ℝ)⁻¹) ^ n := by
 rw [(emb K).measurableEmbedding.comap_apply, filtration_image_pos K n hn]
 have hs : (fun x : K => 1 + x) '' ((𝒪[K]).subtype '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) =
   (fun x : K => -1 + x) ⁻¹' ((𝒪[K]).subtype '' ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])) := by
   ext x; constructor
   · rintro ⟨y, hy, rfl⟩; simpa using hy
   · intro hx; exact ⟨-1 + x, hx, by simp⟩
 rw [hs, measure_preimage_add, ideal_mass K μ, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
   div_eq_mul_inv, inv_pow]

private theorem compact_character_integral
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] [IsFiniteMeasure ν]
    (U : Subgroup G) (hU : IsCompact (U : Set G))
    (χ : G →ₜ* CubicCharacters.Mu3) :
    IntegrableOn (fun x : G => ((χ x : ℂˣ) : ℂ)) (U : Set G) ν ∧
      (∫ x in (U : Set G), ((χ x : ℂˣ) : ℂ) ∂ν) =
        if U ≤ χ.toMonoidHom.ker then ((ν (U : Set G)).toReal : ℂ) else 0 := by
  classical
  have hf : Continuous (fun x : G => ((χ x : ℂˣ) : ℂ)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp χ.continuous)
  refine ⟨hf.continuousOn.integrableOn_compact hU, ?_⟩
  by_cases ht : U ≤ χ.toMonoidHom.ker
  · rw [if_pos ht]
    calc
      (∫ x in (U : Set G), ((χ x : ℂˣ) : ℂ) ∂ν) = ∫ _ in (U : Set G), (1 : ℂ) ∂ν :=
        setIntegral_congr_fun hU.measurableSet (fun x hx => by
          have h : χ x = 1 := ht hx
          simp [h])
      _ = ((ν (U : Set G)).toReal : ℂ) := by
        simp [setIntegral_const, Measure.real, Complex.real_smul]
  · rw [if_neg ht]
    obtain ⟨u, hu, hne⟩ : ∃ u ∈ U, χ u ≠ 1 := by
      by_contra h
      apply ht
      intro u hu
      change χ u = 1
      exact not_ne_iff.mp (fun hn => h ⟨u, hu, hn⟩)
    have hmem (x : G) : u * x ∈ U ↔ x ∈ U :=
      ⟨fun hx => by simpa using U.mul_mem (U.inv_mem hu) hx,
        fun hx => U.mul_mem hu hx⟩
    have htranslate :
        (fun x : G => (U : Set G).indicator (fun y => ((χ y : ℂˣ) : ℂ)) (u * x)) =
          (fun x : G => ((χ u : ℂˣ) : ℂ) * (U : Set G).indicator (fun y => ((χ y : ℂˣ) : ℂ)) x) := by
      funext x
      by_cases hx : x ∈ U
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mpr hx), map_mul]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).mp hx)]
    have heq : ((χ u : ℂˣ) : ℂ) * (∫ x in (U : Set G), ((χ x : ℂˣ) : ℂ) ∂ν) =
        ∫ x in (U : Set G), ((χ x : ℂˣ) : ℂ) ∂ν := by
      have h := integral_mul_left_eq_self (μ := ν)
        ((U : Set G).indicator (fun y => ((χ y : ℂˣ) : ℂ))) u
      rw [htranslate, integral_const_mul, integral_indicator hU.measurableSet] at h
      exact h
    have hc : ((χ u : ℂˣ) : ℂ) ≠ 1 := by
      intro h
      apply hne
      apply Subtype.ext
      exact Units.ext h
    by_contra hI
    exact hc ((mul_eq_right₀ hI).mp heq)

private lemma filtration_integral_exact (μ : Measure K) [μ.IsAddHaarMeasure]
 (ξ : CubicUnitCharacters.Character K) (f : ℕ) (hfpos : 1 ≤ f)
 (htrivial : CubicUnitCharacters.unitFiltration K f ≤ ξ.toMonoidHom.ker)
 (hexact : ¬ CubicUnitCharacters.unitFiltration K (f - 1) ≤ ξ.toMonoidHom.ker) (j : ℕ) :
 let ν := μ.comap (fun u : (𝒪[K])ˣ => (u : K))
 (∫ u in (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ), ((ξ u : ℂˣ) : ℂ) ∂ν) =
 if f ≤ j then ((ν (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ)).toReal : ℂ) else 0 := by
 let ν := μ.comap (fun u : (𝒪[K])ˣ => (u : K))
 letI := units_invariant K μ
 letI := units_finite K μ
 have hiff : CubicUnitCharacters.unitFiltration K j ≤ ξ.toMonoidHom.ker ↔ f ≤ j := by
   constructor
   · intro h
     by_contra hj
     have hj' : j ≤ f - 1 := by omega
     exact hexact ((CubicUnitCharacters.unitFiltration_antitone K hj').trans h)
   · intro hj
     exact (CubicUnitCharacters.unitFiltration_antitone K hj).trans htrivial
 have hcompact : IsCompact (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ) :=
   ((CubicUnitCharacters.unitFiltration K j).isClosed_of_isOpen
     (CubicUnitCharacters.isOpen_unitFiltration K j)).isCompact
 simpa only [hiff] using (compact_character_integral ν _ hcompact ξ).2
private lemma annulus_transport (μ : Measure K) [μ.IsAddHaarMeasure]
 (ξ : CubicUnitCharacters.Character K) (χ : Kˣ →ₜ* ℂˣ)
 (hχ : ∀ u : (𝒪[K])ˣ, χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
 (j : ℕ) :
 (∫ x in unitAnnulus K j, (if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)) ∂μ) =
 ∫ u in ((CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ) \
   (CubicUnitCharacters.unitFiltration K (j + 1) : Set (𝒪[K])ˣ)),
   ((ξ u : ℂˣ) : ℂ) ∂(μ.comap (fun u : (𝒪[K])ˣ => (u : K))) := by
 let e := fun u : (𝒪[K])ˣ => (u : K)
 let S := (CubicUnitCharacters.unitFiltration K j : Set (𝒪[K])ˣ) \
   (CubicUnitCharacters.unitFiltration K (j+1) : Set (𝒪[K])ˣ)
 have he := (emb K).measurableEmbedding
 have hs : e '' S = unitAnnulus K j := by
   ext x; simp only [Set.mem_image, Set.mem_sdiff, SetLike.mem_coe, unitAnnulus, Set.mem_setOf_eq, S, e]
   aesop
 have hm : MeasurableSet S :=
   (CubicUnitCharacters.isOpen_unitFiltration K j).measurableSet.diff
     (CubicUnitCharacters.isOpen_unitFiltration K (j+1)).measurableSet
 have hmap : Measure.map e ((μ.comap e).restrict S) = μ.restrict (unitAnnulus K j) := by
   rw [he.restrict_comap, he.map_comap, Measure.restrict_restrict]
   rw [Set.inter_eq_right.mpr (Set.image_subset_range e S), hs]
   exact he.measurableSet_range
 rw [← hmap, he.integral_map]
 apply integral_congr_ae
 filter_upwards [] with u
 have hu : (u : K) ≠ 0 := by
   have := unit_abs K u
   intro h; simp [h, KPCubicHaar.abs] at this
 simp only [e, dif_neg hu]
 have hm0 : Units.mk0 (u : K) hu = Units.map (𝒪[K]).subtype.toMonoidHom u := by
   apply Units.ext; rfl
 rw [hm0, hχ]

theorem additive_character_annulus_integral
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (ξ : CubicUnitCharacters.Character K)
    (f : ℕ) (hfpos : 1 ≤ f)
    (htrivial : CubicUnitCharacters.unitFiltration K f ≤ ξ.toMonoidHom.ker)
    (hexact : ¬ CubicUnitCharacters.unitFiltration K (f - 1) ≤ ξ.toMonoidHom.ker)
    (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (j : ℕ) :
    (∫ x in unitAnnulus K j,
      (if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)) ∂μ) =
      if j + 1 < f then 0 else if j < f then
        -((μ {x : K | x ∈ (ValuativeRel.valuation K).integer}).toReal : ℂ) *
          ((CubicUnitCharacters.residueCard K : ℂ)⁻¹) ^ (j + 1)
      else ((μ {x : K | x ∈ (ValuativeRel.valuation K).integer}).toReal : ℂ) *
        (1 - (CubicUnitCharacters.residueCard K : ℂ)⁻¹) *
          ((CubicUnitCharacters.residueCard K : ℂ)⁻¹) ^ j := by
  let ν := μ.comap (fun u : (𝒪[K])ˣ => (u : K))
  letI := units_invariant K μ
  letI := units_finite K μ
  have hf : Continuous (fun u : (𝒪[K])ˣ => ((ξ u : ℂˣ) : ℂ)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp ξ.continuous)
  have hint : Integrable (fun u : (𝒪[K])ˣ => ((ξ u : ℂˣ) : ℂ)) ν :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [annulus_transport K μ ξ χ hχ j]
  rw [setIntegral_sdiff (CubicUnitCharacters.isOpen_unitFiltration K (j+1)).measurableSet
    hint.integrableOn (CubicUnitCharacters.unitFiltration_antitone K (by omega))]
  rw [filtration_integral_exact K μ ξ f hfpos htrivial hexact j,
    filtration_integral_exact K μ ξ f hfpos htrivial hexact (j+1)]
  have hmass (n : ℕ) (hn : 1 ≤ n) :
    ((ν (CubicUnitCharacters.unitFiltration K n : Set (𝒪[K])ˣ)).toReal : ℂ) =
    ((μ {x : K | x ∈ (ValuativeRel.valuation K).integer}).toReal : ℂ) *
      ((CubicUnitCharacters.residueCard K : ℂ)⁻¹) ^ n := by
    rw [filtration_mass_pos K μ n hn]
    push_cast
    rfl
  split_ifs with h1 h2 h3 h4 <;> try omega
  all_goals try simp only [sub_zero, sub_self, zero_sub]
  all_goals try {rw [hmass (j+1) (by omega)]; ring}
  all_goals try {rw [hmass j (by omega), hmass (j+1) (by omega), pow_succ]; ring}

end

end DedekindZetaZeroFree.KPRamifiedBetaShell

end

section

namespace DedekindZetaZeroFree.KPRamifiedBetaShell

open scoped Classical ValuativeRel Topology
open ValuativeRel WithZero
open MeasureTheory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
private lemma pi_log {π : 𝒪[K]} (hp : Irreducible π) :
    log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K π)) = -1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have h0 : e (valuation K π) ≠ 0 := by
    simpa [e] using (Valuation.integer.integers (valuation K)).valuation_irreducible_pos hp |>.ne'
  have hlt : log (e (valuation K π)) < 0 := by
    have ht : valuation K π < 1 := (Valuation.integer.integers (valuation K)).valuation_irreducible_lt_one hp
    have : e (valuation K π) < 1 := by simpa using e.strictMono ht
    simpa using (log_lt_log h0 one_ne_zero).mpr this
  obtain ⟨y, hy⟩ := valuation_surjective (e.symm (exp (-1)))
  have hylt : valuation K y < 1 := by
    rw [hy, ← map_one e.symm]
    apply e.symm.strictMono
    simpa using (exp_lt_exp (a := (-1 : ℤ)) (b := 0)).mpr (by omega)
  let z : 𝒪[K] := ⟨y, hylt.le⟩
  have hz : z ∈ 𝓂[K] := by
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit z
    rw [(Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact hylt.ne
  have hle : valuation K y ≤ valuation K π := by
    have heq := hp.maximalIdeal_eq_setOfPred_le_v_coe
    have hz' : z ∈ (𝓂[K] : Set 𝒪[K]) := hz
    rw [heq] at hz'
    exact hz'
  have hl : -1 ≤ log (e (valuation K π)) := by
    have he : exp (-1) ≤ e (valuation K π) := by
      simpa [hy] using e.strictMono.monotone hle
    simpa using (log_le_log (by simp) h0).mpr he
  change log (e (valuation K π)) = -1
  omega

private lemma annulus_values (j : ℕ) {x : K} (hx : x ∈ unitAnnulus K j) :
    x ≠ 0 ∧ valuation K x = 1 ∧ 1-x ≠ 0 ∧
    log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (1-x))) = -(j : ℤ) := by
  obtain ⟨u, rfl, hu, hn⟩ := hx
  have hv : valuation K (u : K) = 1 :=
    (Valuation.integer.integers (valuation K)).one_of_isUnit u.isUnit
  have hzero : (u : K) ≠ 0 := by intro h; simpa [h] using hv
  have hd : (1 - (u : K)) ≠ 0 := by
    intro h
    have he : (u : 𝒪[K]) = 1 := by
      apply Subtype.ext
      simpa using (sub_eq_zero.mp h).symm
    exact hn (by rw [CubicUnitCharacters.unitFiltration_mem_iff K, he]; simp)
  refine ⟨hzero, hv, hd, ?_⟩
  obtain ⟨π, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [CubicUnitCharacters.unitFiltration_mem_iff K] at hu hn
  change (u : 𝒪[K]) - 1 ∈ ((𝓂[K] ^ j : Ideal 𝒪[K]) : Set 𝒪[K]) at hu
  change (u : 𝒪[K]) - 1 ∉ ((𝓂[K] ^ (j+1) : Ideal 𝒪[K]) : Set 𝒪[K]) at hn
  rw [hp.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow] at hu hn
  change valuation K ((u : K) - 1) ≤ valuation K (π : K) ^ j at hu
  change ¬ valuation K ((u : K) - 1) ≤ valuation K (π : K) ^ (j+1) at hn
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have h0 : e (valuation K ((u : K) - 1)) ≠ 0 := by
    have hnz : valuation K ((u : K) - 1) ≠ 0 := by
      exact (valuation K).ne_zero_iff.mpr (sub_ne_zero.mpr (sub_ne_zero.mp hd).symm)
    simpa using e.toMulEquiv.injective.ne hnz
  have hπ0 : e (valuation K (π : K)) ≠ 0 := by
    simpa using (Valuation.integer.integers (valuation K)).valuation_irreducible_pos hp |>.ne'
  have hup := e.strictMono.monotone hu
  have hlo := e.strictMono (lt_of_not_ge hn)
  rw [map_pow] at hup hlo
  have hup' := (log_le_log h0 (pow_ne_zero _ hπ0)).mpr hup
  have hlo' := (log_lt_log (pow_ne_zero _ hπ0) h0).mpr hlo
  have hπ : log (e (valuation K (π : K))) = -1 := pi_log K hp
  simp only [log_pow, hπ, nsmul_eq_mul, mul_neg, mul_one] at hup' hlo'
  have heq : log (e (valuation K ((u : K) - 1))) = -(j : ℤ) := by omega
  change log (e (valuation K (1 - (u : K)))) = -(j : ℤ)
  rw [(valuation K).map_sub_swap]
  exact heq

private lemma weight_power (q : ℝ) (hq : 0 ≤ q) (s : ℂ) (j : ℕ) :
    ((q ^ (-(j : ℤ)) : ℝ) : ℂ) ^ (-s) = ((q : ℂ) ^ s) ^ j := by
  rw [Complex.ofReal_zpow]
  rw [← Complex.cpow_int_mul' (x := (q : ℂ)) (n := -(j : ℤ))]
  · rw [show ((-(j : ℤ) : ℤ) : ℂ) * (-s) = (j : ℂ) * s by push_cast; ring]
    exact Complex.cpow_nat_mul _ _ _
  · simp [Complex.arg_ofReal_of_nonneg hq, Real.pi_pos]
  · simp [Complex.arg_ofReal_of_nonneg hq, Real.pi_pos.le]

theorem weighted_annulus_integral
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (χ : Kˣ →ₜ* ℂˣ) (s : ℂ) (j : ℕ) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))
    let I : K → ℂ := fun x ↦ if hx : x = 0 then 0 else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
    (∫ x in unitAnnulus K j, I x ∂ν) =
      (∫ x in unitAnnulus K j,
        (if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)) ∂μ) *
          ((CubicUnitCharacters.residueCard K : ℂ) ^ s) ^ j := by
  dsimp only
  let A : K → ℝ := fun x ↦ if x = 0 then 0 else
    (CubicUnitCharacters.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K x))
  have hm : MeasurableSet (unitAnnulus K j) := (unit_annuli_partition K).2.1 j
  have hA (x : K) (hx : x ∈ unitAnnulus K j) : A x = 1 := by
    obtain ⟨hn, hv, hd, hl⟩ := annulus_values K j hx
    simp [A, hn, hv]
  have hν : (μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))).restrict (unitAnnulus K j) =
      μ.restrict (unitAnnulus K j) := by
    rw [restrict_withDensity hm]
    calc
      _ = (μ.restrict (unitAnnulus K j)).withDensity 1 := by
        apply withDensity_congr_ae
        filter_upwards [ae_restrict_mem hm] with x hx
        simp [hA x hx]
      _ = _ := withDensity_one
  change (∫ x in unitAnnulus K j,
    (if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ) * (A (1-x) : ℂ) ^ (-s))
    ∂(μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹)))) = _
  rw [hν]
  calc
    _ = ∫ x in unitAnnulus K j,
      (if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)) *
        ((CubicUnitCharacters.residueCard K : ℂ) ^ s) ^ j ∂μ := by
      apply setIntegral_congr_fun hm
      intro x hx
      obtain ⟨hn, hv, hd, hl⟩ := annulus_values K j hx
      simp only [dif_neg hn]
      congr 1
      simp only [A, if_neg hd, hl]
      exact weight_power _ (Nat.cast_nonneg _) s j
    _ = _ := integral_mul_const _ _

end DedekindZetaZeroFree.KPRamifiedBetaShell

end

section

namespace DedekindZetaZeroFree.KPRamifiedBetaShell

open scoped Classical ValuativeRel Topology
open MeasureTheory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local instance : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
local instance : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
private lemma unit_val (u : (𝒪[K])ˣ) : ValuativeRel.valuation K (u : K) = 1 := by
  exact (Valuation.integer.integers (ValuativeRel.valuation K)).one_of_isUnit u.isUnit
 noncomputable def mulEquiv (u : (𝒪[K])ˣ) : K ≃ₜ+ K :=
  { DistribMulAction.toAddEquiv K (Units.map (𝒪[K]).subtype.toMonoidHom u) with
    continuous_toFun := by change Continuous (fun x : K => (u : K) * x); fun_prop
    continuous_invFun := by change Continuous (fun x : K => ((u⁻¹ : (𝒪[K])ˣ) : K) * x); fun_prop }
private lemma mulEquiv_apply (u : (𝒪[K])ˣ) (x : K) : mulEquiv K u x = (u : K) * x := rfl
private lemma unit_preserving (μ : Measure K) [μ.IsAddHaarMeasure] (u : (𝒪[K])ˣ) :
    MeasurePreserving (mulEquiv K u) μ μ := by
  letI := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable K
  let e := mulEquiv K u
  have hpre : e ⁻¹' {x : K | ValuativeRel.valuation K x ≤ 1} =
      {x : K | ValuativeRel.valuation K x ≤ 1} := by
    ext x
    simp [e, mulEquiv_apply, map_mul, unit_val]
  haveI : (μ.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map (μ := μ) e
  have hm := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  have ho : IsOpen {x : K | ValuativeRel.valuation K x ≤ 1} := Valued.isOpen_integer K
  have hc := IsNonarchimedeanLocalField.isCompact_closedBall K 1
  have hp : μ {x : K | ValuativeRel.valuation K x ≤ 1} ≠ 0 :=
    (ho.measure_pos μ ⟨0, by simp⟩).ne'
  have heq : (Measure.addHaarScalarFactor (μ.map e) μ : ENNReal) = 1 := by
    have hh := congrArg (fun m : Measure K => m {x : K | ValuativeRel.valuation K x ≤ 1}) hm
    rw [Measure.map_apply (f := (e : K → K)) e.toHomeomorph.continuous.measurable ho.measurableSet, hpre,
      Measure.smul_apply] at hh
    change μ {x : K | ValuativeRel.valuation K x ≤ 1} =
      (Measure.addHaarScalarFactor (μ.map e) μ : ENNReal) * μ {x : K | ValuativeRel.valuation K x ≤ 1} at hh
    exact (ENNReal.mul_left_inj hp hc.measure_ne_top).mp (by simpa using hh.symm)
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hm]
  have : Measure.addHaarScalarFactor (μ.map e) μ = 1 := by exact_mod_cast heq
  rw [this, one_smul]
private lemma density_preserving {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (w : X → ENNReal) (hw : ∀ x, w (e x) = w x) :
    MeasurePreserving e (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨e.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  have hi : (e ⁻¹' s).indicator w = (s.indicator w) ∘ e := by
    ext x
    by_cases hx : e x ∈ s <;> simp [hx, hw x]
  rw [hi]
  exact (e.measurableEmbedding.lintegral_map (μ := μ) (s.indicator w)).symm.trans
    (by rw [he.map_eq])
private lemma singleton_null (μ : Measure K) [μ.IsAddHaarMeasure] : NullSingletonClass μ := by
  have hzero : μ {(0 : K)} = 0 := by
    by_contra h
    have hi : (𝒪[K] : Set K).Infinite := by
      obtain ⟨a, ha, ha1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
      have hj : Function.Injective (fun n : ℕ => a ^ n) := by
        intro m n h
        have hv := congrArg (ValuativeRel.valuation K) h
        simp only [map_pow] at hv
        exact (pow_right_strictAnti₀ (by simpa only [zero_lt_iff, ne_eq, map_eq_zero] using ha) ha1).injective hv
      exact (Set.infinite_range_of_injective hj).mono (by
        rintro x ⟨n, rfl⟩
        change (ValuativeRel.valuation K) (a ^ n) ≤ 1
        rw [map_pow]
        exact pow_le_one₀ zero_le ha1.le)
    have ht : μ (𝒪[K] : Set K) = ⊤ :=
      hi.meas_eq_top ⟨μ {0}, h, fun x _ => (Measure.addHaar_singleton μ x).ge⟩
    exact (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_ne_top ht
  exact ⟨fun x => (Measure.addHaar_singleton μ x).trans hzero⟩
private lemma sphere_measurable : MeasurableSet {x : K | ValuativeRel.valuation K x = 1} := by
  have hh := (Valued.isOpen_sphere K (r := (Valued.v.restrict (1 : K))) (by simp)).measurableSet
  convert hh using 1
  ext x
  simpa only [IsValuativeTopology.v_eq_valuation, Set.mem_setOf_eq, map_one] using
    ((ValuativeRel.valuation K).restrict_inj (x := x) (y := 1)).symm

theorem integral_complement_units_eq_zero
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (ξ : CubicUnitCharacters.Character K) (hξ : ξ ≠ 1)
    (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (s : ℂ) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))
    let I : K → ℂ := fun x ↦ if hx : x = 0 then 0 else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
    Integrable I ν → (∫ x in (puncturedUnitRegion K)ᶜ, I x ∂ν) = 0 := by
  classical
  let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))
  let I : K → ℂ := fun x ↦ if hx : x = 0 then 0 else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
  change Integrable I ν → (∫ x in (puncturedUnitRegion K)ᶜ, I x ∂ν) = 0
  intro hI
  have hu : ∃ u : (𝒪[K])ˣ, ((ξ u : ℂˣ) : ℂ) ≠ 1 := by
    by_contra h
    push Not at h
    apply hξ
    ext u
    exact h u
  obtain ⟨u, hu⟩ := hu
  let e := mulEquiv K u
  have hA (x : K) : A (e x) = A x := by
    by_cases hx : x = 0
    · simp [A, e, mulEquiv_apply, hx]
    · have he : e x ≠ 0 := by
        intro hh
        apply hx
        exact e.toEquiv.injective (hh.trans (by simp [e, mulEquiv_apply]))
      simp only [A, if_neg hx, if_neg he]
      simp only [e, mulEquiv_apply, map_mul, unit_val, one_mul]
  have heν : MeasurePreserving e.toHomeomorph.toMeasurableEquiv ν ν :=
    density_preserving μ e.toHomeomorph.toMeasurableEquiv (unit_preserving K μ u)
      (fun x => ENNReal.ofReal ((A x)⁻¹)) (fun x => by
        change ENNReal.ofReal ((A (e x))⁻¹) = _
        rw [hA])
  let S : Set K := {x | ValuativeRel.valuation K x ≠ 1}
  have hS : MeasurableSet S := (sphere_measurable K).compl
  have hpre : e.toHomeomorph.toMeasurableEquiv ⁻¹' S = S := by
    ext x
    change (ValuativeRel.valuation K (e x) ≠ 1) ↔ _
    simp only [e, mulEquiv_apply, map_mul, unit_val, one_mul, S, Set.mem_setOf_eq]
  have hshift (x : K) (hxS : x ∈ S) : I (e x) = ((ξ u : ℂˣ) : ℂ) * I x := by
    by_cases hx : x = 0
    · simp [I, e, mulEquiv_apply, hx]
    have he : e x ≠ 0 := by
      intro hh
      apply hx
      exact e.toEquiv.injective (hh.trans (by simp [e, mulEquiv_apply]))
    have hv : ValuativeRel.valuation K (1 - e x) = ValuativeRel.valuation K (1 - x) := by
      have hval : ValuativeRel.valuation K (e x) = ValuativeRel.valuation K x := by
        simp [e, mulEquiv_apply, map_mul, unit_val]
      have hn : ValuativeRel.valuation K x ≠ 1 := hxS
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · rw [(ValuativeRel.valuation K).map_sub_eq_of_lt_left (by simpa [hval] using hlt),
          (ValuativeRel.valuation K).map_sub_eq_of_lt_left (by simpa using hlt)]
      · rw [(ValuativeRel.valuation K).map_sub_eq_of_lt_right (by simpa [hval] using hgt),
          (ValuativeRel.valuation K).map_sub_eq_of_lt_right (by simpa using hgt), hval]
    have hnx : 1 - x ≠ 0 := by
      intro hh
      have : x = 1 := (sub_eq_zero.mp hh).symm
      exact hxS (by simp [this])
    have hne : 1 - e x ≠ 0 := by
      intro hh
      have hv0 : ValuativeRel.valuation K (1 - x) = 0 := by rw [← hv, hh, map_zero]
      exact hnx (by simpa only [map_eq_zero] using hv0)
    have hAA : A (1 - e x) = A (1 - x) := by simp only [A, if_neg hne, if_neg hnx, hv]
    have hunit : Units.mk0 (e x) he =
        Units.map (𝒪[K]).subtype.toMonoidHom u * Units.mk0 x hx := by
      apply Units.ext
      rfl
    simp only [I, dif_neg hx, dif_neg he, hAA, hunit, map_mul, hχ, Units.val_mul]
    ring
  have hi := (heν.restrict_preimage hS).integral_comp
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding I
  rw [hpre] at hi
  have hi' : ((ξ u : ℂˣ) : ℂ) * (∫ x in S, I x ∂ν) = ∫ x in S, I x ∂ν := by
    rw [← integral_const_mul]
    exact (setIntegral_congr_fun hS (fun x hx => (hshift x hx).symm)).trans hi
  have hzero : (∫ x in S, I x ∂ν) = 0 := by
    have hh : (((ξ u : ℂˣ) : ℂ) - 1) * (∫ x in S, I x ∂ν) = 0 := by
      rw [sub_mul, one_mul, hi', sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hu)
  haveI : NullSingletonClass μ := singleton_null K μ
  have hsets : (puncturedUnitRegion K)ᶜ =ᵐ[ν] S := by
    filter_upwards [show ∀ᵐ x ∂ν, x ≠ (1 : K) from ν.ae_ne _] with x hx
    simp [puncturedUnitRegion, S, hx]
  rw [setIntegral_congr_set hsets, hzero]

end DedekindZetaZeroFree.KPRamifiedBetaShell

end

section

namespace DedekindZetaZeroFree.KPRamifiedBetaConductorSeries

open scoped Classical

open scoped ValuativeRel Topology
open MeasureTheory

theorem beta_geometric_ratio_norm_lt_one (q : ℝ) (hq : 1 < q)
    (s : ℂ) (hs : s.re < 1) : ‖(q : ℂ)⁻¹ * (q : ℂ) ^ s‖ < 1 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0,
    Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hpow : q ^ s.re < q := by
    simpa using (Real.rpow_lt_rpow_of_exponent_lt hq hs)
  calc q⁻¹ * q ^ s.re = q ^ s.re / q := by ring
       _ < 1 := (div_lt_one hq0).mpr hpow

theorem conductor_annulus_series_hasSum (a m L : ℂ) (f : ℕ) (hf : 1 ≤ f)
    (h : ‖a * L‖ < 1) :
    HasSum (fun j : ℕ =>
      if j + 1 < f then 0 else if j < f then -m * a ^ (j + 1) * L ^ j
      else m * (1 - a) * (a * L) ^ j)
      (m * (1 - a) * (∑' j : ℕ, (a * L) ^ (j + f)) -
        m * a ^ f * L ^ (f - 1)) := by
  let c : ℕ → ℂ := fun j =>
    if j + 1 < f then 0 else if j < f then -m * a ^ (j + 1) * L ^ j
    else m * (1 - a) * (a * L) ^ j
  change HasSum c _
  have hgeom : Summable (fun j : ℕ => (a * L) ^ j) :=
    summable_geometric_of_norm_lt_one h
  have hshift : Summable (fun j : ℕ => (a * L) ^ (j + f)) := by
    have heq : (fun j : ℕ => (a * L) ^ (j + f)) =
        (fun j : ℕ => (a * L) ^ f * (a * L) ^ j) := by
      funext j
      rw [pow_add, mul_comm]
    rw [heq]
    exact hgeom.mul_left _
  have htail : HasSum (fun j : ℕ => c (j + f))
      (m * (1 - a) * ∑' j : ℕ, (a * L) ^ (j + f)) := by
    have heq : (fun j : ℕ => c (j + f)) =
        (fun j : ℕ => m * (1-a) * (a * L) ^ (j + f)) := by
      funext j
      simp [c, show ¬ j + f < f by omega,
        show ¬ j + f + 1 < f by omega]
    rw [heq]
    rw [← tsum_mul_left]
    exact (hshift.mul_left _).hasSum
  have hsum : ∑ j ∈ Finset.range f, c j =
      -(m * a ^ f * L ^ (f - 1)) := by
    rw [Finset.sum_eq_single (f - 1)]
    · simp [c, show f - 1 + 1 = f by omega,
        show f - 1 < f by omega, neg_mul, mul_assoc]
    · intro j hj hne
      simp only [Finset.mem_range] at hj
      simp [c, show j + 1 < f by omega]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  have h := (hasSum_nat_add_iff f).mp htail
  rw [hsum] at h
  convert h using 1 <;> abel

theorem integral_eq_conductor_series_of_shell_integrals
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (I : X → ℂ)
    (S : Set X) (hS : MeasurableSet S) (shell : ℕ → Set X)
    (hmeas : ∀ j, MeasurableSet (shell j))
    (hdisj : Pairwise (Function.onFun Disjoint shell))
    (hcover : (⋃ j, shell j) = S)
    (hI : Integrable I ν) (hrest : (∫ x in Sᶜ, I x ∂ν) = 0)
    (a m L : ℂ) (f : ℕ) (hf : 1 ≤ f) (h : ‖a * L‖ < 1)
    (hshell : ∀ j, (∫ x in shell j, I x ∂ν) =
      if j + 1 < f then 0 else if j < f then -m * a ^ (j + 1) * L ^ j
      else m * (1 - a) * (a * L) ^ j) :
    (∫ x, I x ∂ν) =
      m * (1 - a) * (∑' j : ℕ, (a * L) ^ (j + f)) -
        m * a ^ f * L ^ (f - 1) := by
  have hsum := hasSum_integral_iUnion hmeas hdisj hI.integrableOn
  rw [hcover] at hsum
  simp_rw [hshell] at hsum
  have hvalue := hsum.unique (conductor_annulus_series_hasSum a m L f hf h)
  rw [← integral_add_compl hS hI, hrest, add_zero]
  exact hvalue

theorem integral_eq_shell_series
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (ξ : CubicUnitCharacters.Character K) (hξ : ξ ≠ 1)
    (f : ℕ) (hfpos : 1 ≤ f)
    (htrivial : CubicUnitCharacters.unitFiltration K f ≤ ξ.toMonoidHom.ker)
    (hexact : ¬ CubicUnitCharacters.unitFiltration K (f - 1) ≤ ξ.toMonoidHom.ker)
    (χ : Kˣ →ₜ* ℂˣ)
    (hχ : ∀ u : (𝒪[K])ˣ,
      χ (Units.map (𝒪[K]).subtype.toMonoidHom u) = (ξ u : ℂˣ))
    (s : ℂ) (hs1 : s.re < 1) :
    let A : K → ℝ := fun x ↦ if x = 0 then 0 else
      (CubicUnitCharacters.residueCard K : ℝ) ^
        WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
          (ValuativeRel.valuation K x))
    let I : K → ℂ := fun x ↦ if hx : x = 0 then 0 else
      (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)
    let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
    Integrable I ν →
    (∫ x, I x ∂ν) =
      ((μ {x : K | x ∈ (ValuativeRel.valuation K).integer}).toReal : ℂ) *
        (1 - (CubicUnitCharacters.residueCard K : ℂ)⁻¹) *
        (∑' j : ℕ, ((CubicUnitCharacters.residueCard K : ℂ)⁻¹ *
          (CubicUnitCharacters.residueCard K : ℂ) ^ s) ^ (j + f)) -
      ((μ {x : K | x ∈ (ValuativeRel.valuation K).integer}).toReal : ℂ) *
        ((CubicUnitCharacters.residueCard K : ℂ)⁻¹) ^ f *
        ((CubicUnitCharacters.residueCard K : ℂ) ^ s) ^ (f - 1) := by
  dsimp only
  intro hI
  let q : ℝ := CubicUnitCharacters.residueCard K
  let a : ℂ := (q : ℂ)⁻¹
  let L : ℂ := (q : ℂ) ^ s
  let m : ℂ := ((μ {x : K | x ∈ (ValuativeRel.valuation K).integer}).toReal : ℂ)
  let A : K → ℝ := fun x ↦ if x = 0 then 0 else
    (CubicUnitCharacters.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (ValuativeRel.valuation K x))
  let I : K → ℂ := fun x ↦ if hx : x = 0 then 0 else
    (χ (Units.mk0 x hx) : ℂ) * (A (1 - x) : ℂ) ^ (-s)
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal ((A x)⁻¹))
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  have hpartition := KPRamifiedBetaShell.unit_annuli_partition K
  obtain ⟨hS, hmeas, hdisj, hcover⟩ := hpartition
  have hrest : (∫ x in (KPRamifiedBetaShell.puncturedUnitRegion K)ᶜ,
      I x ∂ν) = 0 :=
    KPRamifiedBetaShell.integral_complement_units_eq_zero K μ ξ hξ χ hχ s hI
  have hshell (j : ℕ) :
      (∫ x in KPRamifiedBetaShell.unitAnnulus K j, I x ∂ν) =
        if j + 1 < f then 0 else if j < f then
          -m * a ^ (j + 1) * L ^ j else
          m * (1 - a) * (a * L) ^ j := by
    rw [show (∫ x in KPRamifiedBetaShell.unitAnnulus K j, I x ∂ν) =
      (∫ x in KPRamifiedBetaShell.unitAnnulus K j,
        (if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)) ∂μ) * L ^ j
      from KPRamifiedBetaShell.weighted_annulus_integral K μ χ s j]
    rw [KPRamifiedBetaShell.additive_character_annulus_integral K μ ξ
      f hfpos htrivial hexact χ hχ j]
    split_ifs <;> simp only [q, a, L, m, mul_pow, Complex.ofReal_natCast] <;> ring
  have hratio : ‖a * L‖ < 1 := beta_geometric_ratio_norm_lt_one q hq s hs1
  exact integral_eq_conductor_series_of_shell_integrals ν I
    (KPRamifiedBetaShell.puncturedUnitRegion K) hS
    (KPRamifiedBetaShell.unitAnnulus K) hmeas hdisj hcover
    hI hrest a m L f hfpos hratio hshell

end DedekindZetaZeroFree.KPRamifiedBetaConductorSeries

end
