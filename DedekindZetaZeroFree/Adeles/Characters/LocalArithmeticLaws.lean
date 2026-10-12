module

public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderClassCharacters

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

open Filter Topology

private lemma pow_near_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : K) (hx : ‖x - 1‖ < 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  have hnorm : ‖x‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (x - 1) (1 : K)
    simpa [max_eq_right hx.le] using h
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : x ^ (n + 1) - 1 = (x ^ n - 1) * x + (x - 1) := by ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans (by simpa using ih)

private lemma local_circle_character {K : Type*} [NormedField K] [IsUltrametricDist K]
    (Φ : Kˣ →* Circle) (hc : Continuous Φ) : IsLocallyConstant Φ := by
  have harc : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hnh : Φ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Kˣ) :=
    hc.continuousAt.preimage_mem_nhds ((Circle.isOpen_centeredArc _).mem_nhds (by simpa using harc))
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hnh
  obtain ⟨s, hs, hsub⟩ := Filter.mem_comap.mp hnh
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hkill (u : Kˣ) (hu : ‖(u : K) - 1‖ < δ) : Φ u = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n hn
    rw [← map_pow]
    apply hsub
    apply hball
    change dist (↑(u ^ n) : K) (↑(1 : Kˣ) : K) < ε
    rw [dist_eq_norm]
    exact (pow_near_one (u : K) (hu.trans_le (min_le_right _ _)) n).trans_lt
      (hu.trans_le (min_le_left _ _))
  rw [IsLocallyConstant.iff_exists_open]
  intro z
  refine ⟨{t | ‖((t * z⁻¹ : Kˣ) : K) - 1‖ < δ}, ?_, ?_, ?_⟩
  · exact isOpen_lt (by fun_prop) continuous_const
  · simpa using hδ
  · intro t ht
    have h := hkill (t * z⁻¹) ht
    simpa only [map_mul, map_inv, mul_inv_eq_one] using h

private lemma continuous_ideleClassGroup_ofAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) := by
  apply continuous_quot_mk.comp
  apply Continuous.units_map
  change Continuous (fun z : v.adicCompletion F =>
    ((1 : InfiniteAdeleRing F), FiniteAdeleRing.ofAdicCompletion F v z))
  apply Continuous.prodMk continuous_const
  let a := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))
  let f : v.adicCompletion F → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      a (Filter.principal {v}ᶜ) := fun z => ⟨Pi.mulSingle v z, by
        rw [Filter.eventually_principal]
        intro w hw
        rw [Pi.mulSingle_eq_of_ne (by simpa using hw)]
        exact one_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr (by
    change Continuous (fun z : v.adicCompletion F => Pi.mulSingle v z)
    fun_prop)
  have hi : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) := by
    simp
  exact (RestrictedProduct.continuous_inclusion hi).comp hf

theorem localArithmeticLaws_finite (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (hcont : Continuous Φ)
    (v : HeightOneSpectrum (𝓞 F)) : IsLocallyConstant (A.ideleFiniteComponent Φ v) :=
  local_circle_character _ (hcont.comp (continuous_ideleClassGroup_ofAdicCompletion v))

private lemma pi_character_trivial {ι : Type*} {K : ι → Type*}
    [∀ i, CommMonoid (K i)] [∀ i, TopologicalSpace (K i)]
    {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    (χ : ((i : ι) → K i) →* M) (hc : Continuous χ)
    (h : ∀ i z, χ (Pi.mulSingle i z) = 1) : ∀ z, χ z = 1 := by
  intro z
  have hp : HasProd (fun i => Pi.mulSingle i (z i)) z := by
    rw [Pi.hasProd]
    intro j
    have heq : (fun i => Pi.mulSingle i (z i) j) = (fun i => if i = j then z j else 1) := by
      funext i
      by_cases hij : i = j
      · subst i; simp
      · simp [Pi.mulSingle_eq_of_ne' hij, hij]
    rw [heq]
    exact hasProd_ite_eq j (z j)
  have hm := hp.map χ hc
  have hones : (fun i => χ (Pi.mulSingle i (z i))) = (fun _ : ι => (1 : M)) := by
    funext i
    exact h i (z i)
  change HasProd (fun i => χ (Pi.mulSingle i (z i))) (χ z) at hm
  rw [hones] at hm
  exact hm.unique hasProd_one

 def outsideUnitGroup (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (v.adicCompletion F)ˣ :=
  if v ∈ A.Sf then ⊥ else (v.adicCompletionIntegers F).units

 def outsideUnitsIdele (A : SArithmeticData F) :
    ((v : HeightOneSpectrum (𝓞 F)) → outsideUnitGroup A v) →* _root_.IdeleGroup F where
  toFun z := (1, ⟨fun v => (z v).val, Filter.Eventually.of_forall (fun v => by
    have hz := (z v).property
    dsimp [outsideUnitGroup] at hz
    split_ifs at hz with hv
    · have he : (z v).val = 1 := hz
      change (z v).val ∈ (v.adicCompletionIntegers F).units
      rw [he]
      exact (v.adicCompletionIntegers F).units.one_mem
    · exact hz)⟩)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by
    apply Prod.ext
    · simp
    · rfl

private lemma outsideUnitsIdele_continuous (A : SArithmeticData F) :
    Continuous (outsideUnitsIdele A) := by
  apply Continuous.prodMk continuous_const
  let R := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletion F)ˣ
  let B := fun v : HeightOneSpectrum (𝓞 F) => ((v.adicCompletionIntegers F).units : Set (R v))
  let f : ((v : HeightOneSpectrum (𝓞 F)) → outsideUnitGroup A v) → (v : HeightOneSpectrum (𝓞 F)) → B v :=
    fun z v => ⟨(z v).val, by
      have hz := (z v).property
      dsimp [outsideUnitGroup] at hz
      split_ifs at hz with hv
      · have he : (z v).val = 1 := hz
        change (z v).val ∈ (v.adicCompletionIntegers F).units
        rw [he]
        exact (v.adicCompletionIntegers F).units.one_mem
      · exact hz⟩
  have hf : Continuous f := by
    apply continuous_pi
    intro v
    exact (continuous_subtype_val.comp (continuous_apply v)).subtype_mk _
  exact RestrictedProduct.isEmbedding_structureMap.continuous.comp hf

theorem outside_units_trivial (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hcont : Continuous Φ) (hunram : A.IdeleCharacterUnramifiedOutside Φ)
    (x : NumberField.IdeleGroup (𝓞 F) F)
    (hinf : ∀ w : InfinitePlace F, x.val.1 w = 1)
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ A.Sf → x.val.2 v = 1)
    (hout : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → Valued.v (x.val.2 v) = 1) :
    Φ (QuotientGroup.mk x) = 1 := by
  let e := _root_.IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F
  let χ := Φ.comp ((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)).comp
    (e.toMonoidHom.comp (outsideUnitsIdele A)))
  have hc : Continuous χ := hcont.comp (continuous_quot_mk.comp
    (e.continuous.comp (outsideUnitsIdele_continuous A)))
  have hkill : ∀ v z, χ (Pi.mulSingle v z) = 1 := by
    intro v z
    have he : e (outsideUnitsIdele A (Pi.mulSingle v z)) =
        Units.map (NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F v) z.val := by
      apply Units.ext
      apply Prod.ext
      · rfl
      · apply RestrictedProduct.ext
        intro w
        by_cases hw : w = v
        · subst w
          change (↑((Pi.mulSingle (M := fun v => outsideUnitGroup A v) v z v).val) : v.adicCompletion F) = Pi.mulSingle v (z.val : v.adicCompletion F) v
          simp
        · change (↑((Pi.mulSingle (M := fun v => outsideUnitGroup A v) v z w).val) : w.adicCompletion F) = Pi.mulSingle v (z.val : v.adicCompletion F) w
          simp [Pi.mulSingle_eq_of_ne hw]
    change Φ (QuotientGroup.mk (e (outsideUnitsIdele A (Pi.mulSingle v z)))) = 1
    rw [he]
    by_cases hv : v ∈ A.Sf
    · have hz : z.val = 1 := by
        have hz := z.property
        simpa [outsideUnitGroup, hv] using hz
      simp [hz]
    · apply hunram v hv z.val
      rw [← HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
      simpa [outsideUnitGroup, hv] using z.property
  let y := e.symm x
  let z : (v : HeightOneSpectrum (𝓞 F)) → outsideUnitGroup A v := fun v => ⟨y.2 v, by
    dsimp [outsideUnitGroup]
    split_ifs with hv
    · change y.2 v = 1
      apply Units.ext
      exact hS v hv
    · rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
      exact hout v hv⟩
  have he : outsideUnitsIdele A z = y := by
    apply Prod.ext
    · apply Units.ext
      funext w
      exact (hinf w).symm
    · rfl
  have h := pi_character_trivial χ hc hkill z
  change Φ (QuotientGroup.mk (e (outsideUnitsIdele A z))) = 1 at h
  rwa [he, ContinuousMulEquiv.apply_symm_apply] at h

 def sIdele (A : SArithmeticData F) (y : A.G) : NumberField.IdeleGroup (𝓞 F) F :=
  (∏ w : InfinitePlace F, Units.map (NumberField.AdeleRing.ofCompletion (𝓞 F) F w) (y.1 w)) *
    ∏ v : {v // v ∈ A.Sf}, Units.map (NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F v.val) (y.2 v)

private lemma sIdele_infinite (A : SArithmeticData F) (y : A.G) (w : InfinitePlace F) :
    (sIdele A y).val.1 w = (y.1 w : w.Completion) := by
  classical
  have hval : (sIdele A y).val =
      (∏ w : InfinitePlace F, NumberField.AdeleRing.ofCompletion (𝓞 F) F w (y.1 w : w.Completion)) *
      ∏ v : {v // v ∈ A.Sf}, NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F v.val (y.2 v : v.val.adicCompletion F) := by
    simp [sIdele, Units.coe_prod]
  rw [hval]
  dsimp only [AdeleRing] at *
  have hi : (∏ i : InfinitePlace F, AdeleRing.ofCompletion (𝓞 F) F i ↑(y.1 i)).1 =
      ∏ i : InfinitePlace F, Pi.mulSingle i (y.1 i : i.Completion) := by
    erw [Prod.fst_prod]
    rfl
  have hf : (∏ i : {v // v ∈ A.Sf}, AdeleRing.ofAdicCompletion (𝓞 F) F i.val ↑(y.2 i)).1 = 1 := by
    erw [Prod.fst_prod]
    change (∏ i : {v // v ∈ A.Sf}, (1 : InfiniteAdeleRing F)) = 1
    simp
  erw [Prod.fst_mul, hi, hf, mul_one, Finset.univ_prod_mulSingle]

private lemma sIdele_finite (A : SArithmeticData F) (y : A.G) (v : HeightOneSpectrum (𝓞 F)) :
    (sIdele A y).val.2 v = if h : v ∈ A.Sf then (y.2 ⟨v, h⟩ : v.adicCompletion F) else 1 := by
  classical
  have hval : (sIdele A y).val =
      (∏ w : InfinitePlace F, NumberField.AdeleRing.ofCompletion (𝓞 F) F w (y.1 w : w.Completion)) *
      ∏ v : {v // v ∈ A.Sf}, NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F v.val (y.2 v : v.val.adicCompletion F) := by
    simp [sIdele, Units.coe_prod]
  rw [hval]
  have hi : (∏ i : InfinitePlace F, AdeleRing.ofCompletion (𝓞 F) F i ↑(y.1 i)).2 = 1 := by
    erw [Prod.snd_prod]
    change (∏ i : InfinitePlace F, (1 : FiniteAdeleRing (𝓞 F) F)) = 1
    simp
  erw [Prod.snd_mul, hi, one_mul]
  erw [Prod.snd_prod]
  change (∏ i : {v // v ∈ A.Sf}, FiniteAdeleRing.ofAdicCompletion F i.val (y.2 i : i.val.adicCompletion F)) v = _
  change (RestrictedProduct.evalMonoidHom (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (B := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) v)
    (∏ i : {v // v ∈ A.Sf}, FiniteAdeleRing.ofAdicCompletion F i.val (y.2 i : i.val.adicCompletion F)) = _
  erw [map_prod]
  by_cases hv : v ∈ A.Sf
  · rw [dif_pos hv]
    rw [Finset.prod_eq_single (⟨v, hv⟩ : {v // v ∈ A.Sf})]
    · change Pi.mulSingle v (y.2 ⟨v, hv⟩ : v.adicCompletion F) v = _
      simp
    · intro b hb hne
      change Pi.mulSingle b.val (y.2 b : b.val.adicCompletion F) v = 1
      apply Pi.mulSingle_eq_of_ne
      intro h
      exact hne (Subtype.ext h.symm)
    · simp
  · rw [dif_neg hv]
    apply Finset.prod_eq_one
    intro b hb
    change Pi.mulSingle b.val (y.2 b : b.val.adicCompletion F) v = 1
    apply Pi.mulSingle_eq_of_ne
    intro h
    exact hv (h.symm ▸ b.property)

private lemma sIdele_value (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle) (y : A.G) :
    Φ (QuotientGroup.mk (sIdele A y)) = (A.ideleSInverseProduct Φ y)⁻¹ := by
  simp [sIdele, ideleSInverseProduct, ideleInfiniteComponent, ideleFiniteComponent,
    IdeleClassGroup.ofCompletion, IdeleClassGroup.ofAdicCompletion,
    IdeleGroup.ofCompletion, IdeleGroup.ofAdicCompletion]
  rw [mul_comm]
 def infiniteProjection (w : InfinitePlace F) : AdeleRing (𝓞 F) F →* w.Completion where
  toFun x := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

 def finiteProjection (v : HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →* v.adicCompletion F where
  toFun x := x.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma infinite_div (x z : NumberField.IdeleGroup (𝓞 F) F) (w : InfinitePlace F) :
    (x / z).val.1 w = x.val.1 w / z.val.1 w := by
  change (Units.map (infiniteProjection w) (x / z) : w.Completion) = _
  rw [map_div, Units.val_div_eq_div_val]
  rfl

private lemma finite_div (x z : NumberField.IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x / z).val.2 v = x.val.2 v / z.val.2 v := by
  change (Units.map (finiteProjection v) (x / z) : v.adicCompletion F) = _
  rw [map_div, Units.val_div_eq_div_val]
  rfl

theorem outside_valuation_one_value (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hcont : Continuous Φ) (hunram : A.IdeleCharacterUnramifiedOutside Φ)
    (x : NumberField.IdeleGroup (𝓞 F) F)
    (hout : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → Valued.v (x.val.2 v) = 1) :
    Φ (QuotientGroup.mk x) = (A.ideleSInverseProduct Φ (ClassCharacterSteps.sRestriction A x))⁻¹ := by
  let y := ClassCharacterSteps.sRestriction A x
  have hkill : Φ (QuotientGroup.mk (x / sIdele A y)) = 1 := by
    apply outside_units_trivial A Φ hcont hunram
    · intro w
      rw [infinite_div]
      rw [sIdele_infinite]
      exact div_self (Units.ne_zero (y.1 w))
    · intro v hv
      rw [finite_div]
      rw [sIdele_finite, dif_pos hv]
      exact div_self (Units.ne_zero (y.2 ⟨v, hv⟩))
    · intro v hv
      rw [finite_div]
      rw [sIdele_finite, dif_neg hv, div_one, hout v hv]
  have hv := sIdele_value A Φ y
  change Φ ((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)) (x / sIdele A y)) = 1 at hkill
  rw [map_div, map_div, div_eq_one] at hkill
  exact hkill.trans hv

theorem localArithmeticLaws_units (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hcont : Continuous Φ) (hunram : A.IdeleCharacterUnramifiedOutside Φ)
    (ε : A.U) : A.ideleSInverseProduct Φ (A.diagonal ε.val) = 1 := by
  let x := NumberField.IdeleGroup.unitEmbedding (𝓞 F) F ε.val
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → Valued.v (x.val.2 v) = 1 := by
    intro v hv
    change Valued.v (algebraMap F (v.adicCompletion F) (ε.val : F)) = 1
    change Valued.v ((WithVal.toVal (v.valuation F) (ε.val : F) : WithVal (v.valuation F)) : v.adicCompletion F) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact Set.unit_valuation_eq_one (A.Sf : Set (HeightOneSpectrum (𝓞 F))) F ε hv
  have h := outside_valuation_one_value A Φ hcont hunram x hx
  have hs : ClassCharacterSteps.sRestriction A x = A.diagonal ε.val := rfl
  rw [hs] at h
  have hprincipal : QuotientGroup.mk x = (1 : A.ArithmeticIdeleClasses) := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨ε.val, rfl⟩
  rw [hprincipal, map_one] at h
  exact inv_eq_one.mp h.symm

theorem localArithmeticLaws_principal_of_valuation (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hcont : Continuous Φ) (hunram : A.IdeleCharacterUnramifiedOutside Φ)
    (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F) (a : Fˣ)
    (hx : A.RepresentsExteriorIdeal I x)
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = Valued.v (x.val.2 v)) :
    Φ (QuotientGroup.mk x) = A.ideleSInverseProduct Φ (A.diagonal a) := by
  let p := NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a
  have hout : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf →
      Valued.v ((x / p).val.2 v) = 1 := by
    intro v hv
    rw [finite_div, map_div₀]
    change Valued.v (x.val.2 v) / Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1
    rw [ha v hv]
    apply div_self
    have hn : x.val.2 v ≠ 0 := (Units.map (finiteProjection v) x).ne_zero
    exact (map_ne_zero _).mpr hn
  have h := outside_valuation_one_value A Φ hcont hunram (x / p) hout
  have hs : ClassCharacterSteps.sRestriction A (x / p) = (A.diagonal a)⁻¹ := by
    rw [map_div]
    have hsx : ClassCharacterSteps.sRestriction A x = 1 := by
      apply Prod.ext
      · funext w
        apply Units.ext
        exact hx.1 w
      · funext v
        apply Units.ext
        exact hx.2.1 v.val v.property
    rw [hsx, one_div]
    rfl
  rw [hs] at h
  have hp : QuotientGroup.mk p = (1 : A.ArithmeticIdeleClasses) := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨a, rfl⟩
  change Φ ((QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)) (x / p)) = _ at h
  rw [map_div, map_div] at h
  change Φ (QuotientGroup.mk x) / Φ (QuotientGroup.mk p) = _ at h
  rw [hp, map_one, div_one] at h
  simp only [ideleSInverseProduct, ideleInfiniteComponent, ideleFiniteComponent,
    Prod.fst_inv, Prod.snd_inv, Pi.inv_apply, MonoidHom.comp_apply,
    map_inv, inv_inv, Finset.prod_inv_distrib, mul_inv_rev] at h ⊢
  exact h.trans (mul_comm _ _)

 def generatorBoundIdeal (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) (n : ℕ) : Ideal A.R where
  carrier := {a | v.valuation F (a : F) ≤ WithZero.exp (-(n : ℤ))}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change v.valuation F ((a : F) + (b : F)) ≤ _
    exact (ValuationClass.map_add_le_max _ _ _).trans (max_le ha hb)
  smul_mem' := by
    intro a b hb
    change v.valuation F ((a : F) * (b : F)) ≤ _
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (a.property v hv) zero_le).trans (by simpa using hb)

private lemma generator_valuation (A : SArithmeticData F)
    (I : A.Exterior) (r : A.R) (hr : A.Generates I r) (a : Fˣ) (ha : (a : F) = (r : F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) =
      WithZero.exp (-(idealPrimeExponent v.asIdeal I.val : ℤ)) := by
  classical
  let n := idealPrimeExponent v.asIdeal I.val
  have hdvd (k : ℕ) : v.asIdeal ^ k ∣ I.val ↔ k ≤ n := by
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible I.property.1]
    simp [n, idealPrimeExponent]
  have hIn : I.val ≤ v.asIdeal ^ n := Ideal.dvd_iff_le.mp ((hdvd n).mpr le_rfl)
  have hnot : ¬ I.val ≤ v.asIdeal ^ (n + 1) := by
    rw [← Ideal.dvd_iff_le, hdvd]; omega
  have hmap : A.extendIdeal I ≤ generatorBoundIdeal A v hv n := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change v.valuation F (b : F) ≤ WithZero.exp (-(n : ℤ))
    rw [v.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem b n).mpr (hIn hb)
  have hrv : v.valuation F (r : F) ≤ WithZero.exp (-(n : ℤ)) := by
    apply hmap
    rw [← hr.2]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨b, hb, hbn⟩ : ∃ b : 𝓞 F, b ∈ I.val ∧ b ∉ v.asIdeal ^ (n + 1) := by
    contrapose! hnot
    exact hnot
  have hbm : algebraMap (𝓞 F) A.R b ∈ Ideal.span ({r} : Set A.R) := by
    rw [hr.2]
    exact Ideal.mem_map_of_mem _ hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hbm
  have hbv : v.valuation F (b : F) ≤ v.valuation F (r : F) := by
    have hh := congrArg (fun t : A.R => (t : F)) hy
    change (b : F) = (r : F) * (y : F) at hh
    rw [hh, map_mul]
    exact (mul_le_mul_of_nonneg_left (y.property v hv) zero_le).trans (by simp)
  have hrv' : ¬ v.valuation F (r : F) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    intro h
    apply hbn
    apply (v.intValuation_le_pow_iff_mem b (n + 1)).mp
    rw [← v.valuation_of_algebraMap (K := F)]
    exact hbv.trans h
  have hnz : v.valuation F (r : F) ≠ 0 := by
    rw [← ha]
    exact (Valuation.ne_zero_iff _).mpr a.ne_zero
  rw [← WithZero.exp_log hnz, WithZero.exp_le_exp] at hrv hrv'
  have he : WithZero.log (v.valuation F (r : F)) = -(n : ℤ) := by
    push_cast at hrv'
    omega
  change Valued.v ((WithVal.toVal (v.valuation F) (a : F) : WithVal (v.valuation F)) : v.adicCompletion F) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ha, ← WithZero.exp_log hnz, he]

theorem localArithmeticLaws (A : SArithmeticData F)
    (Φ : A.ArithmeticIdeleClasses →* Circle)
    (hcont : Continuous Φ) (hunram : A.IdeleCharacterUnramifiedOutside Φ) :
    (∀ (I : A.Exterior) (x : NumberField.IdeleGroup (𝓞 F) F)
      (a : Fˣ) (r : A.R), A.RepresentsExteriorIdeal I x →
        A.Generates I r → (a : F) = (r : F) →
        Φ (QuotientGroup.mk x) = A.ideleSInverseProduct Φ (A.diagonal a)) ∧
    (∀ ε : A.U, A.ideleSInverseProduct Φ (A.diagonal ε.val) = 1) ∧
    (∀ v : {v // v ∈ A.Sf}, ∀ z : (v.val.adicCompletion F)ˣ,
      ∃ U : Set (v.val.adicCompletion F)ˣ, IsOpen U ∧ z ∈ U ∧
        ∀ t ∈ U, A.ideleFiniteComponent Φ v.val t =
          A.ideleFiniteComponent Φ v.val z) := by
  refine ⟨?_, localArithmeticLaws_units A Φ hcont hunram, ?_⟩
  · intro I x a r hx hr har
    apply localArithmeticLaws_principal_of_valuation A Φ hcont hunram I x a hx
    intro v hv
    exact (generator_valuation A I r hr a har v hv).trans (hx.2.2 v hv).symm
  · intro v z
    exact (IsLocallyConstant.iff_exists_open _).mp
      (localArithmeticLaws_finite A Φ hcont v.val) z

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
