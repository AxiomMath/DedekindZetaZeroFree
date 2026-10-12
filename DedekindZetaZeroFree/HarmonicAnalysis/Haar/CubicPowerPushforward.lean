module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.MultiplicativeCubeIndex
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnitCubeIndex
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ResidueFieldScaling

@[expose] public section

section
namespace DedekindZetaZeroFree.KPCubicHaarTransport
noncomputable section
open MeasureTheory ValuativeRel KPCubicUnitIndices
open scoped Classical ENNReal Topology WithZeroTopology
private lemma units_borel (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := by
  constructor
  unfold Units.instMeasurableSpace
  rw [‹BorelSpace K›.measurable_eq, ← borel_comap]
  rw [← (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced]
variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
private lemma abs_pos {x : K} (hx : x ≠ 0) : 0 < abs K x := by
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast (two_le_residueCard K).trans_lt' (by decide)
  simp only [abs, if_neg hx]
  exact zpow_pos hq _
private lemma abs_mul (x y : K) : abs K (x * y) = abs K x * abs K y := by
  by_cases hx : x = 0
  · subst x; simp [abs]
  by_cases hy : y = 0
  · subst y; simp [abs]
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hex : e (valuation K x) ≠ 0 := by simpa [e] using hx
  have hey : e (valuation K y) ≠ 0 := by simpa [e] using hy
  simp only [abs, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), _root_.map_mul]
  rw [WithZero.log_mul hex hey, zpow_add₀]
  exact_mod_cast (show residueCard K ≠ 0 from by have := two_le_residueCard K; omega)

private lemma density_measurable : Measurable (fun x : K => ENNReal.ofReal ((abs K x)⁻¹)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  apply Measurable.ennreal_ofReal
  apply Measurable.inv
  apply ContinuousOn.measurable_of_countable_compl (s := ({0} : Set K)ᶜ)
  · intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : x ≠ 0 := by simpa using hx
    have hv : valuation K x ≠ 0 := by simpa using hx0
    have he : ∀ᶠ y in 𝓝 x, valuation K y = valuation K x :=
      (WithZeroTopology.tendsto_of_ne_zero hv).mp
        (IsValuativeTopology.continuous_valuation.continuousAt : ContinuousAt (valuation K) x)
    apply (continuousAt_const (y := abs K x)).congr
    filter_upwards [he] with y hy
    have hy0 : y ≠ 0 := by intro h; simp [h] at hy; exact hv hy.symm
    simp [abs, hx0, hy0, hy]
  · simp
private lemma unit_abs (u : Kˣ) (hu : (u : K) ∈ Integers K)
    (hi : ((u⁻¹ : Kˣ) : K) ∈ Integers K) : abs K (u : K) = 1 := by
  have hv : valuation K (u : K) = 1 := by
    apply le_antisymm hu
    have ht : valuation K ((u⁻¹ : Kˣ) : K) = (valuation K (u : K))⁻¹ := by simp
    change valuation K ((u⁻¹ : Kˣ) : K) ≤ 1 at hi
    rw [ht] at hi
    exact (inv_le_one₀ (bot_lt_iff_ne_bot.mpr ((Valuation.ne_zero_iff _).mpr u.ne_zero))).mp hi
  simp [abs, u.ne_zero, hv]
private lemma haar_left (dx : Measure K) [dx.IsAddHaarMeasure]
    (hscale : ∀ (c : K) (hc : c ≠ 0), Measure.map (fun x : K => c * x) dx =
      (ENNReal.ofReal (abs K c))⁻¹ • dx) : (haar K dx).IsMulLeftInvariant := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := units_borel K
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let D := fun x : K => ENNReal.ofReal ((abs K x)⁻¹)
  have hD : Measurable D := density_measurable K
  constructor
  intro g
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs]
  change (dx.withDensity D).comap Units.val ((fun x => g * x) ⁻¹' s) =
    (dx.withDensity D).comap Units.val s
  rw [ev.comap_apply, ev.comap_apply]
  have hpre : Units.val '' ((fun x => g * x) ⁻¹' s) =
      (fun x : K => (g : K) * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨g * u, hu, by simp⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨g⁻¹ * u, ?_, ?_⟩
      · simpa using hu
      · change ((g⁻¹ * u : Kˣ) : K) = x
        simp only [Units.val_mul]
        rw [he]; simp
  rw [hpre, withDensity_apply _ (by exact (ev.measurableSet_image.mpr hs).preimage (by fun_prop)),
    withDensity_apply _ (ev.measurableSet_image.mpr hs)]
  have hscale : Measure.map (fun x : K => (g : K) * x) dx =
      (ENNReal.ofReal (abs K (g : K)))⁻¹ • dx :=
    hscale (g : K) g.ne_zero
  have hmul (x : K) : D ((g : K) * x) = (ENNReal.ofReal (abs K (g : K)))⁻¹ * D x := by
    dsimp [D]
    have ha : abs K ((g : K) * x) = abs K (g : K) * abs K x := abs_mul K _ _
    have hp : 0 < abs K (g : K) := abs_pos K g.ne_zero
    rw [ha, mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr hp.le),
      ENNReal.ofReal_inv_of_pos hp]
  have hm := setLIntegral_map (μ := dx) (g := fun x : K => (g : K) * x)
    (s := Units.val '' s) (ev.measurableSet_image.mpr hs) hD (by fun_prop)
  rw [hscale, Measure.restrict_smul, lintegral_smul_measure] at hm
  simp only [ENNReal.smul_def, smul_eq_mul] at hm
  simp_rw [hmul] at hm
  rw [lintegral_const_mul _ hD] at hm
  have hp : 0 < abs K (g : K) := abs_pos K g.ne_zero
  exact (ENNReal.mul_right_inj (by simp) (by simp [hp])).mp hm.symm
private lemma unit_mass (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (Integers K : Set K) = ENNReal.ofReal m)
    (hres : (residueCard K : ℝ≥0∞) * dx ((Integers K).subtype ''
      (IsLocalRing.maximalIdeal (Integers K) : Set (Integers K))) = dx (Integers K : Set K)) :
    haar K dx {x : Kˣ | (x : K) ∈ Integers K ∧ ((x⁻¹ : Kˣ) : K) ∈ Integers K} =
      ENNReal.ofReal (m * (1 - (residueCard K : ℝ)⁻¹)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := units_borel K
  let ev := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let R := Integers K
  let U : Set Kˣ := {x | (x : K) ∈ R ∧ ((x⁻¹ : Kˣ) : K) ∈ R}
  let P : Set K := R.subtype '' (IsLocalRing.maximalIdeal R : Set R)
  have hU : IsOpen U := (Valued.isOpen_integer K).preimage Units.continuous_val |>.inter
    ((Valued.isOpen_integer K).preimage Units.continuous_coe_inv)
  have hP : MeasurableSet P := by
    have hi : MeasurableSet (IsLocalRing.maximalIdeal R : Set R) :=
      (IsNoetherianRing.isClosed_ideal (IsLocalRing.maximalIdeal R)).measurableSet
    exact (MeasurableEmbedding.subtype_coe (Valued.isClosed_integer K).measurableSet).measurableSet_image.mpr hi
  have hset : Units.val '' U = (R : Set K) \ P := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨hu.1, ?_⟩
      rintro ⟨y, hy, he⟩
      have hval : valuation K (y : K) = 1 := by
        change (y : K) = (u : K) at he
        rw [he]
        have ha := unit_abs K u hu.1 hu.2
        have ht : valuation K (u : K) = 1 := by
          apply le_antisymm hu.1
          have hi := hu.2
          change valuation K ((u⁻¹ : Kˣ) : K) ≤ 1 at hi
          rw [Units.val_inv_eq_inv_val, map_inv₀] at hi
          exact (inv_le_one₀ (bot_lt_iff_ne_bot.mpr ((Valuation.ne_zero_iff _).mpr u.ne_zero))).mp hi
        exact ht
      have hi : IsUnit y := (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr hval
      exact ((IsLocalRing.mem_maximalIdeal y).mp hy) hi
    · rintro ⟨hx, hxp⟩
      have hu : IsUnit (⟨x, hx⟩ : R) := by
        by_contra hn
        apply hxp
        exact ⟨⟨x, hx⟩, (IsLocalRing.mem_maximalIdeal _).mpr hn, rfl⟩
      obtain ⟨u, hu⟩ := hu
      refine ⟨Units.map R.subtype.toMonoidHom u, ⟨?_, ?_⟩, ?_⟩
      · exact u.val.property
      · exact u.inv.property
      · exact congrArg Subtype.val hu
  change (dx.withDensity (fun x => ENNReal.ofReal ((abs K x)⁻¹))).comap Units.val U = _
  rw [ev.comap_apply, withDensity_apply _ (ev.measurableSet_image.mpr hU.measurableSet)]
  have hd : Set.EqOn (fun x : K => ENNReal.ofReal ((abs K x)⁻¹)) (fun _ => 1) (Units.val '' U) := by
    rintro x ⟨u, hu, rfl⟩
    simp [unit_abs K u hu.1 hu.2]
  rw [setLIntegral_congr_fun (ev.measurableSet_image.mpr hU.measurableSet) hd]
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
  have hsub : P ⊆ (R : Set K) := by rintro x ⟨y, hy, rfl⟩; exact y.property
  rw [hset, measure_sdiff hsub hP.nullMeasurableSet (measure_ne_top_of_subset hsub (by rw [hvol]; simp))]
  change (residueCard K : ℝ≥0∞) * dx P = dx (R : Set K) at hres
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast (two_le_residueCard K).trans_lt' (by decide)
  have hq1 : (1 : ℝ) ≤ residueCard K := by exact_mod_cast (two_le_residueCard K).trans' (by decide)
  have hp : dx P = ENNReal.ofReal (m * (residueCard K : ℝ)⁻¹) := by
    have hc : (residueCard K : ℝ≥0∞) = ENNReal.ofReal (residueCard K : ℝ) := by simp
    apply (ENNReal.mul_right_inj (a := (residueCard K : ℝ≥0∞)) (by exact_mod_cast hq.ne') (by simp)).mp
    rw [hres, hvol, ENNReal.ofReal_mul hm.le,
      ENNReal.ofReal_inv_of_pos hq, ← hc, mul_comm (ENNReal.ofReal m),
      ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hq.ne') (by simp), one_mul]
  rw [hp, hvol, ← ENNReal.ofReal_sub]
  · congr 1; ring
  · positivity
private theorem haar_of_scaling_and_residue
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (Integers K : Set K) = ENNReal.ofReal m)
    (hscale : ∀ (c : K) (hc : c ≠ 0), Measure.map (fun x : K => c * x) dx =
      (ENNReal.ofReal (abs K c))⁻¹ • dx)
    (hres : (residueCard K : ℝ≥0∞) * dx ((Integers K).subtype ''
      (IsLocalRing.maximalIdeal (Integers K) : Set (Integers K))) = dx (Integers K : Set K)) :
    (haar K dx).IsHaarMeasure ∧
    haar K dx {x : Kˣ | (x : K) ∈ Integers K ∧ ((x⁻¹ : Kˣ) : K) ∈ Integers K} =
      ENNReal.ofReal (m * (1 - (residueCard K : ℝ)⁻¹)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := units_borel K
  letI := haar_left K dx hscale
  have hmass := unit_mass K dx m hm hvol hres
  refine ⟨?_, hmass⟩
  let U : Set Kˣ := {x | (x : K) ∈ Integers K ∧ ((x⁻¹ : Kˣ) : K) ∈ Integers K}
  have hU : IsOpen U := (Valued.isOpen_integer K).preimage Units.continuous_val |>.inter
    ((Valued.isOpen_integer K).preimage Units.continuous_coe_inv)
  have hcomp : IsCompact U := by
    exact Submonoid.units_isCompact (S := (Integers K).toSubmonoid)
      (IsNonarchimedeanLocalField.isCompact_closedBall K 1)
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior (haar K dx) U hcomp
    (by rw [hU.interior_eq]; exact ⟨1, by simp [U]⟩)
  · rw [hmass]
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    have hq : (1 : ℝ) < residueCard K := by exact_mod_cast two_le_residueCard K
    exact mul_pos hm (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr hq))
  · rw [hmass]; simp

theorem haar_structure_and_unit_mass
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (Integers K : Set K) = ENNReal.ofReal m) :
    (haar K dx).IsHaarMeasure ∧
    haar K dx {x : Kˣ | (x : K) ∈ Integers K ∧ ((x⁻¹ : Kˣ) : K) ∈ Integers K} =
      ENNReal.ofReal (m * (1 - (residueCard K : ℝ)⁻¹)) := by
  apply haar_of_scaling_and_residue K dx m hm hvol
  · intro c hc
    exact IntrinsicHaarScaling.map_mul K dx c hc
  · exact IntrinsicHaarScaling.residue_index_measure K dx

end
end DedekindZetaZeroFree.KPCubicHaarTransport

end

section
namespace DedekindZetaZeroFree.KPCubicHaarTransport
noncomputable section
open MeasureTheory KPCubicUnitIndices ValuativeRel Filter Topology
open scoped ENNReal

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

private theorem secondCountable : SecondCountableTopology K := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
 letI := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
 haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
 infer_instance
private theorem cube_proper : IsProperMap (fun x : Kˣ => x^3) := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
 letI := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
 haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
 have hp : IsProperMap (fun x : K => x^3) := by
   convert (Polynomial.X ^ 3 : Polynomial K).isProperMap_eval (by simp) using 1
   funext x
   simp
 have hprod : IsProperMap (fun p : K × Kᵐᵒᵖ => (p.1^3, p.2^3)) := hp.prodMap (by
   simpa only [MulOpposite.op_pow] using
     (MulOpposite.opHomeomorph.isProperMap.comp hp).comp MulOpposite.opHomeomorph.symm.isProperMap)
 have hcomm : (fun p : K × Kᵐᵒᵖ => (p.1^3, p.2^3)) ∘ Units.embedProduct K =
     Units.embedProduct K ∘ (fun x : Kˣ => x^3) := by funext x; ext <;> simp [Units.embedProduct]
 apply isProperMap_of_comp_of_inj (by fun_prop) Units.continuous_embedProduct
   (by rw [← hcomm]; exact hprod.comp Units.isClosedEmbedding_embedProduct.isProperMap)
 exact Units.embedProduct_injective K

 def unitGroup : Subgroup Kˣ := (valuation K).integer.toSubmonoid.units
private theorem unitGroup_open : IsOpen (unitGroup K : Set Kˣ) := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 exact Submonoid.isOpen_units (Valued.isOpen_integer K)
private theorem unitGroup_compact : IsCompact (unitGroup K : Set Kˣ) := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 exact Submonoid.units_isCompact (IsNonarchimedeanLocalField.isCompact_closedBall K 1)
private theorem cube_preimage_units : (fun x : Kˣ => x^3) ⁻¹' (unitGroup K : Set Kˣ) = unitGroup K := by
 ext x
 change (x^3 : Kˣ) ∈ (unitGroup K : Set Kˣ) ↔ x ∈ (unitGroup K : Set Kˣ)
 change (valuation K ((x^3 : Kˣ) : K) ≤ 1 ∧ valuation K (((x^3)⁻¹ : Kˣ) : K) ≤ 1) ↔
   (valuation K (x : K) ≤ 1 ∧ valuation K ((x⁻¹ : Kˣ) : K) ≤ 1)
 rw [← inv_pow]
 simp only [Units.val_pow_eq_pow_val, map_pow]
 constructor
 · rintro ⟨h, h'⟩
   exact ⟨(pow_le_one_iff_of_nonneg zero_le (by decide)).mp h,
     (pow_le_one_iff_of_nonneg zero_le (by decide)).mp h'⟩
 · rintro ⟨h, h'⟩
   exact ⟨pow_le_one₀ zero_le h, pow_le_one₀ zero_le h'⟩
private theorem cube_unit_index :
 (powMonoidHom (α := Kˣ) 3).range.relIndex (unitGroup K) = (KPCubicUnitIndices.cubeUnits K).index := by
 let O := KPCubicUnitIndices.Integers K
 let f : Oˣ →* Kˣ := Units.map O.subtype.toMonoidHom
 have hrange : f.range = unitGroup K := by
   ext x
   constructor
   · rintro ⟨u, rfl⟩
     exact ⟨u.val.property, u.inv.property⟩
   · rintro ⟨hx, hy⟩
     refine ⟨⟨⟨x.val, hx⟩, ⟨(x⁻¹).val, hy⟩, ?_, ?_⟩, ?_⟩
     · ext; exact x.mul_inv
     · ext; exact x.inv_mul
     · exact Units.ext rfl
 have hcomap : (powMonoidHom (α := Kˣ) 3).range.comap f = KPCubicUnitIndices.cubeUnits K := by
   ext u
   change (∃ t : Kˣ, t^3 = f u) ↔ ∃ t : Oˣ, t^3 = u
   constructor
   · rintro ⟨t, ht⟩
     have hvu : valuation K ((f u : Kˣ) : K) = 1 :=
       (Valuation.integer.integers (valuation K)).one_of_isUnit u.isUnit
     have hvt : valuation K (t : K) = 1 := by
       have hp : valuation K (t : K)^3 = 1 := by
         rw [← map_pow, ← Units.val_pow_eq_pow_val, ht, hvu]
       exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
     let tO : O := ⟨(t : K), hvt.le⟩
     have hunit : IsUnit tO := (Valuation.integer.integers (valuation K)).isUnit_of_one' hvt
     have hft : f hunit.unit = t := by apply Units.ext; change ((hunit.unit : O) : K) = _; rw [hunit.unit_spec]
     have hf : Function.Injective f := Units.map_injective Subtype.val_injective
     refine ⟨hunit.unit, hf ?_⟩
     rw [map_pow, hft, ht]
   · rintro ⟨t, rfl⟩
     exact ⟨f t, (map_pow f t 3).symm⟩
 rw [← hrange, ← Subgroup.index_comap, hcomap]

private theorem haar_isHaar (dx : Measure K) [dx.IsAddHaarMeasure] : (haar K dx).IsHaarMeasure := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 have hc : IsCompact (KPCubicUnitIndices.Integers K : Set K) :=
   IsNonarchimedeanLocalField.isCompact_closedBall K 1
 have ho : IsOpen (KPCubicUnitIndices.Integers K : Set K) := Valued.isOpen_integer K
 have hp : 0 < dx (KPCubicUnitIndices.Integers K : Set K) :=
   ho.measure_pos (μ := dx) ⟨0, by simp⟩
 exact (haar_structure_and_unit_mass K dx _
   (ENNReal.toReal_pos hp.ne' hc.measure_lt_top.ne) (ENNReal.ofReal_toReal hc.measure_lt_top.ne).symm).1

theorem cube_pushforward
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (ζ : Integers K) (hζ : IsPrimitiveRoot ζ 3)
    (dx : Measure K) [dx.IsAddHaarMeasure] :
    Measure.map (fun y : Kˣ => y ^ 3) (haar K dx) =
      ENNReal.ofReal (((powMonoidHom (α := Kˣ) 3).range.index : ℝ) / 3) •
        (haar K dx).restrict ((powMonoidHom (α := Kˣ) 3).range : Set Kˣ) := by
 letI := IsTopologicalAddGroup.rightUniformSpace K
 haveI := isUniformAddGroup_of_addCommGroup (G := K)
 letI := secondCountable K
 haveI : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
 haveI : BorelSpace Kˣ := by
   constructor
   change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
   calc
     _ = MeasurableSpace.comap Units.val (borel K) := congrArg (MeasurableSpace.comap Units.val) (@BorelSpace.measurable_eq K _ _ _)
     _ = borel Kˣ := by
       have hh := @borel_comap Kˣ K Units.val ‹TopologicalSpace K›
       have ht := (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced
       exact ht ▸ hh.symm
 let μ := haar K dx
 letI : μ.IsHaarMeasure := haar_isHaar K dx
 let f := powMonoidHom (α := Kˣ) 3
 let H := f.range
 haveI : H.FiniteIndex := by
   haveI : Finite (Kˣ ⧸ H) := ClassFieldTheory.powerClassGroup_finite K ⟨3, by decide⟩ (by norm_num)
   exact Subgroup.finiteIndex_of_finite_quotient
 have hf : Continuous f := continuous_id.pow 3
 have hp : IsProperMap f := cube_proper K
 have hHc : IsClosed (H : Set Kˣ) := hp.isClosed_range
 have hHo : IsOpen (H : Set Kˣ) := H.isOpen_of_isClosed_of_finiteIndex hHc
 haveI : LocallyCompactSpace H := hHo.locallyCompactSpace
 haveI : SecondCountableTopology H := (hHo.isOpenEmbedding_subtypeVal).isEmbedding.secondCountableTopology
 let ν := μ.comap H.subtype
 have hi : IsOpenEmbedding H.subtype := hHo.isOpenEmbedding_subtypeVal
 haveI : ν.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ hi
 let g := f.rangeRestrict
 have hg : Continuous g := hf.subtype_mk _
 have hgp : IsProperMap g := isProperMap_of_comp_of_inj hg continuous_subtype_val hp Subtype.val_injective
 let ρ := μ.map g
 haveI : ρ.IsHaarMeasure := Measure.isHaarMeasure_map μ g hg f.rangeRestrict_surjective
   (isProperMap_iff_tendsto_cocompact.mp hgp).2
 let c := Measure.haarScalarFactor ρ ν
 have heq : ρ = c • ν := Measure.isMulLeftInvariant_eq_smul ρ ν
 let U := unitGroup K
 have hUo : IsOpen (U : Set Kˣ) := unitGroup_open K
 have hUc : IsCompact (U : Set Kˣ) := unitGroup_compact K
 let W : Set H := H.subtype ⁻¹' (U : Set Kˣ)
 have hρW : ρ W = μ U := by
   change μ.map g W = μ U
   rw [Measure.map_apply hg.measurable (show MeasurableSet W from (hUo.preimage continuous_subtype_val).measurableSet)]
   change μ ((fun y : Kˣ => y^3) ⁻¹' U) = μ U
   rw [cube_preimage_units K]
 have hνW : ν W = μ ((U : Set Kˣ) ∩ H) := by
   rw [hi.measurableEmbedding.comap_apply]
   congr 1
   ext x; simp [W, Subgroup.coe_subtype]
 let V := H.comap U.subtype
 let τ := μ.comap U.subtype
 have hu : IsOpenEmbedding U.subtype := hUo.isOpenEmbedding_subtypeVal
 haveI : τ.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := inferInstance) μ hu
 haveI : V.FiniteIndex := inferInstance
 have hVm : MeasurableSet (V : Set U) := hHc.measurableSet.preimage hu.continuous.measurable
 have hind : (V.index : ENNReal) * μ ((U : Set Kˣ) ∩ H) = μ U := by
   have hh := MeasureTheory.Subgroup.index_mul_measure V hVm τ
   rw [hu.measurableEmbedding.comap_apply, hu.measurableEmbedding.comap_apply] at hh
   have hset : U.subtype '' (V : Set U) = (U : Set Kˣ) ∩ H := by
     ext x
     simp only [Set.mem_image, Set.mem_inter_iff, SetLike.mem_coe, V, Subgroup.mem_comap]
     constructor
     · rintro ⟨y, hy, rfl⟩; exact ⟨y.property, hy⟩
     · rintro ⟨hx, hy⟩; exact ⟨⟨x, hx⟩, hy, rfl⟩
   have huniv : U.subtype '' (Set.univ : Set U) = (U : Set Kˣ) := by ext x; simp
   simpa only [hset, huniv] using hh
 have hind' : (V.index : ENNReal) * ν W = μ U := by rw [hνW]; exact hind
 have hmass : c • ν W = μ U := by rw [← Measure.smul_apply, ← heq]; exact hρW
 have hWpos : ν W ≠ 0 := by
   apply ne_of_gt
   apply (hUo.preimage continuous_subtype_val).measure_pos (μ := ν)
   exact ⟨1, U.one_mem⟩
 have hWfinite : ν W ≠ ∞ := by
   rw [hνW]
   exact (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUc.measure_lt_top).ne
 have hc : (c : ENNReal) = V.index := by
   apply (ENNReal.mul_right_inj hWpos hWfinite).mp
   simpa only [mul_comm, NNReal.smul_def, ENNReal.smul_def, smul_eq_mul] using hmass.trans hind'.symm
 have hidx : V.index = (KPCubicUnitIndices.cubeUnits K).index := by
   rw [Subgroup.index_comap]
   simpa [V, U, H, f] using cube_unit_index K
 have hscalar : (c : ENNReal) = ENNReal.ofReal ((H.index : ℝ)/3) := by
   rw [hc, hidx]
   have hh := field_cube_index K
   change (KPCubicUnitIndices.cubeUnits K).index = ENNReal.ofReal (((f.range.index : ℕ) : ℝ) / 3)
   rw [hh]
   simp
 have hmap := congrArg (Measure.map H.subtype) heq
 rw [Measure.map_map hi.continuous.measurable hg.measurable,
   Measure.map_smul _ hi.continuous.measurable.aemeasurable,
   hi.measurableEmbedding.map_comap] at hmap
 have he : c • μ.restrict (H : Set Kˣ) = (c : ENNReal) • μ.restrict (H : Set Kˣ) := by ext s hs; simp
 have hr : Set.range H.subtype = (H : Set Kˣ) := by ext x; simp
 rw [hr, he, hscalar] at hmap
 exact hmap

end
end DedekindZetaZeroFree.KPCubicHaarTransport

end

section

namespace DedekindZetaZeroFree
namespace KPCubicHaar

noncomputable section
open MeasureTheory ValuativeRel KPCubicUnitIndices

def abs (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) : ℝ := by
  classical
  exact if x = 0 then 0 else
    (KPCubicUnitIndices.residueCard K : ℝ) ^
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x))

def ball (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (y : K) (r : ℝ) : Set K :=
  {x | abs K (x - y) < r}

def multiplicativeHaar (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) : Measure Kˣ :=
  Measure.comap (fun x : Kˣ => (x : K))
    (dx.withDensity (fun x => ENNReal.ofReal ((abs K x)⁻¹)))

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]

@[simp] theorem abs_zero : abs K 0 = 0 := by simp [abs]
@[simp] theorem abs_one : abs K 1 = 1 := by simp [abs]
theorem abs_pos {x : K} (hx : x ≠ 0) : 0 < abs K x := by
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast (two_le_residueCard K).trans_lt' (by decide)
  simp only [abs, if_neg hx]
  exact zpow_pos hq _

@[simp] theorem abs_mul (x y : K) : abs K (x*y) = abs K x * abs K y := by
  by_cases hx : x = 0
  · subst x; simp
  by_cases hy : y = 0
  · subst y; simp
  have hvx : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hvy : valuation K y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hex : e (valuation K x) ≠ 0 := by simpa [e] using hvx
  have hey : e (valuation K y) ≠ 0 := by simpa [e] using hvy
  simp only [abs, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), map_mul]
  rw [WithZero.log_mul hex hey, zpow_add₀]
  exact_mod_cast (show residueCard K ≠ 0 from by have := two_le_residueCard K; omega)
@[simp] theorem abs_inv (x : K) : abs K x⁻¹ = (abs K x)⁻¹ := by
  by_cases hx : x = 0
  · subst x; simp
  simp only [abs, if_neg hx, if_neg (inv_ne_zero hx), map_inv₀, WithZero.log_inv, zpow_neg]
@[simp] theorem abs_pow (x : K) (n : ℕ) : abs K (x ^ n) = abs K x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, abs_mul, ih, pow_succ]
theorem abs_lt_iff {x y : K} (hy : y ≠ 0) :
    abs K x < abs K y ↔ valuation K x < valuation K y := by
  by_cases hx : x = 0
  · subst x
    simp only [abs_zero, map_zero]
    exact iff_of_true (abs_pos K hy) ((Valuation.ne_zero_iff _).mpr hy).bot_lt
  have hvx : valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hvy : valuation K y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hex : e (valuation K x) ≠ 0 := by simpa [e] using hvx
  have hey : e (valuation K y) ≠ 0 := by simpa [e] using hvy
  have hq : (1 : ℝ) < residueCard K := by exact_mod_cast (two_le_residueCard K)
  simp only [abs, if_neg hx, if_neg hy, zpow_lt_zpow_iff_right₀ hq]
  change WithZero.log (e (valuation K x)) < WithZero.log (e (valuation K y)) ↔ _
  rw [← e.toOrderIso.lt_iff_lt]
  change WithZero.log (e (valuation K x)) < WithZero.log (e (valuation K y)) ↔
    e (valuation K x) < e (valuation K y)
  conv_rhs => rw [← WithZero.exp_log hex, ← WithZero.exp_log hey]
  exact WithZero.exp_lt_exp.symm

theorem ball_nonzero_constant_abs (y : K) (hy : y ≠ 0) :
    ∀ x ∈ ball K y (abs K y), x ≠ 0 ∧ abs K x = abs K y := by
  intro x hx
  have hlt : valuation K (x-y) < valuation K y := (abs_lt_iff K hy).mp hx
  have hval : valuation K x = valuation K y := by
    simpa only [sub_add_cancel] using (valuation K).map_add_eq_of_lt_right hlt
  have hne : x ≠ 0 := by
    intro hzero
    have : valuation K y = 0 := by simpa [hzero] using hval.symm
    exact ((Valuation.ne_zero_iff _).mpr hy) this
  refine ⟨hne, ?_⟩
  simp only [abs, if_neg hne, if_neg hy, hval]

theorem ball_abs_isOpen (y : K) (hy : y ≠ 0) : IsOpen (ball K y (abs K y)) := by
  have hset : ball K y (abs K y) =
      (fun x : K => x-y) ⁻¹' {x | (valuation K).restrict x < (valuation K).restrict y} := by
    ext x
    change abs K (x-y) < abs K y ↔ _
    rw [abs_lt_iff K hy]
    exact (valuation K).restrict_lt_iff.symm
  rw [hset]
  exact ((valuation K).isOpen_ball _).preimage (continuous_id.sub continuous_const)
theorem abs_units_locallyConstant : IsLocallyConstant (fun x : Kˣ => abs K (x : K)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Units.val ⁻¹' ball K (x : K) (abs K (x : K)),
    (ball_abs_isOpen K (x : K) x.ne_zero).preimage Units.continuous_val, ?_, ?_⟩
  · change abs K ((x : K) - (x : K)) < abs K (x : K)
    simpa using abs_pos K x.ne_zero
  · intro y hy
    exact (ball_nonzero_constant_abs K (x : K) x.ne_zero (y : K) hy).2

theorem fieldCubes_finiteIndex :
    (powMonoidHom (α := Kˣ) 3).range.FiniteIndex := by
  haveI : Finite (Kˣ ⧸ (powMonoidHom 3).range) :=
    ClassFieldTheory.powerClassGroup_finite K ⟨3, by decide⟩ (by norm_num)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem cubeUnits_eq_comap : cubeUnits K =
    (powMonoidHom (α := Kˣ) 3).range.comap (Units.map (Integers K).subtype.toMonoidHom) := by
  let f : (Integers K)ˣ →* Kˣ := Units.map (Integers K).subtype.toMonoidHom
  have hf : Function.Injective f := Units.map_injective Subtype.val_injective
  ext u
  change (∃ t : (Integers K)ˣ, t ^ 3 = u) ↔ ∃ t : Kˣ, t ^ 3 = f u
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨f t, (map_pow f t 3).symm⟩
  · rintro ⟨t, ht⟩
    have hvu : valuation K ((f u : Kˣ) : K) = 1 :=
      (Valuation.integer.integers (valuation K)).one_of_isUnit u.isUnit
    have hvt : valuation K (t : K) = 1 := by
      have hp : valuation K (t : K) ^ 3 = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ht, hvu]
      exact (pow_eq_one_iff_of_nonneg zero_le (by decide)).mp hp
    let tO : Integers K := ⟨(t : K), hvt.le⟩
    have hunit : IsUnit tO :=
      (Valuation.integer.integers (valuation K)).isUnit_of_one' hvt
    have hft : f hunit.unit = t := by
      apply Units.ext
      change (↑(hunit.unit : Integers K) : K) = (t : K)
      rw [hunit.unit_spec]
    refine ⟨hunit.unit, hf ?_⟩
    rw [map_pow, hft, ht]

theorem cubeUnits_finiteIndex : (cubeUnits K).FiniteIndex := by
  haveI := fieldCubes_finiteIndex K
  rw [cubeUnits_eq_comap]
  infer_instance

theorem cubeKernel_eq_rootsOfUnity :
    (powMonoidHom (α := Kˣ) 3).ker = rootsOfUnity 3 K := by
  ext x
  simp [MonoidHom.mem_ker, rootsOfUnity, powMonoidHom_apply]

theorem card_cubeRoots (ζ : Integers K) (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  have hzK : IsPrimitiveRoot (ζ : K) 3 :=
    hζ.map_of_injective (f := (valuation K).integer.subtype) Subtype.val_injective
  exact hzK.card_rootsOfUnity

open scoped WithZero in

theorem abs_uniformizer (π : K) (hπ : valuation K π = ValuativeRel.uniformizer K) :
    abs K π = (residueCard K : ℝ)⁻¹ := by
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact (ValuativeRel.uniformizer_pos (R := K)).ne' hπ.symm
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hu_ne : ValuativeRel.uniformizer K ≠ 0 := (ValuativeRel.uniformizer_pos (R := K)).ne'
  have hx_ne : e (ValuativeRel.uniformizer K) ≠ 0 := by simpa [e] using hu_ne
  have hx_lt : e (ValuativeRel.uniformizer K) < 1 := by
    rw [← map_one e]
    exact e.toOrderIso.lt_iff_lt.mpr (ValuativeRel.uniformizer_lt_one (R := K))
  have hlog : WithZero.log (e (ValuativeRel.uniformizer K)) = -1 := by
    refine le_antisymm ?_ ?_
    · have h : WithZero.log (e (ValuativeRel.uniformizer K)) < 0 := by
        have hh := hx_lt
        rw [← WithZero.exp_log hx_ne] at hh
        exact WithZero.exp_lt_one_iff.mp hh
      omega
    · rw [WithZero.le_log_iff_exp_le hx_ne]
      have h2 : e.symm (WithZero.exp (-1 : ℤ)) ≤ ValuativeRel.uniformizer K := by
        refine ValuativeRel.le_uniformizer_iff.mpr ?_
        rw [← map_one e.symm]
        exact e.symm.toOrderIso.lt_iff_lt.mpr
          (WithZero.exp_lt_one_iff.mpr (by norm_num : (-1 : ℤ) < 0))
      rw [← e.apply_symm_apply (WithZero.exp (-1 : ℤ))]
      exact e.toOrderIso.le_iff_le.mpr h2
  rw [abs, if_neg hπ0, hπ, hlog, zpow_neg_one]

end
end KPCubicHaar

open MeasureTheory KPCubicHaar KPCubicUnitIndices

theorem kp_rankone_cubic_haar_power
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ζ : Integers K) (hζ : IsPrimitiveRoot ζ 3) :
    (powMonoidHom (α := Kˣ) 3).ker = rootsOfUnity 3 K ∧
    Nat.card (rootsOfUnity 3 K) = 3 ∧
    (cubeUnits K).FiniteIndex ∧
    (powMonoidHom (α := Kˣ) 3).range.FiniteIndex ∧
    ((cubeUnits K).index : ℝ) = 3 / abs K (3 : K) ∧
    ((powMonoidHom (α := Kˣ) 3).range.index : ℝ) = 9 / abs K (3 : K) := by
  refine ⟨cubeKernel_eq_rootsOfUnity K, card_cubeRoots K ζ hζ,
    cubeUnits_finiteIndex K, fieldCubes_finiteIndex K, ?_, ?_⟩
  · exact KPCubicHaarTransport.unit_cube_index K ζ hζ
  · rw [KPCubicHaarTransport.field_cube_index K, Nat.cast_mul, Nat.cast_ofNat]
    rw [show ((cubeUnits K).index : ℝ) = 3 / abs K (3 : K) from
      KPCubicHaarTransport.unit_cube_index K ζ hζ]
    ring

theorem kp_rankone_cubic_haar_power_measure
    (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (m : ℝ) (hm : 0 < m) (hvol : dx (Integers K : Set K) = ENNReal.ofReal m) :
    (multiplicativeHaar K dx).IsHaarMeasure ∧
    multiplicativeHaar K dx {x : Kˣ | (x : K) ∈ Integers K ∧ ((x⁻¹ : Kˣ) : K) ∈ Integers K} =
      ENNReal.ofReal (m * (1 - (residueCard K : ℝ)⁻¹)) := by
  exact KPCubicHaarTransport.haar_structure_and_unit_mass K dx m hm hvol

end DedekindZetaZeroFree

end
