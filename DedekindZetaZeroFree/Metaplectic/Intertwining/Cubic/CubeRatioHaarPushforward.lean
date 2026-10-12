module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.JointMellinBetaIntegrability
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubicCharacterProjection

@[expose] public section

namespace DedekindZetaZeroFree.KPActualFullKernelArithmetic

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))

local notation "K" => q.adicCompletion F

local instance cubeRatioValuativeRel : ValuativeRel K :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance cubeRatioLocalField : IsNonarchimedeanLocalField K :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
local instance cubeRatioMeasurable : MeasurableSpace K := borel K
local instance cubeRatioBorel : BorelSpace K := ⟨rfl⟩

private theorem cube_ratio_generic
    (L : Type*) [Field L] [CharZero L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [MeasurableSpace L] [BorelSpace L]
    (dx : Measure L) [dx.IsAddHaarMeasure]
    (κ : KPCubicUnitIndices.Integers L) (hκ : IsPrimitiveRoot κ 3)
    [Fintype (KPLocalTorus.CubeClasses Lˣ)]
    (cRep : KPLocalTorus.CubeClasses Lˣ → Lˣ)
    (hcRep : ∀ k, QuotientGroup.mk' (CubicCharacters.cubes Lˣ) (cRep k) = k) :
    let μ := KPCubicHaar.multiplicativeHaar L dx
    μ.prod μ = ENNReal.ofReal (KPCubicHaar.abs L 3 / 3) •
      ∑ k : KPLocalTorus.CubeClasses Lˣ,
        Measure.map (fun xy : Lˣ × Lˣ =>
          (xy.1 * xy.2 ^ 3, cRep k * xy.1)) (μ.prod μ) := by
  classical
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  let _ := isUniformAddGroup_of_addCommGroup (G := L)
  let _ : BorelSpace Lˣ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace L) = borel Lˣ
    rw [@BorelSpace.measurable_eq L _ _ _,
      Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap]⟩
  let _ := KPJointRegulator.MellinBetaIntegrability.localField_secondCountable L
  let _ : SecondCountableTopology Lˣ := Units.isEmbedding_val₀.secondCountableTopology
  let μ := KPCubicHaar.multiplicativeHaar L dx
  let _ : SigmaFinite μ := KPJointRegulator.MellinBetaIntegrability.multiplicativeHaar_sigmaFinite L dx
  have hcompact : IsCompact (KPCubicUnitIndices.Integers L : Set L) :=
    IsNonarchimedeanLocalField.isCompact_closedBall L 1
  have hopen : IsOpen (KPCubicUnitIndices.Integers L : Set L) := by
    change IsOpen ((ValuativeRel.valuation L).integer : Set L)
    exact Valued.isOpen_integer L
  have hpos : 0 < dx (KPCubicUnitIndices.Integers L : Set L) :=
    hopen.measure_pos (μ := dx) ⟨0, by simp⟩
  let _ : μ.IsHaarMeasure := (kp_rankone_cubic_haar_power_measure L dx _
    (ENNReal.toReal_pos hpos.ne' hcompact.measure_lt_top.ne)
    (ENNReal.ofReal_toReal hcompact.measure_lt_top.ne).symm).1
  let C := CubicCharacters.cubes Lˣ
  let Q : Lˣ →* KPLocalTorus.CubeClasses Lˣ := QuotientGroup.mk' C
  let R : KPLocalTorus.CubeClasses Lˣ → Set (Lˣ × Lˣ) :=
    fun k => {z | Q (z.2 / z.1) = k}
  let D : Lˣ → Lˣ × Lˣ → Lˣ × Lˣ := fun c z => (z.1*z.2,c*z.1)
  have hD (c : Lˣ) : MeasurePreserving (D c) (μ.prod μ) (μ.prod μ) := by
    have hs := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).comp
      (measurePreserving_prod_mul μ μ)
    have ht := (MeasurePreserving.id μ).prod (measurePreserving_mul_left μ c)
    convert ht.comp hs using 1
    funext z; simp [D, Function.comp_def]
  have hcube : Measure.map (fun z : Lˣ × Lˣ => (z.1,z.2^3)) (μ.prod μ) =
      ENNReal.ofReal ((C.index : ℝ)/3) • (μ.prod μ).restrict (Set.univ ×ˢ (C : Set Lˣ)) := by
    change Measure.map (Prod.map id (fun z : Lˣ => z^3)) (μ.prod μ) = _
    rw [← Measure.map_prod_map μ μ measurable_id (continuous_pow 3).measurable]
    have hc := KPCubicHaarTransport.cube_pushforward L κ hκ dx
    change Measure.map (fun y : Lˣ => y^3) μ =
      ENNReal.ofReal ((C.index : ℝ)/3) • μ.restrict (C : Set Lˣ) at hc
    rw [Measure.map_id, hc,
      Measure.prod_smul_right]
    congr 1
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hdis : DiscreteTopology (KPLocalTorus.CubeClasses Lˣ) :=
    (KPRankOneCubicProjection.local_character_count L (κ : L)
      (hκ.map_of_injective (f := (KPCubicUnitIndices.Integers L).subtype) Subtype.val_injective)).1
  let _ := hdis
  have hR (k) : MeasurableSet (R k) := by
    exact (isOpen_discrete {k}).preimage
      (QuotientGroup.continuous_mk.comp (by fun_prop)) |>.measurableSet
  have hpre (k) : D (cRep k) ⁻¹' R k = Set.univ ×ˢ (C : Set Lˣ) := by
    ext z
    simp only [D, R, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
    have he : cRep k * z.1 / (z.1*z.2) = cRep k / z.2 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_div_eq_div_val]
      field_simp
    rw [he, map_div, hcRep]
    change k / Q z.2 = k ↔ z.2 ∈ C
    simp only [div_eq_mul_inv, mul_eq_left]
    rw [inv_eq_one]
    exact QuotientGroup.eq_one_iff _
  have hmap (k) : Measure.map (fun xy : Lˣ × Lˣ => (xy.1*xy.2^3,cRep k*xy.1))
      (μ.prod μ) = ENNReal.ofReal ((C.index : ℝ)/3) • (μ.prod μ).restrict (R k) := by
    change Measure.map (D (cRep k) ∘ (fun z : Lˣ×Lˣ => (z.1,z.2^3))) _ = _
    have hC : Measurable (fun z : Lˣ×Lˣ => (z.1,z.2^3)) := by fun_prop
    rw [← Measure.map_map (hD _).measurable hC,
      hcube, Measure.map_smul _ (hD _).measurable.aemeasurable, ← hpre,
      ← Measure.restrict_map (hD _).measurable (hR _), (hD _).map_eq]
  have hpartition : (μ.prod μ) = ∑ k, (μ.prod μ).restrict (R k) := by
    have hd : Pairwise (Function.onFun Disjoint R) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro z hi hj
      exact hij (hi.symm.trans hj)
    have hu : (⋃ k, R k) = Set.univ := by
      ext z; simp only [Set.mem_iUnion, R, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨Q (z.2/z.1), rfl⟩
    have hp := Measure.restrict_iUnion (μ := μ.prod μ) hd hR
    rw [hu, Measure.restrict_univ] at hp
    simpa only [Measure.sum_fintype] using hp
  have hind : (C.index : ℝ) = 9 / KPCubicHaar.abs L (3:L) :=
    (kp_rankone_cubic_haar_power L κ hκ).2.2.2.2.2
  have hδ : 0 < KPCubicHaar.abs L (3:L) := KPCubicHaar.abs_pos L (by norm_num)
  change μ.prod μ = ENNReal.ofReal (KPCubicHaar.abs L 3 / 3) •
    ∑ k, Measure.map (fun xy : Lˣ×Lˣ => (xy.1*xy.2^3,cRep k*xy.1)) (μ.prod μ)
  simp_rw [hmap]
  rw [← Finset.smul_sum, smul_smul]
  have hcancel : ENNReal.ofReal (KPCubicHaar.abs L (3:L)/3) *
      ENNReal.ofReal ((C.index : ℝ)/3) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), hind]
    have he : KPCubicHaar.abs L (3:L)/3 * (9 / KPCubicHaar.abs L (3:L)/3) = 1 := by
      field_simp; ring
    rw [he]; simp
  rw [hcancel, one_smul]
  exact hpartition

theorem actual_cube_ratio_pushforward
    (dx : Measure K) [dx.IsAddHaarMeasure]
    (κ : KPCubicUnitIndices.Integers K) (hκ : IsPrimitiveRoot κ 3)
    [Fintype (KPLocalTorus.CubeClasses Kˣ)]
    (cRep : KPLocalTorus.CubeClasses Kˣ → Kˣ)
    (hcRep : ∀ k, QuotientGroup.mk' (CubicCharacters.cubes Kˣ) (cRep k) = k) :
    let μ := KPCubicHaar.multiplicativeHaar K dx
    μ.prod μ = ENNReal.ofReal (KPCubicHaar.abs K 3 / 3) •
      ∑ k : KPLocalTorus.CubeClasses Kˣ,
        Measure.map (fun xy : Kˣ × Kˣ =>
          (xy.1 * xy.2 ^ 3, cRep k * xy.1)) (μ.prod μ) := by
  exact cube_ratio_generic K dx κ hκ cRep hcRep

end

end DedekindZetaZeroFree.KPActualFullKernelArithmetic
