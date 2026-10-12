module

public import DedekindZetaZeroFree.Metaplectic.Kubota.GenuineCuspLinesAndUnitaryMonodromy

@[expose] public section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.OrbitMultiplicity

theorem sum_restrict_of_constant_multiplicity
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (ν : Measure X) (s : Set X) (T : I → Set X)
    (hT : ∀ i, MeasurableSet (T i)) (c : ℝ≥0∞)
    (hc : ∀ᵐ x ∂ν.restrict s, (∑' i, (T i).indicator (fun _ => (1 : ℝ≥0∞)) x) = c) :
    (Measure.sum fun i => ν.restrict (T i ∩ s)) = c • ν.restrict s := by
  calc
    (Measure.sum fun i => ν.restrict (T i ∩ s)) =
        Measure.sum (fun i => (ν.restrict s).withDensity
          ((T i).indicator (fun _ => (1 : ℝ≥0∞)))) := by
      congr 1
      funext i
      rw [withDensity_indicator (hT i), withDensity_const, one_smul,
        Measure.restrict_restrict (hT i)]
    _ = (ν.restrict s).withDensity
        (fun x => ∑' i, (T i).indicator (fun _ => (1 : ℝ≥0∞)) x) := by
      rw [← withDensity_tsum (fun i => measurable_const.indicator (hT i))]
      congr 1
      funext x
      exact ENNReal.tsum_apply
    _ = (ν.restrict s).withDensity (fun _ => c) := withDensity_congr_ae hc
    _ = c • ν.restrict s := withDensity_const c

theorem integral_comparison
    {H X : Type*} [Group H] [Countable H] [MeasurableSpace X]
    [MulAction H X] [MeasurableConstSMul H X]
    (ν : Measure X) [SMulInvariantMeasure H X ν]
    {s t : Set X} (hs : IsFundamentalDomain H s ν)
    (ht : MeasurableSet t) (c : ℝ≥0∞) (hctop : c ≠ ⊤)
    (hcount : ∀ᵐ x ∂ν.restrict s,
      (∑' g : H, (g • t).indicator (fun _ => (1 : ℝ≥0∞)) x) = c)
    (f : X → ℝ) (hinv : ∀ (g : H) (x : X), f (g • x) = f x)
    (hfs : IntegrableOn f s ν) (hft : IntegrableOn f t ν) :
    (∫ x in t, f x ∂ν) = c.toReal * ∫ x in s, f x ∂ν := by
  have hm : (Measure.sum fun g : H => ν.restrict (g • t ∩ s)) =
      c • ν.restrict s :=
    sum_restrict_of_constant_multiplicity ν s (fun g : H => g • t)
      (fun g => ht.const_smul g) c hcount
  have hi : Integrable f (Measure.sum fun g : H => ν.restrict (g • t ∩ s)) := by
    rw [hm]
    exact hfs.smul_measure hctop
  calc
    (∫ x in t, f x ∂ν) = ∑' g : H, ∫ x in g • t ∩ s, f x ∂ν := by
      rw [hs.setIntegral_eq_tsum' hft]
      simp only [hinv]
    _ = ∫ x, f x ∂(Measure.sum fun g : H => ν.restrict (g • t ∩ s)) :=
      (integral_sum_measure hi).symm
    _ = c.toReal * ∫ x in s, f x ∂ν := by
      rw [hm, integral_smul_measure, smul_eq_mul]

theorem integral_eq_zero
    {H X : Type*} [Group H] [Countable H] [MeasurableSpace X]
    [MulAction H X] [MeasurableConstSMul H X]
    (ν : Measure X) [SMulInvariantMeasure H X ν]
    {s t : Set X} (hs : IsFundamentalDomain H s ν)
    (ht : MeasurableSet t) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hcount : ∀ᵐ x ∂ν.restrict s,
      (∑' g : H, (g • t).indicator (fun _ => (1 : ℝ≥0∞)) x) = c)
    (f : X → ℝ) (hinv : ∀ (g : H) (x : X), f (g • x) = f x)
    (hfs : IntegrableOn f s ν) (hft : IntegrableOn f t ν)
    (hzero : (∫ x in t, f x ∂ν) = 0) :
    (∫ x in s, f x ∂ν) = 0 := by
  have heq := integral_comparison ν hs ht c hctop hcount f hinv hfs hft
  rw [hzero] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (ENNReal.toReal_ne_zero.mpr ⟨hc0, hctop⟩)

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.OrbitMultiplicity

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal Pointwise
namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection
variable {F : Type} [Field F] [NumberField F]
 {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
 {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}

private theorem actual_translation_action
    (G : KPCuspCharts.ChartOutput F hF S D)
    (l : D.L) (x : KPCuspCharts.Cross F) :
    G.crossAction (D.inclusion (Multiplicative.ofAdd l)) x =
      (x.1 + KPCuspCharts.embedding F l.val, x.2) := by
  let s := D.inclusion (Multiplicative.ofAdd l)
  obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
  have h := G.actual_action s A hA hc (x, 0)
  rw [G.unipotent_action l (x, 0)] at h
  have hp := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective h
  rw [G.crossAction_formula s A hA hc]
  exact (congrArg Prod.fst hp).symm

theorem existsUnique_ratio_horizontal_representative
    (G : KPCuspCharts.ChartOutput F hF S D)
    (A : Set (KPCuspCharts.Horizontal F))
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (u : D.E) (x : KPCuspCharts.Cross F) :
    ∃! s : S, D.ratio s = u ∧ (G.crossAction s x).1 ∈ A := by
  obtain ⟨t, ht⟩ := D.surjective u
  obtain ⟨l, hl, hlu⟩ := hA (G.crossAction t x).1
  refine ⟨D.inclusion (Multiplicative.ofAdd l) * t, ?_, ?_⟩
  · constructor
    · have hk : D.ratio (D.inclusion (Multiplicative.ofAdd l)) = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [← D.exact]
        exact ⟨_, rfl⟩
      simp [hk, ht]
    · rw [map_mul, Homeomorph.mul_apply, actual_translation_action]
      exact hl
  · intro s hs
    have hk : s * t⁻¹ ∈ D.ratio.ker := by
      simp [MonoidHom.mem_ker, hs.1, ht]
    rw [← D.exact] at hk
    obtain ⟨m, hm⟩ := hk
    have hsform : s = D.inclusion m * t := by
      rw [hm, inv_mul_cancel_right]
    have he : Multiplicative.toAdd m = l := by
      apply hlu
      have hh := hs.2
      rw [hsform, map_mul, Homeomorph.mul_apply] at hh
      change (G.crossAction (D.inclusion (Multiplicative.ofAdd (Multiplicative.toAdd m)))
        (G.crossAction t x)).1 ∈ A at hh
      rw [actual_translation_action] at hh
      exact hh
    rw [hsform]
    congr 1
    exact congrArg D.inclusion (congrArg Multiplicative.ofAdd he)

theorem crossAction_shape (G : KPCuspCharts.ChartOutput F hF S D)
    (s : S) (x : KPCuspCharts.Cross F) :
    (G.crossAction s x).2 = x.2 +
      KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio s)) := by
  obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
  rw [G.crossAction_formula s A hA hc]
  rfl

def orbitRatioEquiv (G : KPCuspCharts.ChartOutput F hF S D)
 (A : Set (KPCuspCharts.Horizontal F))
 (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
   y + KPCuspCharts.embedding F l.val ∈ A)
 (B : Set (KPCuspCharts.Shape F)) (x : KPCuspCharts.Cross F) :
 {s : S // G.crossAction s x ∈ A ×ˢ B} ≃
 {u : D.E // x.2 + KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) ∈ B} := by
 let P := fun u : D.E => existsUnique_ratio_horizontal_representative G A hA u x
 refine {
   toFun := fun s => ⟨D.ratio s.val, ?_⟩
   invFun := fun u => ⟨(P u.val).choose, ?_⟩
   left_inv := ?_
   right_inv := ?_ }
 · rw [← crossAction_shape G s.val x]
   exact s.property.2
 · constructor
   · exact (P u.val).choose_spec.1.2
   · rw [crossAction_shape, (P u.val).choose_spec.1.1]
     exact u.property
 · intro s
   apply Subtype.ext
   exact ((P (D.ratio s.val)).choose_spec.2 s.val ⟨rfl, s.property.1⟩).symm
 · intro u
   apply Subtype.ext
   exact (P u.val).choose_spec.1.1

def shapeUnitEquivKernel
 (B : Set (KPCuspCharts.Shape F))
 (hB : ∀ b : KPCuspCharts.Shape F, ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits,
   b + v.val ∈ B)
 (b : KPCuspCharts.Shape F) :
 {u : D.E // b + KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul u) ∈ B} ≃
 KPCuspCharts.kernelUnits F hF D.E D.integralUnits := by
 let L := KPCuspLogShape.logarithm F hF D.E D.integralUnits
 let v := (hB b).choose
 have hv := (hB b).choose_spec.1
 have hvu := (hB b).choose_spec.2
 let w := v.property.choose
 have hw := v.property.choose_spec
 let t : D.E := Additive.toMul w
 have ht : L (Additive.ofMul t) = v.val := hw
 refine {
   toFun := fun u => ⟨u.val * t⁻¹, ?_⟩
   invFun := fun k => ⟨k.val * t, ?_⟩
   left_inv := ?_
   right_inv := ?_ }
 · change L (Additive.ofMul (u.val * t⁻¹)) = 0
   have hu : L (Additive.ofMul u.val) = v.val := by
     have hmem : L (Additive.ofMul u.val) ∈ KPCuspLogShape.logLattice F hF D.E D.integralUnits :=
       ⟨_, rfl⟩
     exact congrArg Subtype.val (hvu ⟨_, hmem⟩ u.property)
   change L (Additive.ofMul u.val - Additive.ofMul t) = 0
   rw [map_sub, hu, ht, sub_self]
 · change b + L (Additive.ofMul (k.val * t)) ∈ B
   change b + L (Additive.ofMul k.val + Additive.ofMul t) ∈ B
   rw [map_add, show L (Additive.ofMul k.val) = 0 from k.property, zero_add, ht]
   exact hv
 · intro u
   apply Subtype.ext
   exact inv_mul_cancel_right _ _
 · intro k
   apply Subtype.ext
   exact mul_inv_cancel_right _ _

theorem rectangle_orbit_multiplicity (G : KPCuspCharts.ChartOutput F hF S D)
 (A : Set (KPCuspCharts.Horizontal F))
 (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
   y + KPCuspCharts.embedding F l.val ∈ A)
 (B : Set (KPCuspCharts.Shape F))
 (hB : ∀ b : KPCuspCharts.Shape F, ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits,
   b + v.val ∈ B)
 (x : KPCuspCharts.Cross F) :
 letI := KPCuspCharts.homeomorphAction G.crossAction
 (∑' g : S, (g • (A ×ˢ B)).indicator (fun _ => (1 : ℝ≥0∞)) x) =
   (ENat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) := by
 letI := KPCuspCharts.homeomorphAction G.crossAction
 let T : Set S := {s | G.crossAction s x ∈ A ×ˢ B}
 have hi : (∑' g : S, (g • (A ×ˢ B)).indicator (fun _ => (1 : ℝ≥0∞)) x) =
     ∑' s : S, T.indicator (fun _ => (1 : ℝ≥0∞)) s := by
   rw [← (Equiv.inv S).tsum_eq]
   apply tsum_congr
   intro s
   have hm : x ∈ s⁻¹ • (A ×ˢ B) ↔ s • x ∈ A ×ˢ B := Set.mem_inv_smul_set_iff
   simp only [Set.indicator, Equiv.inv_apply]
   have hm' : x ∈ s⁻¹ • (A ×ˢ B) ↔ s ∈ T := hm
   rw [hm']
   split <;> simp_all
 rw [hi, ← tsum_subtype]
 let e := (orbitRatioEquiv G A hA B x).trans (shapeUnitEquivKernel B hB x.2)
 change (∑' _ : T, (1 : ℝ≥0∞)) = _
 rw [ENNReal.tsum_one]
 exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) (ENat.card_congr e)

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end

section
noncomputable section
open MeasureTheory
open scoped Classical
namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

theorem lattice_exact_domain {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  (L : Submodule ℤ X) [DiscreteTopology L] [IsZLattice ℝ L] :
  ∃ A : Set X, MeasurableSet A ∧ Bornology.IsBounded A ∧
    ∀ x : X, ∃! l : L, x + l.val ∈ A := by
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ
  have hb : Submodule.span ℤ (Set.range b) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b,
    ZSpan.fundamentalDomain_isBounded b, ?_⟩
  intro x
  have h := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  rw [hb] at h
  simpa only [Submodule.vadd_def, vadd_eq_add, add_comm] using h

variable {F : Type} [Field F] [NumberField F]
 {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
 {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}

theorem actual_exact_comparison_rectangle (G : KPCuspCharts.ChartOutput F hF S D) :
 ∃ A : Set (KPCuspCharts.Horizontal F), ∃ B : Set (KPCuspCharts.Shape F),
 MeasurableSet A ∧ Bornology.IsBounded A ∧ MeasurableSet B ∧ Bornology.IsBounded B ∧
 (∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
   y + KPCuspCharts.embedding F l.val ∈ A) ∧
 (∀ b : KPCuspCharts.Shape F, ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits,
   b + v.val ∈ B) := by
 obtain ⟨hd, hl⟩ := G.lattice
 letI := hd
 letI := hl
 obtain ⟨A, hAm, hAb, hA⟩ := lattice_exact_domain
   (KPCuspCharts.translationLattice F D.L).toIntSubmodule
 obtain ⟨hld, hll⟩ := (kp_cusp_log_unit_shape F hF D.E D.integralUnits D.unitIndex).1
 letI := hld
 letI := hll
 obtain ⟨B, hBm, hBb, hB⟩ := lattice_exact_domain
   (KPCuspLogShape.logLattice F hF D.E D.integralUnits)
 refine ⟨A, B, hAm, hAb, hBm, hBb, ?_, hB⟩
 have hinj : Function.Injective (KPCuspCharts.embedding F) := by
   intro a b hab
   have h0 := congrFun hab ⟨0, G.positive_dimension⟩
   exact (KPCusp.complexPlace F ⟨0, G.positive_dimension⟩).embedding.injective h0
 intro y
 obtain ⟨z, hz, hzu⟩ := hA y
 obtain ⟨a, ha, haz⟩ := z.property
 refine ⟨⟨a, ha⟩, ?_, ?_⟩
 · simpa only [haz] using hz
 · intro l hl
   have he : KPCuspCharts.embedding F l.val = z.val :=
     congrArg Subtype.val (hzu ⟨_, ⟨l.val, l.property, rfl⟩⟩ hl)
   apply Subtype.ext
   exact hinj (he.trans haz.symm)
end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end
