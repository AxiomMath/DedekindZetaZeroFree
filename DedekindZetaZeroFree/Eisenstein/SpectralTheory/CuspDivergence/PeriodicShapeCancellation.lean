module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.TangentialRegularity
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.HorizontalAveraging
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.MeanZeroIntegration

@[expose] public section

noncomputable section
open MeasureTheory Topology Filter
open scoped Classical Topology
namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice
open KPMeanZeroWeightedEnergy HyperbolicChart
open KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

def horizontalDivergence (F : Type) [Field F] [NumberField F]
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) : ℝ :=
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c,t))
  ∑ i : Fin d,
    (((Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i 0 (fun q => W q i 1) x).re +
    ((Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i 1 (fun q => W q i 2) x).re)

def shapeDivergence (F : Type) [Field F] [NumberField F]
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) : ℝ :=
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c,t))
  ∑ i : Fin d,
    ((coordinateDerivative d i 2 (fun q => W q i 0) x).re -
    (∑ j : Fin d, (coordinateDerivative d j 2 (fun q => W q i 0) x).re) / (d : ℝ))

theorem tangentialDivergence_eq_horizontal_add_shape
    {F : Type} [Field F] [NumberField F]
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    tangentialDivergence F W c t = horizontalDivergence F W c t + shapeDivergence F W c t := by
  unfold tangentialDivergence horizontalDivergence shapeDivergence
  dsimp only
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def projectedShapeDirection (d : ℕ) (hd : 0 < d) (i : Fin d) : KPCuspLogShape.hyperplane d :=
  ⟨fun j => (if j = i then 1 else 0) - 1 / (d : ℝ), by
    change (∑ j : Fin d, ((if j = i then 1 else 0) - 1 / (d : ℝ))) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_ite_eq']
    simp [ne_of_gt hd, Nat.cast_ne_zero, mul_div_cancel₀]⟩

 def shapeEmbedding (d : ℕ) : KPCuspLogShape.hyperplane d →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun := fun b => WithLp.toLp 2 (fun j => if j.2 = 2 then b.val j.1 else 0)
    map_add' := by intro b c; ext ⟨i,k⟩; simp; split <;> simp_all
    map_smul' := by intro r b; ext ⟨i,k⟩; simp }

private theorem shapeEmbedding_direction (d : ℕ) (hd : 0 < d) (i : Fin d) :
    shapeEmbedding d (projectedShapeDirection d hd i) =
      coordinateVector d i 2 - (1 / (d : ℝ)) • ∑ j : Fin d, coordinateVector d j 2 := by
  ext ⟨j,k⟩
  simp [shapeEmbedding, projectedShapeDirection, coordinateVector]
  fin_cases k <;> simp
  have hh : (Finset.univ.filter (fun x : Fin d => j = x)) = {j} := by ext a; simp [eq_comm]
  rw [hh]
  simp

theorem restricted_verticalFlux_fderiv {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (hW : ∀ i, Differentiable ℝ (fun q => W q i 0))
    (c : KPCuspCharts.Cross F) (t : ℝ) (i : Fin (KPCuspLogShape.dimension F)) :
    fderiv ℝ (fun b : KPCuspCharts.Shape F =>
      W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((c.1,b),t))) i 0)
      c.2 (projectedShapeDirection _ hd i) =
      coordinateDerivative _ i 2 (fun q => W q i 0)
        (real _ (KPCuspCharts.toArch F (c,t))) -
      (∑ j, coordinateDerivative _ j 2 (fun q => W q i 0)
        (real _ (KPCuspCharts.toArch F (c,t)))) / (KPCuspLogShape.dimension F : ℝ) := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F ((c.1,(0 : KPCuspCharts.Shape F)),t))
  have he : (fun b : KPCuspCharts.Shape F => real d (KPCuspCharts.toArch F ((c.1,b),t))) =
      fun b => x + shapeEmbedding d b := by
    funext b
    ext ⟨j,k⟩
    fin_cases k <;> simp [x, real, KPCuspCharts.toArch, shapeEmbedding]
  have hc := ((shapeEmbedding d).hasFDerivAt (x := c.2)).add_const x
  have he' : (fun b => shapeEmbedding d b + x) = fun b => x + shapeEmbedding d b := by
    funext b; exact add_comm _ _
  rw [he'] at hc
  have h := (hW i).differentiableAt.hasFDerivAt.comp c.2 hc
  rw [← he] at h
  dsimp only [Function.comp_def] at h
  rw [h.fderiv]
  rw [← congrFun he c.2]
  change (fderiv ℝ (fun q => W q i 0) (real d (KPCuspCharts.toArch F (c,t))))
      (shapeEmbedding d (projectedShapeDirection d hd i)) = _
  rw [shapeEmbedding_direction d hd i]
  simp only [map_sub, map_smul, map_sum, coordinateDerivative, one_div, smul_eq_mul, div_eq_mul_inv]
  simp only [d, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_one]
  ring

theorem shapeDivergence_eq_sum_restricted_fderiv
    {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (hW : ∀ i, Differentiable ℝ (fun q => W q i 0))
    (c : KPCuspCharts.Cross F) (t : ℝ) :
    shapeDivergence F W c t = ∑ i,
      (fderiv ℝ (fun b : KPCuspCharts.Shape F =>
        W (real _ (KPCuspCharts.toArch F ((c.1,b),t))) i 0)
        c.2 (projectedShapeDirection _ hd i)).re := by
  unfold shapeDivergence
  dsimp only
  apply Finset.sum_congr rfl
  intro i hi
  rw [restricted_verticalFlux_fderiv hd W hW c t i]
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.re_sum]

theorem shapeDivergence_eq_zero_of_dimension_le_one
    {F : Type} [Field F] [NumberField F]
    (hd : KPCuspLogShape.dimension F ≤ 1)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (c : KPCuspCharts.Cross F) (t : ℝ) : shapeDivergence F W c t = 0 := by
  unfold shapeDivergence
  dsimp only
  apply Finset.sum_eq_zero
  intro i hi
  have hd1 : KPCuspLogShape.dimension F = 1 := by
    have hi := i.isLt
    omega
  have hu : (Finset.univ : Finset (Fin (KPCuspLogShape.dimension F))) = {i} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Fin.ext
    have hj := j.isLt
    have hi := i.isLt
    omega
  rw [hu]
  simp [hd1]

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]
private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff
private theorem smooth_mean (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)
 def verticalLine {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) (c : KPCuspCharts.Cross F) (t : ℝ)
    (i : Fin (KPCuspLogShape.dimension F)) (r : ℝ) : KPCuspCharts.Coordinates F :=
  ((c.1,c.2 + r • projectedShapeDirection _ hd i),t + r / (KPCuspLogShape.dimension F : ℝ))
private theorem real_verticalLine {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F) (c : KPCuspCharts.Cross F) (t : ℝ)
    (i : Fin (KPCuspLogShape.dimension F)) (r : ℝ) :
    real _ (KPCuspCharts.toArch F (verticalLine hd c t i r)) =
      real _ (KPCuspCharts.toArch F (c,t)) + r • coordinateVector _ i 2 := by
  ext ⟨j,k⟩
  fin_cases k <;> simp [verticalLine, real, KPCuspCharts.toArch,
    projectedShapeDirection, coordinateVector]
  split_ifs <;> simp_all [div_eq_mul_inv] <;> ring

private theorem verticalFlux_eq_line_deriv
    {F : Type} [Field F] [NumberField F] {T : ℝ}
    (hd : 0 < KPCuspLogShape.dimension F)
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (c : KPCuspCharts.Cross F) (t : ℝ) (ht : T < t)
    (i : Fin (KPCuspLogShape.dimension F)) :
    (cutoffScalarFlux _ u a (real _ (KPCuspCharts.toArch F (c,t))) i 0).re =
      a t * deriv (fun r => u (KPCuspCharts.toArch F (verticalLine hd c t i r))) 0 := by
  let d := KPCuspLogShape.dimension F
  let x := real d (KPCuspCharts.toArch F (c,t))
  let g : Space d → ℂ := fun q => (u (arch d q) : ℂ)
  have hx : T < KPCuspLogShape.meanHeight d (arch d x) := by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F hd]; exact ht
  have hu' : ContDiffAt ℝ (⊤ : ℕ∞) g x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((hu.contDiffAt ((isOpen_lt continuous_const (smooth_mean d).continuous).mem_nhds hx)).comp x
        (smooth_arch d).contDiffAt)
  have hline : HasDerivAt (fun r : ℝ => real d (KPCuspCharts.toArch F (verticalLine hd c t i r)))
      (coordinateVector d i 2) 0 := by
    have he : (fun r : ℝ => real d (KPCuspCharts.toArch F (verticalLine hd c t i r))) =
        fun r => x + r • coordinateVector d i 2 := funext (real_verticalLine hd c t i)
    rw [he]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector d i 2)).const_add x
  have hbase : real d (KPCuspCharts.toArch F (verticalLine hd c t i 0)) = x := by
    simp [verticalLine, x]
  have hg : HasFDerivAt g (fderiv ℝ g x)
      (real d (KPCuspCharts.toArch F (verticalLine hd c t i 0))) := by
    rw [hbase]
    exact (hu'.differentiableAt (by simp)).hasFDerivAt
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (hg.comp_hasDerivAt 0 hline)
  have hr' : HasDerivAt (fun r => u (KPCuspCharts.toArch F (verticalLine hd c t i r)))
      (coordinateDerivative d i 2 g x).re 0 := by
    simpa [Function.comp_def, g, arch_real, Complex.reCLM_apply, coordinateDerivative] using hr
  rw [hr'.deriv]
  simp [cutoffScalarFlux, scalarDifferential, differential, arch_real,
    KPCuspCharts.toArch_meanHeight F hd, d, x, g]

theorem cutoff_verticalFlux_crossAction_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (s : S) (c : KPCuspCharts.Cross F) (i : Fin (KPCuspLogShape.dimension F)) :
    (cutoffScalarFlux _ u a (real _ (KPCuspCharts.toArch F (G.crossAction s c,t))) i 0).re =
      (cutoffScalarFlux _ u a (real _ (KPCuspCharts.toArch F (c,t))) i 0).re := by
  by_cases ht : T < t
  · let hd := G.positive_dimension
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    have hact (r : ℝ) : KPCuspSiegel.action F s.val
        (KPCuspCharts.toArch F (verticalLine hd c t i r)) =
        KPCuspCharts.toArch F (verticalLine hd (G.crossAction s c) t i r) := by
      rw [G.actual_action s A hA hc, G.crossAction_formula s A hA hc]
      congr 1
      ext : 2
      · rfl
      · simp [KPCuspCharts.affine, KPCuspCharts.crossAffine, verticalLine, add_assoc, add_comm, add_left_comm]
      · rfl
    have huEv : (fun r => u (KPCuspCharts.toArch F (verticalLine hd (G.crossAction s c) t i r)))
        =ᶠ[nhds 0] fun r => u (KPCuspCharts.toArch F (verticalLine hd c t i r)) := by
      have hn : ∀ᶠ r : ℝ in nhds 0, T < t + r / (KPCuspLogShape.dimension F : ℝ) := by
        exact (isOpen_lt continuous_const (continuous_const.add (continuous_id.div_const _))).mem_nhds
          (by simpa using ht)
      filter_upwards [hn] with r hr
      apply hinv ⟨verticalLine hd (G.crossAction s c) t i r, hr⟩ ⟨verticalLine hd c t i r, hr⟩
      exact ⟨s, hact r⟩
    rw [verticalFlux_eq_line_deriv hd u hu a _ t ht,
      verticalFlux_eq_line_deriv hd u hu a _ t ht, huEv.deriv_eq]
  · have hat : a t = 0 := image_eq_zero_of_notMem_tsupport (fun hm => ht (ha.2.2 hm))
    simp [cutoffScalarFlux, arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension, hat]

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro ⟨i,k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using Complex.reCLM.contDiff.comp
      (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using Complex.imCLM.contDiff.comp
      (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)
set_option maxHeartbeats 600000 in

theorem cutoff_verticalFlux_haar_average_logLattice_periodic
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (i : Fin (KPCuspLogShape.dimension F)) :
    ∃ f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ,
      (∀ (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F),
        f (QuotientAddGroup.mk x) b =
        (cutoffScalarFlux (KPCuspLogShape.dimension F) u a
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t))) i 0).re) ∧
      Continuous (fun b : KPCuspCharts.Shape F => ∫ z, f z b ∂μ) ∧
      (∀ (b : KPCuspCharts.Shape F)
        (v : KPCuspLogShape.logLattice F hF D.E D.integralUnits),
        (∫ z, f z (b + v.val) ∂μ) = ∫ z, f z b ∂μ) := by
  let d := KPCuspLogShape.dimension F
  let k : KPCuspCharts.Cross F → ℝ := fun c =>
    (cutoffScalarFlux d u a (real d (KPCuspCharts.toArch F (c,t))) i 0).re
  have hki (s : S) (c : KPCuspCharts.Cross F) : k (G.crossAction s c) = k c :=
    cutoff_verticalFlux_crossAction_invariant G u hu hinv a ha t s c i
  have hkc : Continuous k := by
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun c : KPCuspCharts.Cross F =>
        real d (KPCuspCharts.toArch F (c,t))) :=
      (smooth_real d).comp (((KPCuspCharts.toArch_contDiff F).of_le (by simp)).comp
        (contDiff_id.prodMk contDiff_const))
    exact (Complex.reCLM.contDiff.comp
      ((cutoff_flux_component_contDiff d u hu a ha i 0).comp hc)).continuous
  have hrel (b : KPCuspCharts.Shape F) (x y : KPCuspCharts.Horizontal F)
      (hxy : QuotientAddGroup.leftRel
        (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)) x y) :
      k (x,b) = k (y,b) := by
    obtain ⟨l, hl, hel⟩ := QuotientAddGroup.leftRel_apply.mp hxy
    have hy : y = x + KPCuspCharts.embedding F l := by rw [hel]; abel
    rw [hy]
    simpa only [crossAction_inclusion] using (hki
      (D.inclusion (Multiplicative.ofAdd ⟨l,hl.1⟩)) (x,b)).symm
  let f : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ :=
    fun z b => Quotient.lift (fun x => k (x,b)) (hrel b) z
  have hfm (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) :
      f (QuotientAddGroup.mk x) b = k (x,b) := rfl
  obtain ⟨hc, hi⟩ := horizontal_average_continuous_invariant G μ hμ hprob f hkc hki
  refine ⟨f,hfm,?_,?_⟩
  · have hp : Continuous (fun b : KPCuspCharts.Shape F =>
        ((0 : KPCuspCharts.Horizontal F), b)) := continuous_const.prodMk continuous_id
    have hh := hc.comp hp
    change Continuous (fun b : KPCuspCharts.Shape F => ∫ z, f z b ∂μ) at hh
    exact hh
  · intro b v
    obtain ⟨e,he⟩ := v.property
    obtain ⟨s,hs⟩ := D.surjective e.toMul
    have hi' := hi s ((0 : KPCuspCharts.Horizontal F),b)
    obtain ⟨A,hA,hc⟩ := D.upper s.val s.property
    rw [G.crossAction_formula s A hA hc] at hi'
    change (∫ z, f z (b + KPCuspLogShape.logarithm F hF D.E D.integralUnits
      (Additive.ofMul (D.ratio s))) ∂μ) = _ at hi'
    rw [hs] at hi'
    change (∫ z, f z (b + KPCuspLogShape.logarithm F hF D.E D.integralUnits e) ∂μ) = _ at hi'
    rw [he] at hi'
    exact hi'

private theorem integral_lift_scale
    {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {L : AddSubgroup X} [Countable L] [T2Space (X ⧸ L)] [SecondCountableTopology (X ⧸ L)]
    (ν : Measure X) [ν.IsAddHaarMeasure] [ν.IsAddRightInvariant] [SigmaFinite ν]
    (μ : Measure (X ⧸ L)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {A : Set X} (hA : IsAddFundamentalDomain L.op A ν) (hAfin : ν A ≠ ⊤)
    (f : X ⧸ L → ℝ) (hf : AEStronglyMeasurable f μ) :
    (∫ x in A, f (QuotientAddGroup.mk x) ∂ν) = (ν A).toReal * ∫ z, f z ∂μ := by
  let μ' : Measure (X ⧸ L) := ν A • μ
  letI : Measure.IsAddLeftInvariant μ' := inferInstanceAs (Measure.IsAddLeftInvariant (ν A • μ))
  letI : IsFiniteMeasure μ' := by
    dsimp [μ']
    exact ⟨by simp [hAfin.lt_top]⟩
  letI : HasAddFundamentalDomain L.op X ν := hA.hasAddFundamentalDomain ν
  letI : AddQuotientMeasureEqMeasurePreimage ν μ' :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage ν (by
      rw [hA.covolume_eq_volume ν]
      simp [μ'])
  have hmp := measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage ν hA μ'
  have hm : AEStronglyMeasurable f μ' := hf.smul_measure (ν A)
  rw [← hmp.map_eq] at hm
  rw [← integral_map hmp.measurable.aemeasurable hm, hmp.map_eq]
  simp [μ', integral_smul_measure]

private theorem kernelLattice_one {F : Type} [Field F] [NumberField F]
  {S : Subgroup (KPCuspArithmetic.PGL2 F)} (D : KPCuspCharts.ParabolicData F S) :
  KPCuspGenuineMonodromy.kernelLattice S D (1 : S →* rootsOfUnity 3 F) = D.L := by
  ext x
  simp [KPCuspGenuineMonodromy.kernelLattice]
private theorem fullTorus_probability_haar {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ μ : Measure (KPCuspCharts.Torus F D.L), μ.IsAddHaarMeasure ∧ IsProbabilityMeasure μ := by
  obtain ⟨hd,hL⟩ := G.lattice
  letI := hd
  letI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  letI := G.compact_torus
  let μ := Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts (KPCuspCharts.Torus F D.L))
  refine ⟨μ,inferInstance,?_⟩
  constructor
  exact Measure.addHaarMeasure_self
set_option maxHeartbeats 600000 in

theorem cutoff_verticalFlux_exact_domain_logLattice_periodic
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (A : Set (KPCuspCharts.Horizontal F)) (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L, y + KPCuspCharts.embedding F l.val ∈ A)
    (b : KPCuspCharts.Shape F) (v : KPCuspLogShape.logLattice F hF D.E D.integralUnits)
    (i : Fin (KPCuspLogShape.dimension F)) :
    (∫ x in A, (cutoffScalarFlux (KPCuspLogShape.dimension F) u a
      (real _ (KPCuspCharts.toArch F ((x,b + v.val),t))) i 0).re) =
    ∫ x in A, (cutoffScalarFlux (KPCuspLogShape.dimension F) u a
      (real _ (KPCuspCharts.toArch F ((x,b),t))) i 0).re := by
  obtain ⟨hd,hL⟩ := G.lattice
  letI := hd
  letI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  letI : Countable (KPCuspCharts.translationLattice F D.L) := countable_of_Lindelof_of_discrete
  obtain ⟨μ,hμ,hprob⟩ := fullTorus_probability_haar G
  letI := hμ
  letI := hprob
  let ρ : S →* rootsOfUnity 3 F := 1
  have heq : KPCuspGenuineMonodromy.kernelLattice S D ρ = D.L := kernelLattice_one D
  have hx := cutoff_verticalFlux_haar_average_logLattice_periodic (ρ := ρ) G u hu hinv a ha t
  unfold KPCuspGenuineMonodromy.KernelTorus at hx
  rw [heq] at hx
  obtain ⟨f,hf,hc,hp⟩ := hx μ hμ hprob i
  have hinj : Function.Injective (KPCuspCharts.embedding F) := by
    intro a c hac
    have h0 := congrFun hac ⟨0, G.positive_dimension⟩
    exact (KPCusp.complexPlace F ⟨0, G.positive_dimension⟩).embedding.injective h0
  have htiling : ∀ y : KPCuspCharts.Horizontal F,
      ∃! l : (KPCuspCharts.translationLattice F D.L).op, l +ᵥ y ∈ A := by
    intro y
    obtain ⟨a, ha, hau⟩ := hA y
    let l : KPCuspCharts.translationLattice F D.L :=
      ⟨KPCuspCharts.embedding F a.val, ⟨a.val, a.property, rfl⟩⟩
    refine ⟨⟨AddOpposite.op l.val, l.property⟩, ?_, ?_⟩
    · exact ha
    · intro k hk
      obtain ⟨c, hc, hec⟩ := k.property
      have hkc : y + KPCuspCharts.embedding F c ∈ A := by
        change y + k.val.unop ∈ A at hk
        rwa [← hec] at hk
      have he := hau ⟨c, hc⟩ hkc
      apply Subtype.ext
      apply AddOpposite.unop_injective
      exact hec.symm.trans (congrArg (fun x : D.L => KPCuspCharts.embedding F x.val) he)
  have hfd : IsAddFundamentalDomain (KPCuspCharts.translationLattice F D.L).op A volume :=
    IsAddFundamentalDomain.mk' hAm.nullMeasurableSet htiling
  have hfc (b : KPCuspCharts.Shape F) : Continuous (fun z => f z b) := by
    apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
    simp_rw [Function.comp_def,hf]
    have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspCharts.Horizontal F =>
        real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t))) := by
      exact (smooth_real _).comp (((KPCuspCharts.toArch_contDiff F).of_le (by simp)).comp
        ((contDiff_id.prodMk contDiff_const).prodMk contDiff_const))
    exact (Complex.reCLM.contDiff.comp
      ((cutoff_flux_component_contDiff _ u hu a ha i 0).comp hr)).continuous
  have hscale (b : KPCuspCharts.Shape F) := integral_lift_scale volume μ hfd
    hAb.measure_lt_top.ne (fun z => f z b) (hfc b).aestronglyMeasurable
  simp_rw [hf] at hscale
  rw [hscale,hscale,hp]

private theorem bounded_setIntegral_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (A : Set H) (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (f : H → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : H) :
    HasDerivAt (fun r : ℝ => ∫ x in A, f (x + r • w) ∂μ)
      (∫ x in A, fderiv ℝ f x w ∂μ) 0 := by
  letI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hAb.measure_lt_top.ne
  have hc : IsCompact (closure A) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hAb.closure
  have hdc : Continuous (fun p : ℝ × H => fderiv ℝ f (p.2 + p.1 • w) w) :=
    ((hf.continuous_fderiv (by simp)).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply continuous_const
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn hdc.continuousOn
  have hfi : Integrable f (μ.restrict A) :=
    hf.continuous.continuousOn.integrableOn_compact hc |>.mono_set subset_closure
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict A) (x₀ := (0 : ℝ))
    (F := fun r x => f (x + r • w)) (F' := fun r x => fderiv ℝ f (x + r • w) w)
    (bound := fun _ => C) (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun r => (hf.continuous.comp (continuous_id.add (continuous_const (y := r • w)))).aestronglyMeasurable)
    (by simpa using hfi)
    (by simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const |>.aestronglyMeasurable)
    ?_ (integrable_const C) ?_
  · simpa using hi.2
  · filter_upwards [ae_restrict_mem hAm] with x hx
    intro r hr
    exact hC (r,x) ⟨hr,subset_closure hx⟩
  · apply Eventually.of_forall
    intro x r hr
    exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt r
      (by simpa using ((hasDerivAt_id r).smul_const w).const_add x)

private theorem periodic_setIntegral_translate_haar
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure]
    (K : AddSubgroup H) [Countable K]
    (A : Set H) (hAm : MeasurableSet A)
    (hA : ∀ x : H, ∃! k : K, x + k.val ∈ A)
    (f : H → ℝ) (hf : ∀ (k : K) x, f (x + k.val) = f x) (v : H) :
    (∫ x in A, f (x + v) ∂μ) = ∫ x in A, f x ∂μ := by
  have hd : IsAddFundamentalDomain K A μ := by
    apply IsAddFundamentalDomain.mk' hAm.nullMeasurableSet
    intro x
    change ∃! k : K, k.val + x ∈ A
    simpa [add_comm] using hA x
  let B := (fun x => x - v) ⁻¹' A
  have hd' : IsAddFundamentalDomain K B μ := by
    apply IsAddFundamentalDomain.mk'
    · exact (hAm.preimage (continuous_id.sub continuous_const).measurable).nullMeasurableSet
    · intro x
      change ∃! k : K, (k.val + x) - v ∈ A
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hA (x - v)
  have hm := measurePreserving_add_right μ v
  have hh := hm.setIntegral_preimage_emb (Homeomorph.addRight v).measurableEmbedding f B
  have he : (fun x => x + v) ⁻¹' B = A := by ext x; simp [B]
  rw [he] at hh
  refine hh.trans (hd'.setIntegral_eq hd ?_)
  intro k x
  change f (k.val + x) = f x
  simpa [add_comm] using hf k x

variable {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}

private theorem periodic_setIntegral_translate
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H] [(volume : Measure H).IsAddHaarMeasure] (K : AddSubgroup H) [Countable K]
    (A : Set H) (hAm : MeasurableSet A)
    (hA : ∀ x : H, ∃! k : K, x + k.val ∈ A)
    (f : H → ℂ) (hf : ∀ (k : K) x, f (x + k.val) = f x) (v : H) :
    (∫ x in A, f (x + v) ∂volume) = ∫ x in A, f x ∂volume := by
  have hd : IsAddFundamentalDomain K A volume := by
    apply IsAddFundamentalDomain.mk' hAm.nullMeasurableSet
    intro x
    change ∃! k : K, k.val + x ∈ A
    simpa [add_comm] using hA x
  let B := (fun x => x - v) ⁻¹' A
  have hd' : IsAddFundamentalDomain K B volume := by
    apply IsAddFundamentalDomain.mk'
    · exact (hAm.preimage (continuous_id.sub continuous_const).measurable).nullMeasurableSet
    · intro x
      change ∃! k : K, (k.val + x) - v ∈ A
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hA (x - v)
  have hm := measurePreserving_add_right (volume : Measure H) v
  have hh := hm.setIntegral_preimage_emb (Homeomorph.addRight v).measurableEmbedding f B
  have he : (fun x => x + v) ⁻¹' B = A := by ext x; simp [B]
  rw [he] at hh
  refine hh.trans (hd'.setIntegral_eq hd ?_)
  intro k x
  change f (k.val + x) = f x
  simpa [add_comm] using hf k x
private theorem periodic_setIntegral_fderiv_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasureSpace H] [BorelSpace H] [(volume : Measure H).IsAddHaarMeasure]
    (K : AddSubgroup H) [Countable K] (A : Set H) (hAm : MeasurableSet A)
    (hAb : Bornology.IsBounded A) (hA : ∀ x : H, ∃! k : K, x + k.val ∈ A)
    (f : H → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ (k : K) x, f (x + k.val) = f x) (w : H) :
    (∫ x in A, fderiv ℝ f x w ∂volume) = 0 := by
  letI : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAb.measure_lt_top.ne
  have hc : IsCompact (closure A) := Metric.isCompact_of_isClosed_isBounded isClosed_closure hAb.closure
  have hdc : Continuous (fun p : ℝ × H => fderiv ℝ f (p.2 + p.1 • w) w) :=
    ((hf.continuous_fderiv (by simp)).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply continuous_const
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn hdc.continuousOn
  have hfi : Integrable f (volume.restrict A) :=
    (hf.continuous.continuousOn.integrableOn_compact hc).mono_set (subset_closure)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict A) (x₀ := (0 : ℝ))
    (F := fun s x => f (x + s • w)) (F' := fun s x => fderiv ℝ f (x + s • w) w)
    (bound := fun _ => C) (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun s => (hf.continuous.comp (continuous_id.add (continuous_const (y := s • w)))).aestronglyMeasurable)
    (by simpa using hfi)
    (by simpa using ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
    ?_ (integrable_const C) ?_
  · have he : (fun s : ℝ => ∫ x in A, f (x + s • w)) = fun _ => ∫ x in A, f x := by
      funext s
      exact periodic_setIntegral_translate K A hAm hA f hp (s • w)
    have hz := (hasDerivAt_const (0 : ℝ) (∫ x in A, f x)).unique (he ▸ hi.2)
    simpa using hz.symm
  · filter_upwards [ae_restrict_mem hAm] with x hx
    intro s hs
    exact hC (s,x) ⟨hs, subset_closure hx⟩
  · apply Eventually.of_forall
    intro x s hs
    exact (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt s
      (by simpa using ((hasDerivAt_id s).smul_const w |>.const_add x))
 def horizontalShift {F : Type} [Field F] [NumberField F] (l : F) : Space (KPCuspLogShape.dimension F) :=
  real (KPCuspLogShape.dimension F) (fun i => (KPCuspCharts.embedding F l i, 0))
private theorem shift_arch {F : Type} [Field F] [NumberField F]
    (l : F) (q : Space (KPCuspLogShape.dimension F)) :
    arch (KPCuspLogShape.dimension F) (q + horizontalShift l) =
      fun i => ((arch (KPCuspLogShape.dimension F) q i).1 + KPCuspCharts.embedding F l i,
        (arch (KPCuspLogShape.dimension F) q i).2) := by
  ext i <;> simp [arch, horizontalShift, real, Complex.ext_iff]
private theorem u_horizontalShift_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) {T : ℝ}
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (l : D.L) (q : Space (KPCuspLogShape.dimension F))
    (hq : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (arch (KPCuspLogShape.dimension F) q)) :
    u (arch (KPCuspLogShape.dimension F) (q + horizontalShift l.val)) =
      u (arch (KPCuspLogShape.dimension F) q) := by
  let z := arch (KPCuspLogShape.dimension F) q
  let p := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).symm z
  have hp : T < p.2 := hq
  let p' : {p : KPCuspCharts.Coordinates F // T < p.2} := ⟨p, hp⟩
  let r' : {p : KPCuspCharts.Coordinates F // T < p.2} :=
    ⟨((p.1.1 + KPCuspCharts.embedding F l.val, p.1.2), p.2), hp⟩
  have he : KPCuspCharts.toArch F p = z := (KPCuspCharts.toArchHomeomorph F G.positive_dimension).apply_symm_apply z
  have hr : KPCuspCharts.highRelation F S T r' p' := by
    refine ⟨D.inclusion (Multiplicative.ofAdd l), ?_⟩
    change KPCuspSiegel.action F _ (KPCuspCharts.toArch F p) = _
    exact G.unipotent_action l p
  have hh := hinv r' p' hr
  rw [he] at hh
  rw [shift_arch]
  convert hh using 1
  congr 1
  ext i
  · have hei := congrFun he i
    simpa [KPCuspCharts.toArch, z, r'] using (congrArg Prod.fst hei).symm
  · have hei := congrFun he i
    simpa [KPCuspCharts.toArch, z, r'] using (congrArg Prod.snd hei).symm
private theorem cutoff_flux_horizontalShift_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) {T : ℝ}
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a)
    (l : D.L) (q : Space (KPCuspLogShape.dimension F)) (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    cutoffScalarFlux (KPCuspLogShape.dimension F) u a (q + horizontalShift l.val) i k =
      cutoffScalarFlux (KPCuspLogShape.dimension F) u a q i k := by
  let d := KPCuspLogShape.dimension F
  let m := fun q : Space d => KPCuspLogShape.meanHeight d (arch d q)
  have hm (r : Space d) : m (r + horizontalShift l.val) = m r := by
    simp [m, arch, horizontalShift, real, KPCuspLogShape.meanHeight]
  by_cases hq : m q ∈ tsupport a
  · have hmc : Continuous m := by
      unfold m KPCuspLogShape.meanHeight
      apply Continuous.div_const
      apply continuous_finset_sum
      intro j hj
      exact (EuclideanSpace.proj (𝕜 := ℝ) (j, (2 : Fin 3))).continuous
    have hn : ∀ᶠ r in 𝓝 q, T < m r :=
      (isOpen_lt continuous_const hmc).mem_nhds (ha.2.2 hq)
    have he : (fun r : Space d => (u (arch d (r + horizontalShift l.val)) : ℂ)) =ᶠ[𝓝 q]
        (fun r : Space d => (u (arch d r) : ℂ)) := by
      filter_upwards [hn] with r hr
      rw [u_horizontalShift_invariant G u hinv l r hr]
    have hd : fderiv ℝ (fun r => (u (arch d r) : ℂ)) (q + horizontalShift l.val) =
        fderiv ℝ (fun r => (u (arch d r) : ℂ)) q := by
      rw [← fderiv_comp_add_right (𝕜 := ℝ) (x := q) (horizontalShift l.val)]
      exact he.fderiv_eq
    have hv : (q + horizontalShift l.val) (i,2) = q (i,2) := by
      simp [horizontalShift, real]
    change (a (m (q + horizontalShift l.val)) : ℂ) * scalarDifferential d u (q + horizontalShift l.val) i k =
      (a (m q) : ℂ) * scalarDifferential d u q i k
    rw [hm]
    congr 1
    fin_cases k <;> simp [differential, scalarDifferential, coordinateDerivative, hd, hv]
  · change (a (m (q + horizontalShift l.val)) : ℂ) * _ = (a (m q) : ℂ) * _
    simp [hm, image_eq_zero_of_notMem_tsupport hq]
 def horizontalRealLinear (d : ℕ) : (Fin d → ℂ) →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap {
    toFun x := real d (fun i => (x i, 0))
    map_add' := by intro x y; ext ⟨i,k⟩; fin_cases k <;> simp [real]
    map_smul' := by intro r x; ext ⟨i,k⟩; fin_cases k <;> simp [real, Complex.real_smul] }
 def sliceOrigin {F : Type} [Field F] [NumberField F] (b : KPCuspCharts.Shape F) (t : ℝ) :=
  real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((0,b),t))
private theorem slice_real_eq {F : Type} [Field F] [NumberField F]
    (b : KPCuspCharts.Shape F) (t : ℝ) (x : KPCuspCharts.Horizontal F) :
    real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t)) =
      horizontalRealLinear (KPCuspLogShape.dimension F) x + sliceOrigin b t := by
  ext ⟨i,k⟩; fin_cases k <;> simp [real, KPCuspCharts.toArch, horizontalRealLinear, sliceOrigin]
private theorem horizontalRealLinear_coord (d : ℕ) (i : Fin d) (k : Fin 2) :
    horizontalRealLinear d (Pi.single i (if k = 0 then 1 else Complex.I)) =
      coordinateVector d i (k.castLE (by decide)) := by
  ext ⟨j,l⟩
  by_cases hj : j = i
  all_goals fin_cases k <;> fin_cases l <;>
    simp [horizontalRealLinear, real, coordinateVector, PiLp.toLp_apply, Pi.single_apply,
      PiLp.proj_apply, ← ite_and, and_comm, hj]
private theorem slice_coordinateDerivative_eq
    {F : Type} [Field F] [NumberField F]
    (f : Space (KPCuspLogShape.dimension F) → ℂ) (hf : Differentiable ℝ f)
    (b : KPCuspCharts.Shape F) (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 2) :
    fderiv ℝ (fun x => f (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t)))) x
      (Pi.single i (if k = 0 then 1 else Complex.I)) =
    coordinateDerivative (KPCuspLogShape.dimension F) i (k.castLE (by decide)) f
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t))) := by
  simp_rw [slice_real_eq]
  have hh := (hf _).hasFDerivAt.comp x
    (((horizontalRealLinear (KPCuspLogShape.dimension F)).hasFDerivAt).add_const (sliceOrigin b t))
  have hh' := hh.fderiv
  simp only [Function.comp_def] at hh'
  rw [hh']
  simp only [ContinuousLinearMap.comp_apply, horizontalRealLinear_coord, coordinateDerivative]
private theorem cutoff_flux_slice_periodic
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) {T : ℝ}
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (b : KPCuspCharts.Shape F) (t : ℝ)
    (l : D.L) (x : KPCuspCharts.Horizontal F) (i : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    cutoffScalarFlux (KPCuspLogShape.dimension F) u a
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x + KPCuspCharts.embedding F l.val,b),t))) i k =
    cutoffScalarFlux (KPCuspLogShape.dimension F) u a
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t))) i k := by
  have he : real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x + KPCuspCharts.embedding F l.val,b),t)) =
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t)) + horizontalShift l.val := by
    ext ⟨j,r⟩; fin_cases r <;> simp [real, KPCuspCharts.toArch, horizontalShift]
  rw [he]
  exact cutoff_flux_horizontalShift_invariant G u hinv a ha l _ i k

theorem cutoff_horizontalDivergence_integral_zero
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (A : Set (KPCuspCharts.Horizontal F))
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (b : KPCuspCharts.Shape F) :
    (∫ x in A, horizontalDivergence F
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) (x,b) t ∂volume) = 0 := by
  let d := KPCuspLogShape.dimension F
  let W := cutoffScalarFlux d u a
  let K := KPCuspCharts.translationLattice F D.L
  have hAK : ∀ x : KPCuspCharts.Horizontal F, ∃! k : K, x + k.val ∈ A := by
    intro x
    obtain ⟨l,hl,hlu⟩ := hA x
    refine ⟨⟨KPCuspCharts.embedding F l.val, ?_⟩,hl,?_⟩
    · exact ⟨l.val,l.property,rfl⟩
    · intro k hk
      obtain ⟨r,hr,he⟩ := k.property
      have hu' := hlu ⟨r,hr⟩ (by simpa [he] using hk)
      apply Subtype.ext
      simpa [he] using congrArg (fun l : D.L => KPCuspCharts.embedding F l.val) hu'
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable K := by
    have hh : Function.Surjective (fun l : D.L => (⟨KPCuspCharts.embedding F l.val, ⟨l.val,l.property,rfl⟩⟩ : K)) := by
      intro k
      obtain ⟨r,hr,he⟩ := k.property
      exact ⟨⟨r,hr⟩, Subtype.ext he⟩
    exact Function.Surjective.countable hh
  have hs (i : Fin d) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => W x i k) :=
    cutoff_flux_component_contDiff d u hu a ha i k
  have hp (i : Fin d) (k : Fin 3) (l : K) (x : KPCuspCharts.Horizontal F) :
      W (real d (KPCuspCharts.toArch F ((x + l.val,b),t))) i k =
      W (real d (KPCuspCharts.toArch F ((x,b),t))) i k := by
    obtain ⟨r,hr,he⟩ := l.property
    rw [← he]
    exact cutoff_flux_slice_periodic G u hinv a ha b t ⟨r,hr⟩ x i k
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspCharts.Horizontal F =>
      real d (KPCuspCharts.toArch F ((x,b),t))) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t)))
    simp_rw [slice_real_eq]
    exact (horizontalRealLinear d).contDiff.add contDiff_const
  have hz (i : Fin d) (k : Fin 2) :
      (∫ x in A, coordinateDerivative d i (k.castLE (by decide)) (fun q => W q i (if k = 0 then 1 else 2))
        (real d (KPCuspCharts.toArch F ((x,b),t)))) = 0 := by
    have hd' (x : KPCuspCharts.Horizontal F) := slice_coordinateDerivative_eq
      (fun q => W q i (if k = 0 then 1 else 2)) ((hs i _).differentiable (by simp)) b t x i k
    change (∫ x in A, coordinateDerivative (KPCuspLogShape.dimension F) i (k.castLE (by decide))
      (fun q => W q i (if k = 0 then 1 else 2))
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((x,b),t)))) = 0
    simp_rw [← hd']
    exact periodic_setIntegral_fderiv_zero K A hAm hAb hAK _ ((hs i _).comp hsc)
      (hp i _) (Pi.single i (if k = 0 then 1 else Complex.I))
  have hc (i : Fin d) (j k : Fin 3) : Continuous (fun x : KPCuspCharts.Horizontal F =>
      coordinateDerivative d i j (fun q => W q i k) (real d (KPCuspCharts.toArch F ((x,b),t)))) :=
    (((hs i k).continuous_fderiv (by simp)).clm_apply continuous_const).comp hsc.continuous
  have hint (i : Fin d) (j k : Fin 3) : IntegrableOn (fun x : KPCuspCharts.Horizontal F =>
      coordinateDerivative d i j (fun q => W q i k) (real d (KPCuspCharts.toArch F ((x,b),t)))) A :=
    ((hc i j k).continuousOn.integrableOn_compact
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hAb.closure)).mono_set subset_closure
  have hre (i : Fin d) (j k : Fin 3) : IntegrableOn (fun x : KPCuspCharts.Horizontal F =>
      (coordinateDerivative d i j (fun q => W q i k) (real d (KPCuspCharts.toArch F ((x,b),t)))).re) A :=
    (hint i j k).re
  have hz0 (i : Fin d) : (∫ x in A, (coordinateDerivative d i 0 (fun q => W q i 1)
      (real d (KPCuspCharts.toArch F ((x,b),t)))).re) = 0 := by
    rw [show (∫ x in A, (coordinateDerivative d i 0 (fun q => W q i 1) (real d (KPCuspCharts.toArch F ((x,b),t)))).re) =
      (∫ x in A, coordinateDerivative d i 0 (fun q => W q i 1) (real d (KPCuspCharts.toArch F ((x,b),t)))).re from
      Complex.reCLM.integral_comp_comm (hint i 0 1)]
    simpa using congrArg Complex.re (hz i 0)
  have hz1 (i : Fin d) : (∫ x in A, (coordinateDerivative d i 1 (fun q => W q i 2)
      (real d (KPCuspCharts.toArch F ((x,b),t)))).re) = 0 := by
    rw [show (∫ x in A, (coordinateDerivative d i 1 (fun q => W q i 2) (real d (KPCuspCharts.toArch F ((x,b),t)))).re) =
      (∫ x in A, coordinateDerivative d i 1 (fun q => W q i 2) (real d (KPCuspCharts.toArch F ((x,b),t)))).re from
      Complex.reCLM.integral_comp_comm (hint i 1 2)]
    simpa using congrArg Complex.re (hz i 1)
  have he : (fun x : KPCuspCharts.Horizontal F => horizontalDivergence F W (x,b) t) =
      fun x => ∑ i : Fin d, (Real.exp (t + b.val i) *
        (coordinateDerivative d i 0 (fun q => W q i 1) (real d (KPCuspCharts.toArch F ((x,b),t)))).re +
        Real.exp (t + b.val i) *
        (coordinateDerivative d i 1 (fun q => W q i 2) (real d (KPCuspCharts.toArch F ((x,b),t)))).re) := by
    funext x
    unfold horizontalDivergence
    dsimp only
    apply Finset.sum_congr rfl
    intro i hi
    have hheight : (real d (KPCuspCharts.toArch F ((x,b),t))) (i,2) = t + b.val i := by
      simp [real, KPCuspCharts.toArch]
    dsimp only [d] at hheight
    rw [hheight]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  change (∫ x in A, horizontalDivergence F W (x,b) t) = 0
  rw [he, integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_add ((hre i 0 1).const_mul _) ((hre i 1 2).const_mul _),
      integral_const_mul, integral_const_mul, hz0, hz1]
    simp
  · intro i hi
    exact ((hre i 0 1).const_mul _).add ((hre i 1 2).const_mul _)

theorem cutoff_verticalFlux_shape_direction_integral_zero
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (hB : ∀ b : KPCuspCharts.Shape F,
      ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits, b + v.val ∈ B)
    (i : Fin (KPCuspLogShape.dimension F)) (w : KPCuspCharts.Shape F) :
    (∫ c in A ×ˢ B, fderiv ℝ (fun c : KPCuspCharts.Cross F =>
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a
        (real _ (KPCuspCharts.toArch F (c,t))) i 0).re) c (0,w)
      ∂volume.prod G.shapeMeasure) = 0 := by
  let d := KPCuspLogShape.dimension F
  let k : KPCuspCharts.Cross F → ℝ := fun c =>
    (cutoffScalarFlux d u a (real d (KPCuspCharts.toArch F (c,t))) i 0).re
  have hkc : ContDiff ℝ (⊤ : ℕ∞) k :=
    Complex.reCLM.contDiff.comp ((cutoff_flux_component_contDiff d u hu a ha i 0).comp
      ((smooth_real d).comp (((KPCuspCharts.toArch_contDiff F).of_le (by simp)).comp
        (contDiff_id.prodMk contDiff_const))))
  letI := G.haar_shapeMeasure
  let K := (KPCuspLogShape.logLattice F hF D.E D.integralUnits).toAddSubgroup
  letI : DiscreteTopology K := KPCuspLogShape.logarithm_discrete F hF D.E D.integralUnits
  letI : Countable K := countable_of_Lindelof_of_discrete
  have hav (v : K) (b : KPCuspCharts.Shape F) :
      (∫ x in A, k (x,b + v.val)) = ∫ x in A, k (x,b) :=
    cutoff_verticalFlux_exact_domain_logLattice_periodic G u hu hinv a ha t A hAm hAb hA b v i
  have hb : Bornology.IsBounded (A ×ˢ B) := hAb.prod hBb
  let μ : Measure (KPCuspCharts.Cross F) := volume.prod G.shapeMeasure
  letI : IsFiniteMeasureOnCompacts μ := inferInstance
  have hd := bounded_setIntegral_hasDerivAt (volume.prod G.shapeMeasure) (A ×ˢ B)
    (hAm.prod hBm) hb k hkc (0,w)
  have he : (fun r : ℝ => ∫ c in A ×ˢ B, k (c + r • (0,w)) ∂volume.prod G.shapeMeasure) =
      fun _ => ∫ c in A ×ˢ B, k c ∂volume.prod G.shapeMeasure := by
    funext r
    have hc : IsCompact (closure (A ×ˢ B)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
    have hi (r : ℝ) : IntegrableOn (fun c => k (c + r • (0,w))) (A ×ˢ B) (volume.prod G.shapeMeasure) :=
      ((hkc.continuous.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact hc).mono_set subset_closure
    have hir := hi r
    rw [IntegrableOn, ← Measure.prod_restrict] at hir
    rw [← Measure.prod_restrict, integral_prod_symm _ hir]
    have hz := hi 0
    simp only [zero_smul,add_zero] at hz
    rw [IntegrableOn, ← Measure.prod_restrict] at hz
    rw [integral_prod_symm _ hz]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
    exact periodic_setIntegral_translate_haar G.shapeMeasure K B hBm hB
      (fun b => ∫ x in A, k (x,b)) hav (r • w)
  have hz := hd.unique (he ▸ hasDerivAt_const (0 : ℝ) (∫ c in A ×ˢ B, k c ∂volume.prod G.shapeMeasure))
  exact hz

theorem cutoff_shapeDivergence_rectangle_integral_zero
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) (t : ℝ)
    (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (hB : ∀ b : KPCuspCharts.Shape F,
      ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits, b + v.val ∈ B) :
    (∫ c in A ×ˢ B, shapeDivergence F
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) c t
      ∂volume.prod G.shapeMeasure) = 0 := by
  by_cases hd : KPCuspLogShape.dimension F ≤ 1
  · simp only [shapeDivergence_eq_zero_of_dimension_le_one hd, integral_zero]
  · let d := KPCuspLogShape.dimension F
    let W := cutoffScalarFlux d u a
    have hw (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => W q i 0) :=
      cutoff_flux_component_contDiff d u hu a ha i 0
    let k : Fin d → KPCuspCharts.Cross F → ℝ := fun i c =>
      (W (real d (KPCuspCharts.toArch F (c,t))) i 0).re
    have hk (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (k i) :=
      Complex.reCLM.contDiff.comp ((hw i).comp
        ((smooth_real d).comp (((KPCuspCharts.toArch_contDiff F).of_le (by simp)).comp
          (contDiff_id.prodMk contDiff_const))))
    have he (c : KPCuspCharts.Cross F) : shapeDivergence F W c t =
        ∑ i, fderiv ℝ (k i) c (0,projectedShapeDirection d G.positive_dimension i) := by
      rw [shapeDivergence_eq_sum_restricted_fderiv G.positive_dimension W
        (fun i => (hw i).differentiable (by simp))]
      apply Finset.sum_congr rfl
      intro i hi
      let g : KPCuspCharts.Cross F → ℂ := fun c => W (real d (KPCuspCharts.toArch F (c,t))) i 0
      have hg : Differentiable ℝ g := ((hw i).comp
        ((smooth_real d).comp (((KPCuspCharts.toArch_contDiff F).of_le (by simp)).comp
          (contDiff_id.prodMk contDiff_const)))).differentiable (by simp)
      have hb : HasFDerivAt (fun b : KPCuspCharts.Shape F => (c.1,b))
          (ContinuousLinearMap.inr ℝ (KPCuspCharts.Horizontal F) (KPCuspCharts.Shape F)) c.2 := by
        simpa using ((ContinuousLinearMap.inr ℝ (KPCuspCharts.Horizontal F) (KPCuspCharts.Shape F)).hasFDerivAt
          (x := c.2)).const_add (c.1,0)
      have h1 := (hg c).hasFDerivAt.comp c.2 hb
      have h2 := Complex.reCLM.hasFDerivAt.comp c (hg c).hasFDerivAt
      dsimp only [Function.comp_def] at h1 h2
      change HasFDerivAt (k i) (Complex.reCLM ∘L fderiv ℝ g c) c at h2
      rw [h1.fderiv, h2.fderiv]
      rfl
    letI := G.haar_shapeMeasure
    have hb : Bornology.IsBounded (A ×ˢ B) := hAb.prod hBb
    have hc : IsCompact (closure (A ×ˢ B)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
    have hint (i : Fin d) : IntegrableOn (fun c => fderiv ℝ (k i) c
        (0,projectedShapeDirection d G.positive_dimension i)) (A ×ˢ B) (volume.prod G.shapeMeasure) :=
      (((hk i).continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn.integrableOn_compact hc
        |>.mono_set subset_closure
    change (∫ c in A ×ˢ B, shapeDivergence F W c t ∂volume.prod G.shapeMeasure) = 0
    simp_rw [he]
    rw [integral_finset_sum Finset.univ (fun i hi => hint i)]
    apply Finset.sum_eq_zero
    intro i hi
    exact cutoff_verticalFlux_shape_direction_integral_zero G u hu hinv a ha t A B hAm hAb hBm hBb hA hB i
      (projectedShapeDirection d G.positive_dimension i)

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration.Slice

end
