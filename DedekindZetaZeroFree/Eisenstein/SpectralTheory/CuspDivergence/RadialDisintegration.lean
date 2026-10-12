module

public import DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingSmoothness
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.CompactRadialIntegrability
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.SliceIdentity

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical Topology Pointwise

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem slice_jet_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : E × ℝ → G) {T : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {p : E × ℝ | T < p.2})
    (c : E) {v : ℝ} (hv : T < v) (n : ℕ) :
    iteratedFDerivWithin ℝ n (fun t : ℝ => f (c, t)) (Set.Ioi T) v =
      (iteratedFDerivWithin ℝ n f {p : E × ℝ | T < p.2} (c, v)).compContinuousLinearMap
        (fun _ => (ContinuousLinearMap.inr ℝ E ℝ)) := by
  set U : Set (E × ℝ) := {p : E × ℝ | T < p.2} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_snd
  have hUuniq : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn
  have hincl : (ContinuousLinearMap.inr ℝ E ℝ) ⁻¹' U = Set.Ioi T := by
    ext t; simp [U, ContinuousLinearMap.inr_apply]
  have ha : (c, (0:ℝ)) +ᵥ U = U := by
    ext p
    simp only [U, Set.mem_setOf_eq, Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [vadd_eq_add] using hy
    · intro hp
      exact ⟨p - (c, (0:ℝ)), by simpa using hp, by simp [vadd_eq_add]⟩
  have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E × ℝ => f (z + (c, (0:ℝ)))) U :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (by
      intro z hz
      change z + (c, (0:ℝ)) ∈ U
      have h : z + (c, (0:ℝ)) = (c, (0:ℝ)) +ᵥ z := by simp [vadd_eq_add, add_comm]
      rw [h, ← ha]
      exact Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩)
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
      (ContinuousLinearMap.inr ℝ E ℝ) hshift hUuniq
      (by rw [hincl]; exact isOpen_Ioi.uniqueDiffOn)
      (x := v) (by simpa [U, ContinuousLinearMap.inr_apply] using hv) (i := n) (by simp)
  have hshift' : iteratedFDerivWithin ℝ n (fun z : E × ℝ => f (z + (c, (0:ℝ)))) U
      ((ContinuousLinearMap.inr ℝ E ℝ) v) =
      iteratedFDerivWithin ℝ n f U ((c, v)) := by
    rw [iteratedFDerivWithin_comp_add_right n (c, (0:ℝ)) ((ContinuousLinearMap.inr ℝ E ℝ) v)]
    simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero, ha]
  have hfun : (fun t : ℝ => f (c, t)) =
      ((fun z : E × ℝ => f (z + (c, (0:ℝ)))) ∘ (ContinuousLinearMap.inr ℝ E ℝ)) := by
    funext t; simp [ContinuousLinearMap.inr_apply]
  rw [hfun, ← hincl, hcomp, hshift']

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

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

 def chartLinear (F : Type) [Field F] [NumberField F] :
    KPCuspCharts.Coordinates F →L[ℝ] Space (KPCuspLogShape.dimension F) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => real _ (KPCuspCharts.toArch F p)
    map_add' := by
      intro p q
      ext ⟨i,k⟩
      fin_cases k <;> simp [real, KPCuspCharts.toArch] <;> ring
    map_smul' := by
      intro r p
      ext ⟨i,k⟩
      fin_cases k <;> simp [real, KPCuspCharts.toArch] <;> ring }

private theorem chartLinear_vertical (F : Type) [Field F] [NumberField F] :
    chartLinear F ((0,0),1) = ∑ i, coordinateVector (KPCuspLogShape.dimension F) i 2 := by
  ext ⟨i,k⟩
  fin_cases k <;> simp [chartLinear, real, KPCuspCharts.toArch, coordinateVector]

private theorem average_smooth_jets
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) {T : ℝ}
    (f : KPCuspCharts.Coordinates F → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {p | T < p.2})
    (hi : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q → f p.val = f q.val) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t => ∫ c, f (c,t) ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain))
      (Set.Ioi T) ∧
    ∀ n : ℕ, ∀ t ∈ Set.Ioi T,
      iteratedFDerivWithin ℝ n
        (fun t => ∫ c, f (c,t) ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain))
        (Set.Ioi T) t =
        ∫ c, iteratedFDerivWithin ℝ n (fun t => f (c,t)) (Set.Ioi T) t
          ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  let μ := (volume.prod G.shapeMeasure).restrict G.fundamentalDomain
  have hμ : IsFiniteMeasure μ := by
    letI := G.finite_sectionMeasure
    constructor
    have h := measure_lt_top G.sectionMeasure Set.univ
    rw [G.sectionMeasure_formula,
      Measure.map_apply measurable_quotient_mk'' MeasurableSet.univ] at h
    simpa [μ] using h
  letI := hμ
  let U : Set (KPCuspCharts.Coordinates F) := {p | T < p.2}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_snd
  let J (n : ℕ) (p : KPCuspCharts.Coordinates F) :=
    iteratedFDerivWithin ℝ n (fun t => f (p.1,t)) (Set.Ioi T) p.2
  have hJ (n : ℕ) : ContinuousOn (J n) U := by
    have hc := (ContinuousMultilinearMap.compContinuousLinearMapL (F := ℂ)
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ (KPCuspCharts.Cross F) ℝ)).continuous
    apply (hc.comp_continuousOn
      (ContinuousOn.continuousOn_iteratedFDerivWithin hf hU.uniqueDiffOn (by simp))).congr
    intro p hp
    exact slice_jet_eq (KPCuspCharts.Cross F) f hf p.1 hp n
  have hJi (n : ℕ) (p q : {p : KPCuspCharts.Coordinates F // T < p.2})
      (hpq : KPCuspCharts.highRelation F S T p q) : J n p.val = J n q.val := by
    have he : (Quotient.mk _ p : KPCuspCharts.HighQuotient F S T) =
        Quotient.mk _ q := Quotient.sound hpq
    have hh : ((Quotient.mk _ p.val.1 : KPCuspCharts.CrossQuotient F S), (⟨p.val.2,p.property⟩ : Set.Ioi T)) =
        (Quotient.mk _ q.val.1, (⟨q.val.2,q.property⟩ : Set.Ioi T)) := by
      apply (G.highPresentation T).injective
      simpa only [G.highPresentation_formula] using he
    have ht : p.val.2 = q.val.2 := congrArg (fun x => (x.2 : ℝ)) hh
    have hcross := congrArg Prod.fst hh
    dsimp only at hcross
    have heq : Set.EqOn (fun t => f (p.val.1,t)) (fun t => f (q.val.1,t)) (Set.Ioi T) := by
      intro t ht
      apply hi ⟨(p.val.1,t),ht⟩ ⟨(q.val.1,t),ht⟩
      apply Quotient.exact
      rw [← G.highPresentation_formula T p.val.1 ⟨t,ht⟩,
          ← G.highPresentation_formula T q.val.1 ⟨t,ht⟩, hcross]
    dsimp [J]
    rw [← ht]
    exact iteratedFDerivWithin_congr heq p.property n
  have hb (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioi T) :
      ∃ (s : Set ℝ) (b : KPCuspCharts.Cross F → ℝ),
        s ∈ nhds t ∧ s ⊆ Set.Ioi T ∧ Integrable b μ ∧
        ∀ᵐ c ∂μ, ∀ v ∈ s, ‖J n (c,v)‖ ≤ b c := by
    let K := Set.Icc ((T+t)/2) (t+1)
    have hK : IsCompact K := isCompact_Icc
    have hKT : K ⊆ Set.Ioi T := by intro v hv; dsimp [K] at hv; simp only [Set.mem_Ioi]; have htt : T < t := ht; linarith [hv.1]
    let d : KPCuspCharts.HighQuotient F S T → (ℝ [×n]→L[ℝ] ℂ) :=
      Quotient.lift (fun p => J n p.val) (hJi n)
    have hd : Continuous d := Continuous.quotient_lift ((hJ n).restrict) (hJi n)
    let j : K → Set.Ioi T := fun v => ⟨v.val, hKT v.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    let g : KPCuspCharts.CrossQuotient F S × K → (ℝ [×n]→L[ℝ] ℂ) :=
      fun p => d (G.highPresentation T (p.1,j p.2))
    have hg : Continuous g := hd.comp ((G.highPresentation T).continuous.comp
      (continuous_fst.prodMk (hj.comp continuous_snd)))
    letI := G.compact_cross
    letI := isCompact_iff_compactSpace.mp hK
    obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨K,fun _ => B, ?_, hKT, integrable_const B, Filter.Eventually.of_forall ?_⟩
    · apply Icc_mem_nhds <;> change _ < _ <;> have htt : T < t := ht <;> linarith
    · intro c v hv
      simpa [g,j,d, G.highPresentation_formula] using hB (Quotient.mk _ c,⟨v,hv⟩) (Set.mem_univ _)
  apply KPGlobalTorusBorelTwistCompatibilityBorelInduction.integral_contDiffOn_of_locally_dominated_jets
    μ (fun t c => f (c,t)) (Set.Ioi T) isOpen_Ioi
  · intro c
    exact hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ht)
  · intro n t ht
    have hc : Continuous (fun c => J n (c,t)) := by
      apply continuous_iff_continuousAt.mpr
      intro c
      exact ((hJ n).continuousAt (hU.mem_nhds ht)).comp
        (continuous_id.prodMk continuous_const).continuousAt
    exact hc.aestronglyMeasurable
  · exact hb

theorem scalar_differential_radialMean_contDiffOn
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (radialMean G (scalarDifferential (KPCuspLogShape.dimension F) u)) (Set.Ioi T) := by
  let d := KPCuspLogShape.dimension F
  let U : Set (KPCuspCharts.Coordinates F) := {p | T < p.2}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_snd
  let f : KPCuspCharts.Coordinates F → ℂ := fun p => (u (KPCuspCharts.toArch F p) : ℂ)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f U := by
    apply Complex.ofRealCLM.contDiff.contDiffOn.comp
      (hu.comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp)).contDiffOn ?_) (Set.mapsTo_univ _ _)
    intro p hp
    change T < KPCuspLogShape.meanHeight d (KPCuspCharts.toArch F p)
    rwa [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
  let e : KPCuspCharts.Coordinates F := ((0,0),1)
  let g : KPCuspCharts.Coordinates F → ℂ := fun p => fderivWithin ℝ f U p e / (d : ℂ)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g U :=
    ((hf.fderivWithin hU.uniqueDiffOn (by simp)).clm_apply contDiffOn_const).div_const _
  have hgi : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q → g p.val = g q.val := by
    intro p q hpq
    have he : (Quotient.mk _ p : KPCuspCharts.HighQuotient F S T) =
        Quotient.mk _ q := Quotient.sound hpq
    have hh : ((Quotient.mk _ p.val.1 : KPCuspCharts.CrossQuotient F S),
        (⟨p.val.2,p.property⟩ : Set.Ioi T)) =
        (Quotient.mk _ q.val.1, (⟨q.val.2,q.property⟩ : Set.Ioi T)) := by
      apply (G.highPresentation T).injective
      simpa only [G.highPresentation_formula] using he
    have ht : p.val.2 = q.val.2 := congrArg (fun x => (x.2 : ℝ)) hh
    have hcross := congrArg Prod.fst hh
    dsimp only at hcross
    have heq : Set.EqOn (fun t => f (p.val.1,t)) (fun t => f (q.val.1,t)) (Set.Ioi T) := by
      intro t ht
      apply congrArg (fun r : ℝ => (r : ℂ))
      apply hinv ⟨(p.val.1,t),ht⟩ ⟨(q.val.1,t),ht⟩
      apply Quotient.exact
      rw [← G.highPresentation_formula T p.val.1 ⟨t,ht⟩,
          ← G.highPresentation_formula T q.val.1 ⟨t,ht⟩, hcross]
    have hj := iteratedFDerivWithin_congr (𝕜 := ℝ) heq p.property 1
    rw [slice_jet_eq (KPCuspCharts.Cross F) f hf p.val.1 p.property 1,
        slice_jet_eq (KPCuspCharts.Cross F) f hf q.val.1 p.property 1] at hj
    have hv := congrArg (fun A : ℝ [×1]→L[ℝ] ℂ => A (fun _ => 1)) hj
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.inr_apply] at hv
    rw [iteratedFDerivWithin_one_apply (hU.uniqueDiffOn _ p.property),
        iteratedFDerivWithin_one_apply (hU.uniqueDiffOn (q.val.1,p.val.2) p.property)] at hv
    conv_rhs at hv => rw [ht]
    exact congrArg (fun z : ℂ => z / (d : ℂ)) hv
  have hgs := (average_smooth_jets G g hg hgi).1
  have hident : ∀ p ∈ U,
      g p = ((∑ i : Fin d, (scalarDifferential d u (real d (KPCuspCharts.toArch F p)) i 0).re) /
        (d : ℝ) : ℝ) := by
    intro p hp
    let x := real d (KPCuspCharts.toArch F p)
    let h : Space d → ℝ := fun y => u (arch d y)
    have hopen : IsOpen {z : KPArch.Space d | T < KPCuspLogShape.meanHeight d z} :=
      isOpen_lt continuous_const (smooth_mean d).continuous
    have hx : T < KPCuspLogShape.meanHeight d (arch d x) := by
      dsimp [x]
      rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact hp
    have hh : DifferentiableAt ℝ h x :=
      ((hu.contDiffAt (hopen.mem_nhds hx)).comp x (smooth_arch d).contDiffAt).differentiableAt (by simp)
    have hc : HasFDerivAt (fun y => (h y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ h x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x hh.hasFDerivAt
    have hchart : HasFDerivAt f
        ((Complex.ofRealCLM.comp (fderiv ℝ h x)).comp (chartLinear F)) p := by
      have hc' := hc.comp p (chartLinear F).hasFDerivAt
      convert hc' using 1
      funext y
      simp [f,h,chartLinear,d,arch_real]
    have he : chartLinear F e = ∑ i : Fin d, coordinateVector d i 2 := chartLinear_vertical F
    dsimp [g]
    rw [fderivWithin_of_isOpen hU hp, hchart.fderiv]
    simp only [ContinuousLinearMap.comp_apply, he, map_sum]
    have hcder : fderiv ℝ (fun q => (u (arch d q) : ℂ)) x =
        Complex.ofRealCLM.comp (fderiv ℝ h x) := hc.fderiv
    simp only [scalarDifferential, differential, Matrix.cons_val_zero, coordinateDerivative]
    change (∑ i : Fin d, Complex.ofRealCLM ((fderiv ℝ h x) (coordinateVector d i 2))) / (d : ℂ) =
      ↑((∑ i : Fin d, (fderiv ℝ (fun q => (u (arch d q) : ℂ)) x (coordinateVector d i 2)).re) / (d : ℝ))
    rw [hcder]
    simp [ContinuousLinearMap.comp_apply]
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t => (∫ c, g (c,t) ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)).re)
      (Set.Ioi T) := Complex.reCLM.contDiff.contDiffOn.comp hgs (Set.mapsTo_univ _ _)
  apply hsm.congr
  intro t ht
  have heq : (fun c => g (c,t)) = (fun c =>
      (((∑ i : Fin d, (scalarDifferential d u (real d (KPCuspCharts.toArch F (c,t))) i 0).re) /
        (d : ℝ) : ℝ) : ℂ)) := by funext c; exact hident (c,t) ht
  rw [heq, integral_complex_ofReal]
  rfl

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem contDiff_arch_for_realCoordinates (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem contDiff_meanHeight_for_realCoordinates (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem smooth_real (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (real d) := by
  apply (contDiff_piLp 2).mpr
  intro j
  rcases j with ⟨i, k⟩
  fin_cases k
  · simpa [real, Function.comp_def] using
      Complex.reCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using
      Complex.imCLM.contDiff.comp (contDiff_fst.comp (contDiff_apply ℝ KPArch.H3 i))
  · simpa [real, Function.comp_def] using contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

private theorem differential_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q => differential d g q i k) x := by
  have he : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Space d => (Real.exp (q (i,2)) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.contDiffAt.exp)
  fin_cases k
  · simpa [differential] using derivative_smoothAt d g x hg i 2
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 0)
  · simpa [differential] using he.mul (derivative_smoothAt d g x hg i 1)

private theorem contDiff_exp_coord (d : ℕ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space d => (Real.exp (p (i, 2)) : ℂ)) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.exp
  exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem continuous_codifferential (d : ℕ) (W : Space d → Cotangent d)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) : Continuous (codifferential d W) := by
  unfold codifferential
  apply continuous_finset_sum
  intro i _
  have h (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun p => W p i k) :=
    contDiff_pi.mp (contDiff_pi.mp hW i) k
  have hcd (k k' : Fin 3) : Continuous (coordinateDerivative d i k (fun q => W q i k')) := by
    unfold coordinateDerivative
    exact ((h k').continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have he := (contDiff_exp_coord d i).continuous
  exact (((hcd 2 0).neg.add (continuous_const.mul (h 0).continuous)).sub
    (he.mul (hcd 0 1))).sub (he.mul (hcd 1 2))

private theorem cutoffScalarFlux_smooth (d : ℕ) (u : KPArch.Space d → ℝ) {T : ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {z | T < KPCuspLogShape.meanHeight d z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffScalarFlux d u a) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : KPCuspLogShape.meanHeight d (arch d x) ∈ tsupport a
  · have hv : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => (u (arch d q) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((hu.contDiffAt ((isOpen_lt continuous_const (contDiff_meanHeight_for_realCoordinates d).continuous).mem_nhds
          (ha.2.2 hx))).comp x (contDiff_arch_for_realCoordinates d).contDiffAt)
    have hc : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : Space d => (a (KPCuspLogShape.meanHeight d (arch d x)) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        ((ha.1.comp ((contDiff_meanHeight_for_realCoordinates d).comp (contDiff_arch_for_realCoordinates d))).contDiffAt)
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro k
    simpa only [cutoffScalarFlux, scalarDifferential] using
      hc.mul (differential_smoothAt d _ x hv i k)
  · have hmhc : Continuous (fun q : Space d => KPCuspLogShape.meanHeight d (arch d q)) :=
      ((contDiff_meanHeight_for_realCoordinates d).comp (contDiff_arch_for_realCoordinates d)).continuous
    have hh := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hmhc.continuousAt
    have hWz : cutoffScalarFlux d u a =ᶠ[nhds x] 0 := by
      filter_upwards [hh] with q hq
      change a (KPCuspLogShape.meanHeight d (arch d q)) = 0 at hq
      funext i k
      simp [cutoffScalarFlux, scalarDifferential, hq]
    exact contDiffAt_const.congr_of_eventuallyEq hWz

private theorem chart_smooth {F : Type} [Field F] [NumberField F] :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
      real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p)) :=
  (smooth_real _).comp ((KPCuspCharts.toArch_contDiff F).of_le (by simp))

theorem cutoff_scalar_codifferential_continuous
    {F : Type} [Field F] [NumberField F]
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    Continuous (fun p : KPCuspCharts.Coordinates F =>
      (codifferential (KPCuspLogShape.dimension F)
        (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re) := by
  have hW : ContDiff ℝ (⊤ : ℕ∞) (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) :=
    cutoffScalarFlux_smooth _ u hu a ha
  have hcont : Continuous (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)) :=
    continuous_codifferential _ _ hW
  exact Complex.continuous_re.comp (hcont.comp chart_smooth.continuous)

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

private theorem arch_real_for_radialCutoff (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

private theorem contDiff_arch_for_radialCutoff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff

private theorem contDiff_meanHeight_for_radialCutoff (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (KPCuspLogShape.meanHeight d) := by
  unfold KPCuspLogShape.meanHeight
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i hi
  exact contDiff_snd.comp (contDiff_apply ℝ KPArch.H3 i)

private theorem codifferential_radial_mul_eq_zero_of_notMem_tsupport
    (d : ℕ) (a : ℝ → ℝ)
    (V : Space d → Cotangent d) (x : Space d)
    (hx : KPCuspLogShape.meanHeight d (arch d x) ∉ tsupport a) :
    codifferential d (fun q i k =>
      (a (KPCuspLogShape.meanHeight d (arch d q)) : ℂ) * V q i k) x = 0 := by
  have hh : Continuous (fun q : Space d => KPCuspLogShape.meanHeight d (arch d q)) :=
    (contDiff_meanHeight_for_radialCutoff d).continuous.comp (contDiff_arch_for_radialCutoff d).continuous
  have hn : (tsupport a)ᶜ ∈ 𝓝 (KPCuspLogShape.meanHeight d (arch d x)) :=
    (isClosed_tsupport a).isOpen_compl.mem_nhds hx
  have hw (i : Fin d) (k : Fin 3) :
      (fun q : Space d => (a (KPCuspLogShape.meanHeight d (arch d q)) : ℂ) * V q i k)
      =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hh.continuousAt.preimage_mem_nhds hn] with q hq
    simp [image_eq_zero_of_notMem_tsupport hq]
  have hc (i : Fin d) (j k : Fin 3) : coordinateDerivative d i j
      (fun q => (a (KPCuspLogShape.meanHeight d (arch d q)) : ℂ) * V q i k) x = 0 := by
    unfold coordinateDerivative
    rw [(hw i k).fderiv_eq]
    simp
  simp [codifferential, hc, image_eq_zero_of_notMem_tsupport hx]

theorem support_radial_codifferential_subset
    {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (a : ℝ → ℝ)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F)) :
    Function.support (fun p : KPCuspCharts.Coordinates F =>
      (codifferential (KPCuspLogShape.dimension F) (fun x i k =>
        (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (arch (KPCuspLogShape.dimension F) x)) : ℂ) * W x i k)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re) ⊆
      {p | p.2 ∈ tsupport a} := by
  intro p hp
  by_contra hx
  apply hp
  dsimp only
  rw [codifferential_radial_mul_eq_zero_of_notMem_tsupport]
  · rfl
  · simpa only [arch_real_for_radialCutoff, KPCuspCharts.toArch_meanHeight F hd, Set.mem_setOf_eq] using hx

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

theorem cutoff_scalar_codifferential_integrable
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
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    Integrable (fun p : KPCuspCharts.Coordinates F =>
      (codifferential (KPCuspLogShape.dimension F)
        (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re)
      (chartMeasure G) := by
  apply integrable_of_continuous_high_orbit_invariant G ha.2.1 ha.2.2
  · exact (cutoff_scalar_codifferential_continuous u hu a ha).continuousOn
  · exact support_radial_codifferential_subset G.positive_dimension a
      (scalarDifferential (KPCuspLogShape.dimension F) u)
  · intro p q hrel
    exact cutoff_scalar_codifferential_high_orbit_invariant G u hu hinv a ha p q hrel

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end

end

section

noncomputable section
open MeasureTheory Filter
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDescent
open KPMeanZeroWeightedEnergy HyperbolicChart

def radialMarginal
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (t : ℝ) : ℝ :=
  ∫ c : KPCuspCharts.Cross F,
    (∑ i : Fin (KPCuspLogShape.dimension F),
      (W (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t))) i 0).re) /
        (KPCuspLogShape.dimension F : ℝ)
    ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)

private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]

theorem radialMarginal_radial_mul
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → ℝ)
    (V : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (t : ℝ) :
    radialMarginal G (fun x i k =>
      (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) : ℂ) * V x i k) t =
      a t * radialMarginal G V t := by
  unfold radialMarginal
  simp only [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    ← Finset.mul_sum]
  simp_rw [mul_div_assoc]
  exact integral_const_mul _ _

theorem hasCompactSupport_radialMarginal_radial_mul
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → ℝ) (ha : HasCompactSupport a)
    (V : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F)) :
    HasCompactSupport (radialMarginal G (fun x i k =>
      (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) : ℂ) * V x i k)) := by
  apply ha.mono
  intro t ht
  change a t ≠ 0
  intro hz
  apply ht
  change radialMarginal G _ t = 0
  rw [radialMarginal_radial_mul, hz, zero_mul]

theorem radialMarginal_radial_mul_contDiff_of_contDiffOn
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (a : ℝ → ℝ) (ha : CompactRadialTest T a)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) (radialMarginal G W) (Set.Ioi T)) :
    ContDiff ℝ (⊤ : ℕ∞) (radialMarginal G (fun x i k =>
      (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) : ℂ) * W x i k)) := by
  have h : radialMarginal G (fun x i k =>
      (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) : ℂ) * W x i k) =
      a * radialMarginal G W := by
    funext t
    exact radialMarginal_radial_mul G a W t
  rw [h]
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t ∈ Set.Ioi T
  · exact (ha.1.contDiffAt).mul (hW.contDiffAt (isOpen_Ioi.mem_nhds ht))
  · have ht' : t ∉ tsupport a := fun hmem => ht (ha.2.2 hmem)
    have hz : a =ᶠ[nhds t] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp ht'
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with s hs
    change a s * radialMarginal G W s = 0
    rw [hs, zero_mul]

theorem integral_codifferential_eq_radial_of_slice_identity
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F))
    (hW : Integrable (fun p : KPCuspCharts.Coordinates F =>
      (codifferential (KPCuspLogShape.dimension F) W
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re)
      (KPMeanZeroWeightedEnergy.chartMeasure G))
    (hslice : ∀ᵐ t ∂KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F),
      (∫ c : KPCuspCharts.Cross F,
        (codifferential (KPCuspLogShape.dimension F) W
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (c, t)))).re
        ∂((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)) =
      -deriv (radialMarginal G W) t +
        2 * (KPCuspLogShape.dimension F : ℝ) * radialMarginal G W t) :
    (∫ p : KPCuspCharts.Coordinates F,
      (codifferential (KPCuspLogShape.dimension F) W
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
      ∂KPMeanZeroWeightedEnergy.chartMeasure G) =
    ∫ t, (-deriv (radialMarginal G W) t +
      2 * (KPCuspLogShape.dimension F : ℝ) * radialMarginal G W t)
      ∂KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F) := by
  letI := G.haar_shapeMeasure
  letI : SigmaFinite (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)) := by
    dsimp [KPCuspCharts.radialMeasure]
    infer_instance
  have hm : KPMeanZeroWeightedEnergy.chartMeasure G =
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain).prod
        (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)) := by
    rw [KPMeanZeroWeightedEnergy.chartMeasure, Measure.restrict_prod_eq_prod_univ]
    congr 1
    ext p
    simp
  rw [hm] at hW ⊢
  rw [integral_prod_symm _ hW]
  exact integral_congr_ae hslice

theorem scalar_flux_radial_disintegration
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
    (a : ℝ → ℝ) (ha : CompactRadialTest T a) :
    let W : Space (KPCuspLogShape.dimension F) → Cotangent (KPCuspLogShape.dimension F) :=
      fun x i k => (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) x)) : ℂ) *
        differential (KPCuspLogShape.dimension F)
          (fun q => (u (arch (KPCuspLogShape.dimension F) q) : ℂ)) x i k
    let J := radialMarginal G W
    ContDiff ℝ (⊤ : ℕ∞) J ∧ HasCompactSupport J ∧
      (∫ p : KPCuspCharts.Coordinates F,
        (codifferential (KPCuspLogShape.dimension F) W
          (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))).re
        ∂KPMeanZeroWeightedEnergy.chartMeasure G) =
      ∫ t, (-deriv J t + 2 * (KPCuspLogShape.dimension F : ℝ) * J t)
        ∂KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply radialMarginal_radial_mul_contDiff_of_contDiffOn G a ha
    exact ScalarFluxDisintegration.scalar_differential_radialMean_contDiffOn
      G u hu hinv
  · exact hasCompactSupport_radialMarginal_radial_mul G a ha.2.1 _
  · apply integral_codifferential_eq_radial_of_slice_identity G
    · exact ScalarFluxDisintegration.cutoff_scalar_codifferential_integrable
        G u hu hinv a ha
    · exact Filter.Eventually.of_forall
        (ScalarFluxDisintegration.cutoff_scalar_codifferential_slice G u hu hinv a ha)

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDescent

end

end
