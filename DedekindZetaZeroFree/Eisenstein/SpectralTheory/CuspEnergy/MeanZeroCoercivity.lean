module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.KernelTorus.PoincareInequality
public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.RadialProductPresentation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspCrossSections.FiberIntegralComparison
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.CompactRadialIntegrability

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

variable {F : Type} [Field F] [NumberField F]
private theorem rotation (L : ℂ →L[ℝ] ℂ) (u : ℂ) :
    ‖L u‖ ^ 2 + ‖L (u * Complex.I)‖ ^ 2 =
      ‖u‖ ^ 2 * (‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2) := by
  have h (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I := by
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
  rw [h u, h (u * Complex.I)]
  simp only [Complex.mul_I_re, Complex.mul_I_im]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im]
  ring

variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}
private theorem lift_eq (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (v : Representative ζ hζ S ρ V T) (b : KPCuspCharts.Shape F) (t : Set.Ioi T) :
    (fun y : KPCuspCharts.Horizontal F => v.torusSlice G H b t (QuotientAddGroup.mk y)) =
      (fun y => v.scalar ((y,b),t.val)) := by
  funext y
  have h := H.realization_formula (H.realization.symm (v.horizontalSlice G b t)) y
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h.symm
private theorem smooth_cross (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspCharts.Cross F => v.scalar (x,t.val)) := by
  apply v.smooth.comp_contDiff
  · have hh : ContDiff ℝ (⊤ : ℕ∞) (KPCuspCharts.toArch F) :=
      (KPCuspCharts.toArch_contDiff F).of_le (by simp)
    exact hh.comp (contDiff_id.prodMk contDiff_const)
  · intro x
    change T < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F (x,t.val))
    rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact t.property
private theorem slice_deriv (f : KPCuspCharts.Cross F → ℂ)
    (hf : Differentiable ℝ f) (y : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) :
    fderiv ℝ (fun z => f (z,b)) y =
      (fderiv ℝ f (y,b)).comp (ContinuousLinearMap.inl ℝ _ _) := by
  exact ((hf (y,b)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).prodMk (hasFDerivAt_const b y))).fderiv
private theorem continuous_energy (f : KPCuspCharts.Cross F → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    Continuous (fun x : KPCuspCharts.Cross F =>
      ∑ i, Real.exp (2 * (t + (x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
        (‖fderiv ℝ (fun z => f (z,x.2)) x.1 (Pi.single i 1)‖ ^ 2 +
         ‖fderiv ℝ (fun z => f (z,x.2)) x.1 (Pi.single i Complex.I)‖ ^ 2)) := by
  simp_rw [slice_deriv f (hf.differentiable (by simp))]
  apply continuous_finset_sum
  intro i hi
  apply Continuous.mul
  · exact Real.continuous_exp.comp (continuous_const.mul (continuous_const.add
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))))
  · exact (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2).add
      (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)

 def diagonal (a : KPCuspCharts.Horizontal F) :
    KPCuspCharts.Horizontal F →L[ℝ] KPCuspCharts.Horizontal F :=
  ContinuousLinearMap.pi (fun i => a i • ContinuousLinearMap.proj i)
private theorem diagonal_single (a : KPCuspCharts.Horizontal F)
    (i : Fin (KPCuspLogShape.dimension F)) (z : ℂ) :
    diagonal a (Pi.single i z) = Pi.single i (a i * z) := by
  ext j
  by_cases h : j = i
  · subst j; simp [diagonal]
  · simp [diagonal, Pi.single_eq_of_ne h]
private theorem transformed_deriv
    (f g : KPCuspCharts.Horizontal F → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a b y : KPCuspCharts.Horizontal F) (c : ℂ)
    (he : ∀ z, g (diagonal a z + b) = c * f z) :
    (fderiv ℝ g (diagonal a y + b)).comp (diagonal a) = c • fderiv ℝ f y := by
  have hd := (hg _).hasFDerivAt.comp y
    ((diagonal a).hasFDerivAt.add_const b)
  have hc := (hf y).hasFDerivAt.const_mul c
  have hh : (fun z => g (diagonal a z + b)) = (fun z => c * f z) := funext he
  change HasFDerivAt (fun z => g (diagonal a z + b)) _ y at hd
  rw [hh] at hd
  exact hd.unique hc
private theorem derivative_rotation
    (f g : KPCuspCharts.Horizontal F → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a b y : KPCuspCharts.Horizontal F) (c : ℂ)
    (hc : ‖c‖ = 1) (he : ∀ z, g (diagonal a z + b) = c * f z)
    (i : Fin (KPCuspLogShape.dimension F)) :
    ‖a i‖ ^ 2 *
      (‖fderiv ℝ g (diagonal a y + b) (Pi.single i 1)‖ ^ 2 +
       ‖fderiv ℝ g (diagonal a y + b) (Pi.single i Complex.I)‖ ^ 2) =
      ‖fderiv ℝ f y (Pi.single i 1)‖ ^ 2 +
       ‖fderiv ℝ f y (Pi.single i Complex.I)‖ ^ 2 := by
  let L := (fderiv ℝ g (diagonal a y + b)).comp (ContinuousLinearMap.single ℝ (fun _ => ℂ) i)
  have hh := rotation L (a i)
  have hd := transformed_deriv f g hf hg a b y c he
  have hz (z : ℂ) : fderiv ℝ g (diagonal a y + b) (Pi.single i (a i * z)) =
      c * fderiv ℝ f y (Pi.single i z) := by
    have h := congrArg (fun A : KPCuspCharts.Horizontal F →L[ℝ] ℂ => A (Pi.single i z)) hd
    simpa only [ContinuousLinearMap.comp_apply, diagonal_single,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using h
  dsimp [L] at hh
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply] at hh
  have hz1 := hz 1
  simp only [mul_one] at hz1
  rw [hz1, hz Complex.I, norm_mul, norm_mul, hc, one_mul, one_mul] at hh
  exact hh.symm

private theorem chi_norm (s : S) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)‖ = 1 := by
  apply IsOfFinOrder.norm_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by decide, ?_⟩
  have hp : (ρ s) ^ 3 = 1 := by
    apply Subtype.ext
    exact (mem_rootsOfUnity 3 _).mp (ρ s).property
  simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun u => (KPCuspGenuineMonodromy.chi F ζ hζ u : ℂ)) hp
private theorem invariant_energy
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T) (s : S)
    (x : KPCuspCharts.Cross F) :
    let en := fun x : KPCuspCharts.Cross F =>
      ∑ i, Real.exp (2 * (t.val + (x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
        (‖fderiv ℝ (fun z => v.scalar ((z,x.2),t.val)) x.1 (Pi.single i 1)‖ ^ 2 +
         ‖fderiv ℝ (fun z => v.scalar ((z,x.2),t.val)) x.1 (Pi.single i Complex.I)‖ ^ 2)
    en (G.crossAction s x) = en x := by
  obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
  rw [G.crossAction_formula s A hA hc]
  let a := KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F)
  let b := KPCuspCharts.embedding F (A 0 1 / A 1 1)
  let l := KPCuspLogShape.logarithm F hF D.E D.integralUnits (Additive.ofMul (D.ratio s))
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (ρ s)
  let f := fun z => v.scalar ((z,x.2),t.val)
  let g := fun z => v.scalar ((z,x.2 + l),t.val)
  have hf : Differentiable ℝ f :=
    ((smooth_cross G v t).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have hg : Differentiable ℝ g :=
    ((smooth_cross G v t).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have he : ∀ z, g (diagonal a z + b) = c * f z := by
    intro z
    have hh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspCharts.toArch F ((z,x.2),t.val)) := by
      rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact t.property
    have hh := v.equivariant s (KPCuspCharts.toArch F ((z,x.2),t.val)) hh
    rw [G.actual_action s A hA hc] at hh
    exact hh
  change (∑ i, Real.exp (2 * (t.val + ((x.2 + l : KPCuspCharts.Shape F) :
      Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
      (‖fderiv ℝ g (diagonal a x.1 + b) (Pi.single i 1)‖ ^ 2 +
       ‖fderiv ℝ g (diagonal a x.1 + b) (Pi.single i Complex.I)‖ ^ 2)) = _
  apply Finset.sum_congr rfl
  intro i hi
  have hn : ‖a i‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    exact (map_ne_zero (KPCusp.complexPlace F i).embedding).mpr (Units.ne_zero _)
  have hl : (l : Fin (KPCuspLogShape.dimension F) → ℝ) i = Real.log ‖a i‖ := by
    simp [l, a, KPCuspLogShape.logarithm, KPCuspLogShape.logRatio,
      KPCuspCharts.embedding, NumberField.InfinitePlace.norm_embedding_eq]
  have hw : Real.exp (2 * (t.val + ((x.2 + l : KPCuspCharts.Shape F) :
      Fin (KPCuspLogShape.dimension F) → ℝ) i)) =
      Real.exp (2 * (t.val + (x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)) * ‖a i‖ ^ 2 := by
    change Real.exp (2 * (t.val + ((x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
      (l : Fin (KPCuspLogShape.dimension F) → ℝ) i))) = _
    rw [hl, show 2 * (t.val + ((x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i +
      Real.log ‖a i‖)) = 2 * (t.val + (x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i) +
      (Real.log ‖a i‖ + Real.log ‖a i‖) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (lt_of_le_of_ne (norm_nonneg _) hn.symm), sq]
  rw [hw, mul_assoc, derivative_rotation f g hf hg a b x.1 c (chi_norm s) he i]

theorem horizontal_energy_continuous_invariant
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T) :
    let energy : KPCuspCharts.Cross F → ℝ := fun x =>
      torusHorizontalSq S D ρ x.2 t.val (v.torusSlice G H x.2 t)
        (QuotientAddGroup.mk x.1)
    Continuous energy ∧ ∀ (s : S) (x : KPCuspCharts.Cross F),
      energy (G.crossAction s x) = energy x := by
  dsimp only
  have heq (x : KPCuspCharts.Cross F) :
      torusHorizontalSq S D ρ x.2 t.val (v.torusSlice G H x.2 t)
          (QuotientAddGroup.mk x.1) =
      ∑ i, Real.exp (2 * (t.val + (x.2 : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
        (‖fderiv ℝ (fun z => v.scalar ((z,x.2),t.val)) x.1 (Pi.single i 1)‖ ^ 2 +
         ‖fderiv ℝ (fun z => v.scalar ((z,x.2),t.val)) x.1 (Pi.single i Complex.I)‖ ^ 2) := by
    rw [torusHorizontalSq_mk, lift_eq]
  simp_rw [heq]
  exact ⟨continuous_energy _ (smooth_cross G v t) t.val, invariant_energy G v t⟩

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
  {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
  {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

def mulHom (s : S) : KPCuspCharts.Horizontal F →+ KPCuspCharts.Horizontal F where
  toFun y := fun i => KPCuspCharts.embedding F ((D.ratio s : Fˣ) : F) i * y i
  map_zero' := by funext i; simp
  map_add' y z := by funext i; simp [mul_add]

private theorem kernel_borel (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) :
    BorelSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) := by
  obtain ⟨hd, hf⟩ := G.lattice
  letI := hd
  have hle : KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) ≤
      KPCuspCharts.translationLattice F D.L := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, H.kernel_le hx, rfl⟩
  letI : DiscreteTopology (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)) :=
    DiscreteTopology.of_subset hd hle
  letI : IsClosed (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ) : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  exact AddCosetSpace.borelSpace
private theorem monodromy_preserving (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ) (s : S) :
    MeasurePreserving (H.monodromy s) μ μ := by
  letI := kernel_borel G H
  letI := H.compact
  letI := hμ
  letI := hprob
  let M := H.monodromy s
  let e : KPCuspGenuineMonodromy.KernelTorus S D ρ ≃ₜ
      KPCuspGenuineMonodromy.KernelTorus S D ρ :=
    M.trans (Homeomorph.addRight (- M 0))
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
        change M (QuotientAddGroup.mk x + QuotientAddGroup.mk y) + - M 0 =
          (M (QuotientAddGroup.mk x) + - M 0) + (M (QuotientAddGroup.mk y) + - M 0)
        simp only [← sub_eq_add_neg]
        rw [← QuotientAddGroup.mk_add]
        have hz : (0 : KPCuspGenuineMonodromy.KernelTorus S D ρ) = QuotientAddGroup.mk (0 : KPCuspCharts.Horizontal F) := rfl
        simp only [M, hz, H.monodromy_formula s A _ hA hc]
        simp only [Pi.zero_apply, mul_zero, zero_add]
        rw [← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub,
          ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_add]
        congr 1
        ext i
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
  let a : KPCuspGenuineMonodromy.KernelTorus S D ρ ≃ₜ+
      KPCuspGenuineMonodromy.KernelTorus S D ρ :=
    ⟨{ e.toEquiv with map_add' := hadd }, e.continuous, e.symm.continuous⟩
  letI : (μ.map a).IsAddHaarMeasure := a.isAddHaarMeasure_map μ
  letI : IsProbabilityMeasure (μ.map a) := (Measure.isProbabilityMeasure_map_iff a.continuous.measurable.aemeasurable).mpr hprob
  have ha : MeasurePreserving a μ μ :=
    ⟨a.continuous.measurable, Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
  have hp := (measurePreserving_add_right μ (M 0)).comp ha
  convert hp using 1
  ext z
  change M z = (M z + - M 0) + M 0
  abel
private theorem slice_mk {T : ℝ} (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (v : Representative ζ hζ S ρ V T) (b : KPCuspCharts.Shape F)
    (t : Set.Ioi T) (y : KPCuspCharts.Horizontal F) :
    v.torusSlice G H b t (QuotientAddGroup.mk y) = v.scalar ((y,b),t.val) := by
  have h := H.realization_formula (H.realization.symm (v.horizontalSlice G b t)) y
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h.symm

private theorem scalar_norm_action {T : ℝ} (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T)
    (s : S) (x : KPCuspCharts.Cross F) :
    ‖v.scalar (G.crossAction s x, t.val)‖ = ‖v.scalar (x, t.val)‖ := by
  obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
  rw [G.crossAction_formula s A hA hc]
  have hh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (KPCuspCharts.toArch F (x, t.val)) := by
    rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact t.property
  have he := v.equivariant s (KPCuspCharts.toArch F (x, t.val)) hh
  rw [G.actual_action s A hA hc] at he
  change v.scalar (KPCuspCharts.crossAffine F hF D.E D.integralUnits
      (D.ratio s) (A 0 1 / A 1 1) x, t.val) =
    (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar (x, t.val) at he
  have hu : ‖(KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    have hp : (ρ s) ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (ρ s).property
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u => (KPCuspGenuineMonodromy.chi F ζ hζ u : ℂ)) hp
  rw [he, norm_mul, hu, one_mul]

theorem slice_coercivity_transport
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (B : Set (KPCuspCharts.Shape F))
    (hcover : ∀ b : KPCuspCharts.Shape F, ∃ b' ∈ B,
      (QuotientAddGroup.mk b : KPCuspCharts.Base F hF D.E D.integralUnits) =
        QuotientAddGroup.mk b')
    (v : Representative ζ hζ S ρ V T) (c : ℝ)
    (hslice : ∀ b ∈ B, ∀ t : Set.Ioi T,
      (c * Real.exp (2 * t.val)) *
          (∫ z, ‖v.torusSlice G H b t z‖ ^ 2 ∂μ) ≤
        (∫ z, torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) z ∂μ)) :
    ∀ (b : KPCuspCharts.Shape F) (t : Set.Ioi T),
      (c * Real.exp (2 * t.val)) *
          (∫ z, ‖v.torusSlice G H b t z‖ ^ 2 ∂μ) ≤
        (∫ z, torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) z ∂μ) := by
  intro b t
  obtain ⟨b', hb', hbb'⟩ := hcover b
  have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hbb'
  change b - b' ∈ (KPCuspLogShape.logarithm F hF D.E D.integralUnits).range at hmem
  obtain ⟨u, hu⟩ := hmem
  obtain ⟨s, hs⟩ := D.surjective u.toMul
  have hshape : b' + KPCuspLogShape.logarithm F hF D.E D.integralUnits
      (Additive.ofMul (D.ratio s)) = b := by
    rw [hs]
    change b' + KPCuspLogShape.logarithm F hF D.E D.integralUnits u = b
    rw [hu]
    abel
  have hcross (y : KPCuspCharts.Horizontal F) :
      (QuotientAddGroup.mk (G.crossAction s (y,b')).1,
        (G.crossAction s (y,b')).2) = (H.monodromy s (QuotientAddGroup.mk y), b) := by
    obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
    rw [G.crossAction_formula s A hA hc]
    simp only [KPCuspCharts.crossAffine, KPCuspCharts.affine, hshape, H.monodromy_formula s A _ hA hc]
  have hm : ∀ z, ‖v.torusSlice G H b t (H.monodromy s z)‖ ^ 2 =
      ‖v.torusSlice G H b' t z‖ ^ 2 := by
    intro z
    induction z using Quotient.inductionOn with
    | h y =>
      have h := congrArg (fun p => ‖v.torusSlice G H p.2 t p.1‖ ^ 2) (hcross y)
      rw [← h]
      simp only [slice_mk]
      rw [scalar_norm_action G v t s (y,b')]
  have he : ∀ z, torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) (H.monodromy s z) =
      torusHorizontalSq S D ρ b' t.val (v.torusSlice G H b' t) z := by
    intro z
    induction z using Quotient.inductionOn with
    | h y =>
      have h := congrArg (fun p => torusHorizontalSq S D ρ p.2 t.val
        (v.torusSlice G H p.2 t) p.1) (hcross y)
      rw [← h]
      exact (horizontal_energy_continuous_invariant G H v t).2 s (y,b')
  letI := kernel_borel G H
  have hp := monodromy_preserving G H μ hμ hprob s
  have im := hp.integral_comp (H.monodromy s).toMeasurableEquiv.measurableEmbedding
    (fun z => ‖v.torusSlice G H b t z‖ ^ 2)
  have ie := hp.integral_comp (H.monodromy s).toMeasurableEquiv.measurableEmbedding
    (fun z => torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) z)
  simp_rw [hm] at im
  simp_rw [he] at ie
  rw [← im, ← ie]
  exact hslice b' hb' t

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

theorem gradientSq_cross_section_integrable
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T) :
    Integrable (fun x : KPCuspCharts.Cross F => v.gradientSq (x, t.val))
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  have hgeom := KPCompactGreenRadialIntegrability.gradientSq_continuousOn_and_invariant G v
  have hcont : Continuous (fun x : KPCuspCharts.Cross F => v.gradientSq (x, t.val)) :=
    hgeom.1.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => t.property)
  have hinv : ∀ x y : KPCuspCharts.Cross F, KPCuspCharts.crossRelation F S x y →
      v.gradientSq (x, t.val) = v.gradientSq (y, t.val) := by
    intro x y hxy
    exact hgeom.2 ⟨(x, t.val), t.property⟩ ⟨(y, t.val), t.property⟩
      ((KPCuspCharts.highRelation_product F hF S D T _ _).mpr ⟨hxy, rfl⟩)
  let energy : KPCuspCharts.CrossQuotient F S → ℝ :=
    Quotient.lift (fun x => v.gradientSq (x, t.val)) hinv
  have hecont : Continuous energy := hcont.quotient_lift hinv
  letI := G.compact_cross
  letI : IsFiniteMeasure G.sectionMeasure := G.finite_sectionMeasure
  have hmap : IsFiniteMeasure (Measure.map (Quotient.mk (KPCuspCharts.crossRelation F S))
      ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain)) := by
    rw [← G.sectionMeasure_formula]
    infer_instance
  letI := hmap
  letI : IsFiniteMeasure ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) :=
    Measure.isFiniteMeasure_of_map
      (f := Quotient.mk (KPCuspCharts.crossRelation F S))
      measurable_quotient_mk''.aemeasurable
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hecont.continuousOn
  refine ⟨hcont.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C) ?_⟩
  exact Filter.Eventually.of_forall fun x =>
    hC (Quotient.mk (KPCuspCharts.crossRelation F S) x) (Set.mem_univ _)

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
  {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
  {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
  {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ} {T : ℝ}

theorem gradientSq_nonneg (v : Representative ζ hζ S ρ V T)
    (p : KPCuspCharts.Coordinates F) : 0 ≤ v.gradientSq p := by
  unfold Representative.gradientSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _

theorem cross_section_coercivity_zero (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T) :
    ((0 : ℝ) * Real.exp (2 * t.val)) *
      (∫ x : KPCuspCharts.Cross F, ‖v.scalar (x, t.val)‖ ^ 2
        ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ≤
      (∫ x : KPCuspCharts.Cross F, v.gradientSq (x, t.val)
        ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  simp only [zero_mul]
  exact integral_nonneg fun x => gradientSq_nonneg v (x, t.val)

theorem scalar_norm_crossAffine
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T)
    (s : S) (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A = (s : KPCuspArithmetic.PGL2 F))
    (hc : A 1 0 = 0) (x : KPCuspCharts.Cross F) :
    ‖v.scalar (KPCuspCharts.crossAffine F hF D.E D.integralUnits
      (D.ratio s) (A 0 1 / A 1 1) x, t.val)‖ = ‖v.scalar (x, t.val)‖ := by
  have hh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (KPCuspCharts.toArch F (x, t.val)) := by
    rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact t.property
  have he := v.equivariant s (KPCuspCharts.toArch F (x, t.val)) hh
  rw [G.actual_action s A hA hc] at he
  change v.scalar (KPCuspCharts.crossAffine F hF D.E D.integralUnits
      (D.ratio s) (A 0 1 / A 1 1) x, t.val) =
    (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * v.scalar (x, t.val) at he
  have hu : ‖(KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ)‖ = 1 := by
    apply IsOfFinOrder.norm_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨3, by decide, ?_⟩
    have hp : (ρ s) ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 _).mp (ρ s).property
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u => (KPCuspGenuineMonodromy.chi F ζ hζ u : ℂ)) hp
  rw [he, norm_mul, hu, one_mul]

theorem scalar_norm_crossAction
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T)
    (s : S) (x : KPCuspCharts.Cross F) :
    ‖v.scalar (G.crossAction s x, t.val)‖ = ‖v.scalar (x, t.val)‖ := by
  obtain ⟨A, hA, hc⟩ := D.upper s.val s.property
  rw [G.crossAction_formula s A hA hc]
  exact scalar_norm_crossAffine G v t s A hA hc x

theorem scalar_slice_continuous
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (t : Set.Ioi T) :
    Continuous (fun x : KPCuspCharts.Cross F => v.scalar (x, t.val)) := by
  have hx : Continuous (fun x : KPCuspCharts.Cross F => KPCuspCharts.toArch F (x, t.val)) :=
    (KPCuspCharts.toArch_contDiff F).continuous.comp (continuous_id.prodMk continuous_const)
  exact v.smooth.continuousOn.comp_continuous hx (fun x => by
    change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (KPCuspCharts.toArch F (x, t.val))
    rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact t.property)

 def horizontalRealLinear (d : ℕ) : (Fin d → ℂ) →L[ℝ] HyperbolicChart.Space d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d × Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j =>
      if j.2 = 0 then Complex.reCLM.comp (ContinuousLinearMap.proj j.1)
      else if j.2 = 1 then Complex.imCLM.comp (ContinuousLinearMap.proj j.1)
      else 0))
private theorem horizontalRealLinear_apply (d : ℕ) (y : Fin d → ℂ) (j : Fin d × Fin 3) :
    horizontalRealLinear d y j = if j.2 = 0 then (y j.1).re else
      if j.2 = 1 then (y j.1).im else 0 := by
  change (if j.2 = 0 then Complex.reCLM.comp (ContinuousLinearMap.proj j.1)
      else if j.2 = 1 then Complex.imCLM.comp (ContinuousLinearMap.proj j.1)
      else (0 : (Fin d → ℂ) →L[ℝ] ℝ)) y = _
  split_ifs <;> rfl

private theorem horizontalRealLinear_single_one (d : ℕ) (i : Fin d) :
    horizontalRealLinear d (Pi.single i 1) = HyperbolicChart.coordinateVector d i 0 := by
  ext ⟨j, k⟩
  simp only [horizontalRealLinear_apply, HyperbolicChart.coordinateVector,
    PiLp.toLp_apply]
  by_cases hi : j = i
  · subst i
    fin_cases k <;> simp
  · fin_cases k <;> simp [Pi.single_eq_of_ne hi, hi, Prod.ext_iff]
private theorem horizontalRealLinear_single_I (d : ℕ) (i : Fin d) :
    horizontalRealLinear d (Pi.single i Complex.I) = HyperbolicChart.coordinateVector d i 1 := by
  ext ⟨j, k⟩
  simp only [horizontalRealLinear_apply, HyperbolicChart.coordinateVector,
    PiLp.toLp_apply]
  by_cases hi : j = i
  · subst i
    fin_cases k <;> simp
  · fin_cases k <;> simp [Pi.single_eq_of_ne hi, hi, Prod.ext_iff]

private theorem smooth_arch (d : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (arch d) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · exact Complex.equivRealProdCLM.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (0 : Fin 3))).contDiff.prodMk
       (EuclideanSpace.proj (𝕜 := ℝ) (i, (1 : Fin 3))).contDiff)
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff
private theorem arch_real (d : ℕ) (z : KPArch.Space d) : arch d (real d z) = z := by
  ext i <;> simp [arch, real]
private theorem representative_differentiableAt (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (x : KPCuspCharts.Cross F) (t : Set.Ioi T) :
    DifferentiableAt ℝ (v.val ∘ arch (KPCuspLogShape.dimension F))
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (x, t.val))) := by
  have hh : Continuous (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)) := by
    unfold KPCuspLogShape.meanHeight
    exact (continuous_finset_sum _ (fun i _ => (continuous_apply i).snd)).div_const _
  have ho : IsOpen {z : KPArch.Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z} :=
    isOpen_lt continuous_const hh
  have hp : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F)
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F (x, t.val)))) := by
    rw [arch_real, KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact t.property
  exact ((v.smooth.contDiffAt (ho.mem_nhds hp)).comp _
    (smooth_arch _).contDiffAt).differentiableAt (by simp)

private theorem horizontal_real_deriv (b : KPCuspCharts.Shape F) (t : ℝ)
    (y : KPCuspCharts.Horizontal F) :
    HasFDerivAt (fun z : KPCuspCharts.Horizontal F => real (KPCuspLogShape.dimension F)
      (KPCuspCharts.toArch F ((z,b),t))) (horizontalRealLinear (KPCuspLogShape.dimension F)) y := by
  have he : (fun z : KPCuspCharts.Horizontal F => real (KPCuspLogShape.dimension F)
      (KPCuspCharts.toArch F ((z,b),t))) =
      fun z => horizontalRealLinear (KPCuspLogShape.dimension F) z +
        real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((0,b),t)) := by
    funext z
    ext ⟨i,k⟩
    fin_cases k <;> simp [real, KPCuspCharts.toArch, horizontalRealLinear_apply]
  rw [he]
  exact (horizontalRealLinear _).hasFDerivAt.add_const _

private theorem scalar_slice_fderiv (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (b : KPCuspCharts.Shape F)
    (t : Set.Ioi T) (y : KPCuspCharts.Horizontal F) :
    fderiv ℝ (fun z : KPCuspCharts.Horizontal F => v.scalar ((z,b),t.val)) y =
      (fderiv ℝ (v.val ∘ arch (KPCuspLogShape.dimension F))
        (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((y,b),t.val)))).comp
          (horizontalRealLinear (KPCuspLogShape.dimension F)) := by
  have he : (fun z : KPCuspCharts.Horizontal F => v.scalar ((z,b),t.val)) =
      (v.val ∘ arch (KPCuspLogShape.dimension F)) ∘
        (fun z => real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((z,b),t.val))) := by
    funext z
    simp [Function.comp_def, arch_real, Representative.scalar]
  rw [he]
  exact ((representative_differentiableAt G v (y,b) t).hasFDerivAt.comp y
    (horizontal_real_deriv b t.val y)).fderiv

theorem torusSlice_mk (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (v : Representative ζ hζ S ρ V T) (b : KPCuspCharts.Shape F)
    (t : Set.Ioi T) (y : KPCuspCharts.Horizontal F) :
    v.torusSlice G H b t (QuotientAddGroup.mk y) = v.scalar ((y,b),t.val) := by
  have h := H.realization_formula (H.realization.symm (v.horizontalSlice G b t)) y
  simp only [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem torusHorizontalSq_le_gradientSq (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (v : Representative ζ hζ S ρ V T) (b : KPCuspCharts.Shape F)
    (t : Set.Ioi T) (y : KPCuspCharts.Horizontal F) :
    torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) (QuotientAddGroup.mk y) ≤
      v.gradientSq ((y,b),t.val) := by
  rw [torusHorizontalSq_mk]
  have he : (fun z : KPCuspCharts.Horizontal F =>
      v.torusSlice G H b t (QuotientAddGroup.mk z)) =
      (fun z => v.scalar ((z,b),t.val)) := funext (torusSlice_mk G H v b t)
  rw [he, scalar_slice_fderiv G v b t y]
  simp only [ContinuousLinearMap.comp_apply, horizontalRealLinear_single_one,
    horizontalRealLinear_single_I]
  unfold Representative.gradientSq
  dsimp only
  apply Finset.sum_le_sum
  intro i hi
  simp only [Fin.sum_univ_three, HyperbolicChart.differential,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_def,
    Fin.succ_zero_eq_one, HyperbolicChart.coordinateDerivative, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  simp only [real, KPCuspCharts.toArch, PiLp.toLp_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [← Real.exp_nat_mul]
  simp only [Function.comp_def, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_two, Nat.cast_ofNat,
    Fin.succ_zero_eq_one]
  nlinarith [sq_nonneg (‖fderiv ℝ (v.val ∘ arch (KPCuspLogShape.dimension F))
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F ((y,b),t.val)))
      (HyperbolicChart.coordinateVector (KPCuspLogShape.dimension F) i 2)‖)]

theorem cross_section_coercivity
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (B : Set (KPCuspCharts.Shape F)) (hB : IsCompact B)
    (hcover : ∀ b : KPCuspCharts.Shape F, ∃ b' ∈ B,
      (QuotientAddGroup.mk b : KPCuspCharts.Base F hF D.E D.integralUnits) =
        QuotientAddGroup.mk b')
    (v : Representative ζ hζ S ρ V T) (c : ℝ) (hc : 0 ≤ c)
    (hslice : ∀ b ∈ B, ∀ t : Set.Ioi T,
      (c * Real.exp (2 * t.val)) *
          (∫ z, ‖v.torusSlice G H b t z‖ ^ 2 ∂μ) ≤
        (∫ z, torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) z ∂μ)) :
    ∀ t : Set.Ioi T,
      (c * Real.exp (2 * t.val)) *
          (∫ x : KPCuspCharts.Cross F, ‖v.scalar (x, t.val)‖ ^ 2
            ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ≤
        (∫ x : KPCuspCharts.Cross F, v.gradientSq (x, t.val)
          ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) := by
  intro t
  by_cases hzero : c = 0
  · subst c
    exact cross_section_coercivity_zero G v t
  let mass : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ :=
    fun z b => ‖v.torusSlice G H b t z‖ ^ 2
  let energy : KPCuspGenuineMonodromy.KernelTorus S D ρ → KPCuspCharts.Shape F → ℝ :=
    fun z b => torusHorizontalSq S D ρ b t.val (v.torusSlice G H b t) z
  have hm_cont : Continuous (fun x : KPCuspCharts.Cross F =>
      mass (QuotientAddGroup.mk x.1) x.2) := by
    simp only [mass, torusSlice_mk, Prod.eta]
    exact (scalar_slice_continuous G v t).norm.pow 2
  have hm_inv : ∀ (s : S) (x : KPCuspCharts.Cross F),
      mass (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        mass (QuotientAddGroup.mk x.1) x.2 := by
    intro s x
    simp only [mass, torusSlice_mk]
    exact congrArg (fun r : ℝ => r ^ 2) (scalar_norm_crossAction G v t s x)
  have he_data := CrossSection.horizontal_energy_continuous_invariant G H v t
  change Continuous (fun x : KPCuspCharts.Cross F =>
      energy (QuotientAddGroup.mk x.1) x.2) ∧
    (∀ (s : S) (x : KPCuspCharts.Cross F),
      energy (QuotientAddGroup.mk (G.crossAction s x).1) (G.crossAction s x).2 =
        energy (QuotientAddGroup.mk x.1) x.2) at he_data
  have hfiber := CrossSection.slice_coercivity_transport G H μ hμ hprob B
    hcover v c hslice
  have hcomp := CrossSection.invariant_fiber_integral_comparison G μ hμ hprob
    mass energy hm_cont he_data.1 hm_inv he_data.2 (c * Real.exp (2 * t.val))
      (fun b => hfiber b t)
  have hg := CrossSection.gradientSq_cross_section_integrable G v t
  have hle : ∀ x : KPCuspCharts.Cross F,
      energy (QuotientAddGroup.mk x.1) x.2 ≤ v.gradientSq (x, t.val) := by
    intro x
    exact torusHorizontalSq_le_gradientSq G H v x.2 t x.1
  have he_nonneg : ∀ x : KPCuspCharts.Cross F,
      0 ≤ energy (QuotientAddGroup.mk x.1) x.2 := by
    intro x
    exact torusHorizontalSq_nonneg S D ρ x.2 t.val (v.torusSlice G H x.2 t) _
  have he_int : Integrable (fun x : KPCuspCharts.Cross F =>
      energy (QuotientAddGroup.mk x.1) x.2)
        ((volume.prod G.shapeMeasure).restrict G.fundamentalDomain) :=
    hg.mono_nonneg he_data.1.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall he_nonneg) (Filter.Eventually.of_forall hle)
  have hdom := integral_mono he_int hg hle
  simp only [mass, torusSlice_mk] at hcomp
  exact hcomp.trans hdom

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

theorem smooth_periodic_slice
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (v : Representative ζ hζ S ρ V T)
    (b : KPCuspCharts.Shape F) (t : Set.Ioi T) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : KPCuspCharts.Horizontal F =>
      v.torusSlice G H b t (QuotientAddGroup.mk y)) := by

  have hpt : ∀ y, v.torusSlice G H b t (QuotientAddGroup.mk y) =
      v.val (KPCuspCharts.toArch F ((y, b), t.val)) := by
    intro y
    have h := H.realization_formula (H.realization.symm (v.horizontalSlice G b t)) y
    simp only [LinearEquiv.apply_symm_apply] at h
    show (H.realization.symm (v.horizontalSlice G b t)).val (QuotientAddGroup.mk y) =
      v.val (KPCuspCharts.toArch F ((y, b), t.val))
    rw [← h]
    rfl
  rw [show (fun y : KPCuspCharts.Horizontal F =>
        v.torusSlice G H b t (QuotientAddGroup.mk y)) =
      (v.val ∘ fun y : KPCuspCharts.Horizontal F =>
        KPCuspCharts.toArch F ((y, b), t.val)) from funext hpt]

  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : KPCuspCharts.Horizontal F =>
      KPCuspCharts.toArch F ((y, b), t.val)) := by
    rw [contDiff_pi]
    intro i
    simp only [KPCuspCharts.toArch]
    fun_prop

  have hs : ∀ y : KPCuspCharts.Horizontal F,
      KPCuspCharts.toArch F ((y, b), t.val) ∈
        {x | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x} := by
    intro y
    simp only [Set.mem_setOf_eq]
    rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
    exact t.property
  exact v.smooth.comp_contDiff hf hs

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

theorem integrate_cross_section_coercivity
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)}
    {D : KPCuspCharts.ParabolicData F S} {ρ : S →* rootsOfUnity 3 F}
    {V : Submodule ℂ ℂ} {T : ℝ}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (v : Representative ζ hζ S ρ V T) (c : ℝ) (hc : 0 ≤ c)
    (hcross : ∀ t : Set.Ioi T,
      (c * Real.exp (2 * t.val)) *
          (∫ x : KPCuspCharts.Cross F, ‖v.scalar (x, t.val)‖ ^ 2
            ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain) ≤
        (∫ x : KPCuspCharts.Cross F, v.gradientSq (x, t.val)
          ∂(volume.prod G.shapeMeasure).restrict G.fundamentalDomain))
    (η : ℝ → ℝ) (hη : CompactRadialTest T η) :
    c * (∫ p, Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2
      ∂chartMeasure G) ≤
      (∫ p, η p.2 ^ 2 * v.gradientSq p ∂chartMeasure G) := by
  let μ := (volume.prod G.shapeMeasure).restrict G.fundamentalDomain
  let ν := KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F)
  letI := G.haar_shapeMeasure
  letI : SigmaFinite ν := by
    dsimp [ν, KPCuspCharts.radialMeasure]
    infer_instance
  have hm : chartMeasure G = μ.prod ν := by
    dsimp [chartMeasure, μ]
    rw [← show ν.restrict Set.univ = ν from Measure.restrict_univ,
      Measure.prod_restrict]
    congr 1
    ext p
    simp
  have hi := KPCompactGreen.compact_radial_densities_integrable G v η hη
  have hl : Integrable (fun p : KPCuspCharts.Coordinates F =>
      Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) (μ.prod ν) := by
    simpa only [hm] using hi.2.2.1
  have hr : Integrable (fun p : KPCuspCharts.Coordinates F =>
      η p.2 ^ 2 * v.gradientSq p) (μ.prod ν) := by
    simpa only [hm] using hi.1
  rw [hm, integral_prod_symm _ hl, integral_prod_symm _ hr,
    ← integral_const_mul]
  apply integral_mono_ae (hl.integral_prod_right.const_mul c) hr.integral_prod_right
  filter_upwards with t
  simp only [integral_const_mul]
  by_cases ht : T < t
  · have hh := mul_le_mul_of_nonneg_left (hcross ⟨t, ht⟩) (sq_nonneg (η t))
    dsimp only at hh
    convert hh using 1 <;> ring
  · have hz : η t = 0 := by
      by_contra hs
      exact ht (hη.2.2 (subset_tsupport η hs))
    simp [hz]

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

theorem mean_zero_gap_specialization
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
    {g : KPFiniteCuspAtlas.FiniteCover F ζ hζ}
    {line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g}
    (A : KPFiniteCuspAtlas.ComponentAtlas F ζ hζ hF U g line)
    (a : Fin A.cuspCount)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus _ (A.parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g)
        (A.cusp a) (A.representative a)))))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {T : ℝ}
      (v : Representative ζ hζ _
        (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
          (KPCuspGenuineMonodromy.Component F ζ hζ U g)
          (A.cusp a) (A.representative a)))
        (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) T),
      (∀ b t, (∫ y, v.torusSlice (A.geometry a) (A.monodromy a) b t y ∂μ) = 0) →
      ∀ (η : ℝ → ℝ), CompactRadialTest T η →
        c * (∫ p, Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2
          ∂chartMeasure (A.geometry a)) ≤
        (∫ p, η p.2 ^ 2 * v.gradientSq p ∂chartMeasure (A.geometry a)) := by
  refine ⟨4 * Real.pi ^ 2 * A.frequencyGap, by
    have := A.positive_frequencyGap
    positivity, ?_⟩
  intro T v hv η hη
  have hmode : ∀ b ∈ A.boundedShapes a,
      ∀ ξ : KPCuspFrequencyGap.Frequency _ (A.parabolic a)
        (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
          (KPCuspGenuineMonodromy.Component F ζ hζ U g)
          (A.cusp a) (A.representative a))),
      (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
        ∀ t : ℝ, 4 * Real.pi ^ 2 * A.frequencyGap * Real.exp (2 * t) ≤
          KPCuspFrequencyGap.horizontalEnergy t b ξ := by
    intro b hb ξ hξ t
    have hgap := A.shortest_frequency a b hb ξ hξ
    dsimp [KPCuspFrequencyGap.horizontalEnergy]
    calc
      _ = (4 * Real.pi ^ 2 * Real.exp (2 * t)) * A.frequencyGap := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  have hc : 0 ≤ 4 * Real.pi ^ 2 * A.frequencyGap := by
    have := A.positive_frequencyGap
    positivity
  have hslice : ∀ b ∈ A.boundedShapes a, ∀ t : Set.Ioi T,
      (4 * Real.pi ^ 2 * A.frequencyGap * Real.exp (2 * t.val)) *
          (∫ z, ‖v.torusSlice (A.geometry a) (A.monodromy a) b t z‖ ^ 2 ∂μ) ≤
        (∫ z, GapCoercivity.torusHorizontalSq _ (A.parabolic a) _ b t.val
          (v.torusSlice (A.geometry a) (A.monodromy a) b t) z ∂μ) := by
    intro b hb t
    exact GapCoercivity.kernel_torus_poincare _ (A.parabolic a) _
      ⟨(A.frequencies a).kernel_discrete, (A.frequencies a).kernel_full⟩
      μ hμ hprob b t.val
      (4 * Real.pi ^ 2 * A.frequencyGap * Real.exp (2 * t.val))
      (fun ξ hξ => hmode b hb ξ hξ t.val)
      (v.torusSlice (A.geometry a) (A.monodromy a) b t)
      (GapCoercivity.smooth_periodic_slice (A.geometry a) (A.monodromy a) v b t)
      (hv b t)
  have hcross := GapCoercivity.cross_section_coercivity
    (A.geometry a) (A.monodromy a) μ hμ hprob
    (A.boundedShapes a) (A.compact_boundedShapes a) (A.shapes_cover a)
    v (4 * Real.pi ^ 2 * A.frequencyGap) hc hslice
  exact GapCoercivity.integrate_cross_section_coercivity
    (A.geometry a) v (4 * Real.pi ^ 2 * A.frequencyGap) hc hcross η hη

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

end

end
