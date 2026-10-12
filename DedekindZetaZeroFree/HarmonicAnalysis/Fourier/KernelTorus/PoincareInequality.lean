module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.KernelTorus.Parseval
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactTori.DirectionalDerivativeIntegral

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal Pointwise
open MeasureTheory.Measure

namespace DedekindZetaZeroFree.PeriodicLiftHaar

variable {F : Type} [Field F] [NumberField F]

private theorem compact_of_finite_haar
    {G : Type*} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [IsTopologicalAddGroup G] [WeaklyLocallyCompactSpace G]
    [MeasurableConstVAdd G G] (μ : Measure G) [μ.IsAddLeftInvariant]
    [μ.IsOpenPosMeasure] [IsFiniteMeasure μ] : CompactSpace G := by
  classical
  by_contra H
  rw [not_compactSpace_iff] at H
  obtain ⟨K, K1, hK, Kclosed⟩ : ∃ K ∈ nhds (0 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 0
  have K_pos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have A : ∀ L : Set G, IsCompact L → ∃ g : G, Disjoint L (g +ᵥ K) := fun L hL =>
    exists_disjoint_vadd_of_isCompact hL hK
  choose! g hg using A
  let L : ℕ → Set G := fun n => (fun T : Set G => T ∪ (g T +ᵥ K))^[n] K
  have Lcompact : ∀ n, IsCompact (L n) := fun n => by
    induction n with
    | zero => exact hK
    | succ n IH =>
      simp only [L, Function.iterate_succ_apply']
      exact IH.union (hK.vadd (g (L n)))
  have Lclosed : ∀ n, IsClosed (L n) := fun n => by
    induction n with
    | zero => exact Kclosed
    | succ n IH =>
      simp only [L, Function.iterate_succ_apply']
      exact IH.union (Kclosed.vadd (g (L n)))
  have M : ∀ n, μ (L n) = (n + 1 : ℕ) * μ K := fun n => by
    induction n with
    | zero => simp [L]
    | succ n IH =>
      calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) +ᵥ K) := by
          simp only [L, Function.iterate_succ_apply']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurableSet
        _ = (n + 1 + 1 : ℕ) * μ K := by
          simp only [IH, measure_vadd, add_mul, Nat.cast_add, Nat.cast_one, one_mul]
  have N : Filter.Tendsto (fun n => μ (L n)) Filter.atTop (nhds (∞ * μ K)) := by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ENNReal.tendsto_nat_nhds_top.comp (Filter.tendsto_add_atTop_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', ite_false] at N
  have ht : μ Set.univ = ∞ := top_le_iff.1 <|
    le_of_tendsto' N fun n => measure_mono (Set.subset_univ _)
  exact (measure_ne_top μ Set.univ) ht

private theorem derivative_mk
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : AddSubgroup H) (f : H ⧸ K → ℂ) (w y : H) :
    fderiv ℝ (fun x : H => f (QuotientAddGroup.mk x))
      (Quotient.out (QuotientAddGroup.mk y : H ⧸ K)) w =
      fderiv ℝ (fun x : H => f (QuotientAddGroup.mk x)) y w := by
  let x : H := Quotient.out (QuotientAddGroup.mk y : H ⧸ K)
  have hx : (QuotientAddGroup.mk x : H ⧸ K) = QuotientAddGroup.mk y := Quotient.out_eq _
  have hd : (QuotientAddGroup.mk (y - x) : H ⧸ K) = 0 := by
    rw [QuotientAddGroup.mk_sub, hx, sub_self]
  have hshift : (fun z : H => f (QuotientAddGroup.mk (z + (y - x)))) =
      (fun z => f (QuotientAddGroup.mk z)) := by
    funext z
    rw [QuotientAddGroup.mk_add, hd, add_zero]
  have hh := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun z : H => f (QuotientAddGroup.mk z)) (x := x) (y - x)
  rw [hshift, show x + (y - x) = y by abel] at hh
  exact congrArg (fun L => L w) hh

 def exponent (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) :
    KPCuspCharts.Horizontal F →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp ((innerSL ℝ ξ).comp
    (KPCuspFrequencyGap.coordinates _).symm.toLinearMap.toContinuousLinearMap)).smulRight
      ((2 * Real.pi : ℂ) * Complex.I)

private theorem exponent_apply
    (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F))
    (y : KPCuspCharts.Horizontal F) :
    exponent ξ y = (2 * Real.pi * inner ℝ ξ
      ((KPCuspFrequencyGap.coordinates _).symm y) : ℝ) * Complex.I := by
  change ((inner ℝ ξ ((KPCuspFrequencyGap.coordinates _).symm y) : ℝ) : ℂ) *
    ((2 * Real.pi : ℂ) * Complex.I) = _
  push_cast
  ring

private theorem mode_lift (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (ξ : KPCuspFrequencyGap.Frequency S D ρ) :
    (fun y : KPCuspCharts.Horizontal F =>
      KPCuspFrequencyGap.torusMode S D ρ ξ (QuotientAddGroup.mk y)) =
    (fun y => Complex.exp (exponent (ξ : KPCuspFrequencyGap.Euclidean _) y)) := by
  funext y
  rw [exponent_apply]
  rfl

theorem coefficient_fderiv
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y)))
    (ξ : KPCuspFrequencyGap.Frequency S D ρ) (w : KPCuspCharts.Horizontal F) :
    KPMeanZeroWeightedEnergy.GapCoercivity.Fourier.coefficient S D ρ μ
      (fun z => fderiv ℝ (fun y : KPCuspCharts.Horizontal F =>
        f (QuotientAddGroup.mk y)) (Quotient.out z) w) ξ =
      ((2 * Real.pi : ℂ) * Complex.I *
        (inner ℝ (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F))
          ((KPCuspFrequencyGap.coordinates _).symm w) : ℝ)) *
        KPMeanZeroWeightedEnergy.GapCoercivity.Fourier.coefficient S D ρ μ f ξ := by
  letI := hμ
  letI := hprob
  letI : OpensMeasurableSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    (opensMeasurableSpace_iff_forall_measurableSet).mpr (fun U hU =>
      (QuotientAddGroup.continuous_mk).isOpen_preimage U hU |>.measurableSet)
  let K := KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ)
  let Q := KPCuspGenuineMonodromy.KernelTorus S D ρ
  let m := KPCuspFrequencyGap.torusMode S D ρ ξ
  let L := exponent (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F))
  let c : ℂ := (2 * Real.pi : ℂ) * Complex.I *
    (inner ℝ (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F))
      ((KPCuspFrequencyGap.coordinates _).symm w) : ℝ)
  let df := fun z : Q => fderiv ℝ (fun y : KPCuspCharts.Horizontal F =>
    f (QuotientAddGroup.mk y)) (Quotient.out z) w
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : KPCuspCharts.Horizontal F => m (QuotientAddGroup.mk y)) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : KPCuspCharts.Horizontal F =>
      KPCuspFrequencyGap.torusMode S D ρ ξ (QuotientAddGroup.mk y))
    rw [mode_lift]
    exact L.contDiff.cexp
  have hd : ∀ y : KPCuspCharts.Horizontal F,
      fderiv ℝ (fun x : KPCuspCharts.Horizontal F => m (QuotientAddGroup.mk x)) y =
        m (QuotientAddGroup.mk y) • L := by
    intro y
    change fderiv ℝ (fun x : KPCuspCharts.Horizontal F =>
      KPCuspFrequencyGap.torusMode S D ρ ξ (QuotientAddGroup.mk x)) y = _
    rw [mode_lift]
    have hmy : m (QuotientAddGroup.mk y) = Complex.exp (L y) :=
      congrFun (mode_lift S D ρ ξ) y
    rw [hmy]
    exact (L.hasFDerivAt.cexp).fderiv
  have hLc : L w = c := by
    dsimp [L, c]
    rw [exponent_apply]
    push_cast
    ring
  have hsc : star c = -c := by
    dsimp [c]
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hms : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => star (m (QuotientAddGroup.mk y))) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp hm
  have hp := integral_fderiv_eq_zero K μ hμ hprob
    (fun z : Q => star (m z) * f z) (hms.mul hf) w
  have hder : ∀ z : Q,
      fderiv ℝ (fun y : KPCuspCharts.Horizontal F =>
        star (m (QuotientAddGroup.mk y)) * f (QuotientAddGroup.mk y)) (Quotient.out z) w =
        star (m z) * df z - c * (star (m z) * f z) := by
    intro z
    change (fderiv ℝ ((fun y : KPCuspCharts.Horizontal F => star (m (QuotientAddGroup.mk y))) *
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))) (Quotient.out z)) w = _
    rw [fderiv_mul (hms.differentiable (by simp)).differentiableAt
      (hf.differentiable (by simp)).differentiableAt]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      fderiv_star, ContinuousLinearMap.comp_apply, starL'_apply, hd,
      ContinuousLinearMap.smul_apply, smul_eq_mul, star_mul, hLc, hsc]
    simp only [Quotient.out_eq]
    change star (m z) * df z + f z * star (m z * c) = _
    rw [star_mul, hsc]
    ring
  have heq : (fun z : Q => fderiv ℝ (fun y : KPCuspCharts.Horizontal F =>
      star (m (QuotientAddGroup.mk y)) * f (QuotientAddGroup.mk y)) (Quotient.out z) w) =
      (fun z : Q => star (m z) * df z - c * (star (m z) * f z)) := funext hder
  rw [heq] at hp
  letI : MeasurableConstVAdd Q Q := ⟨fun a => by
    induction a using Quotient.inductionOn with
    | h x =>
      apply measurable_from_quotient.mpr
      change Measurable (fun y : KPCuspCharts.Horizontal F =>
        (QuotientAddGroup.mk x : Q) + QuotientAddGroup.mk y)
      simp only [← QuotientAddGroup.mk_add]
      exact QuotientAddGroup.measurable_coe.comp (measurable_const.add measurable_id)⟩
  have hc : CompactSpace Q := compact_of_finite_haar μ
  letI := hc
  have hcf : Continuous f :=
    (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr hf.continuous
  have hcm : Continuous m :=
    (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr hm.continuous
  have hcdf : Continuous df := by
    apply (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr
    change Continuous (fun y : KPCuspCharts.Horizontal F =>
      fderiv ℝ (fun x : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk x))
        (Quotient.out (QuotientAddGroup.mk y : Q)) w)
    have he : (fun y : KPCuspCharts.Horizontal F =>
        fderiv ℝ (fun x : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk x))
          (Quotient.out (QuotientAddGroup.mk y : Q)) w) =
        (fun y : KPCuspCharts.Horizontal F =>
          fderiv ℝ (fun x : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk x)) y w) :=
      funext (derivative_mk K f w)
    rw [he]
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 : Integrable (fun z : Q => star (m z) * df z) μ := by
    have hh := (hcm.star.mul hcdf).continuousOn.integrableOn_compact'
      (μ := μ) isCompact_univ MeasurableSet.univ
    rw [IntegrableOn, Measure.restrict_univ] at hh
    convert hh using 1
  have hi2 : Integrable (fun z : Q => c * (star (m z) * f z)) μ := by
    have hh := (continuous_const (y := c) |>.mul (hcm.star.mul hcf)).continuousOn.integrableOn_compact'
      (μ := μ) isCompact_univ MeasurableSet.univ
    rw [IntegrableOn, Measure.restrict_univ] at hh
    convert hh using 1
  rw [integral_sub hi1 hi2, integral_const_mul] at hp
  exact sub_eq_zero.mp hp

end DedekindZetaZeroFree.PeriodicLiftHaar

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.Fourier

variable {F : Type} [Field F] [NumberField F]

def horizontalDeriv
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (w : KPCuspCharts.Horizontal F)
    (z : KPCuspGenuineMonodromy.KernelTorus S D ρ) : ℂ :=
  fderiv ℝ (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))
    (Quotient.out z) w

private theorem horizontalDeriv_mk
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (w y : KPCuspCharts.Horizontal F) :
    horizontalDeriv S D ρ f w (QuotientAddGroup.mk y) =
      fderiv ℝ (fun z : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk z)) y w := by
  let x : KPCuspCharts.Horizontal F := Quotient.out
    (QuotientAddGroup.mk y : KPCuspGenuineMonodromy.KernelTorus S D ρ)
  have hx : (QuotientAddGroup.mk x : KPCuspGenuineMonodromy.KernelTorus S D ρ) =
      QuotientAddGroup.mk y := Quotient.out_eq _
  have hd : (QuotientAddGroup.mk (y - x) : KPCuspGenuineMonodromy.KernelTorus S D ρ) = 0 := by
    rw [QuotientAddGroup.mk_sub, hx, sub_self]
  have hshift : (fun z : KPCuspCharts.Horizontal F =>
      f (QuotientAddGroup.mk (z + (y - x)))) =
      (fun z => f (QuotientAddGroup.mk z)) := by
    funext z
    rw [QuotientAddGroup.mk_add, hd, add_zero]
  have hh := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun z : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk z))
    (x := x) (y - x)
  rw [hshift, show x + (y - x) = y by abel] at hh
  exact congrArg (fun L => L w) hh

private theorem continuous_horizontalDeriv
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y)))
    (w : KPCuspCharts.Horizontal F) : Continuous (horizontalDeriv S D ρ f w) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ))).continuous_iff.mpr
  change Continuous (fun y : KPCuspCharts.Horizontal F =>
    horizontalDeriv S D ρ f w (QuotientAddGroup.mk y))
  simp_rw [horizontalDeriv_mk]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem pairing_single
    (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F))
    (i : Fin (KPCuspLogShape.dimension F)) (v : ℂ) :
    inner ℝ ξ ((KPCuspFrequencyGap.coordinates _).symm (Pi.single i v)) =
      (star (KPCuspFrequencyGap.coordinates _ ξ i) * v).re := by
  simp_rw [PiLp.inner_apply (𝕜 := ℝ)]
  have hs : ∀ j, ((KPCuspFrequencyGap.coordinates (KPCuspLogShape.dimension F)).symm
      (Pi.single i v)).ofLp j = (Pi.single i v : KPCuspCharts.Horizontal F) j := by
    intro j; rfl
  simp only [hs, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    rw [real_inner_eq_re_inner ℂ]
    simp only [RCLike.inner_apply]
    rw [mul_comm]
    rfl
  · intro j hj hji
    simp [hji]
  · simp

theorem coefficient_horizontalDeriv
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y)))
    (ξ : KPCuspFrequencyGap.Frequency S D ρ) (w : KPCuspCharts.Horizontal F) :
    coefficient S D ρ μ (horizontalDeriv S D ρ f w) ξ =
      ((2 * Real.pi : ℂ) * Complex.I *
        (inner ℝ (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F))
          ((KPCuspFrequencyGap.coordinates _).symm w) : ℝ)) *
        coefficient S D ρ μ f ξ := by
  exact PeriodicLiftHaar.coefficient_fderiv S D ρ μ hμ hprob f hf ξ w

private theorem coefficient_energy_eq
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y)))
    (ξ : KPCuspFrequencyGap.Frequency S D ρ) :
    (∑ i, Real.exp (2 * (t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
      (‖coefficient S D ρ μ (horizontalDeriv S D ρ f (Pi.single i 1)) ξ‖ ^ 2 +
        ‖coefficient S D ρ μ (horizontalDeriv S D ρ f (Pi.single i Complex.I)) ξ‖ ^ 2)) =
      ‖coefficient S D ρ μ f ξ‖ ^ 2 * KPCuspFrequencyGap.horizontalEnergy t b ξ := by
  simp_rw [coefficient_horizontalDeriv S D ρ μ hμ hprob f hf, pairing_single]
  simp only [norm_mul, Complex.mul_re, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, sub_neg_eq_add,
    zero_add, Complex.conj_re, Complex.conj_im, neg_neg, Complex.norm_I,
    Complex.norm_real, one_mul, mul_one]
  unfold KPCuspFrequencyGap.horizontalEnergy KPCuspFrequencyGap.shapeEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Real.exp (2 * (t + (b : Fin _ → ℝ) i)) =
    Real.exp (2 * t) * Real.exp (2 * (b : Fin _ → ℝ) i) by rw [mul_add, Real.exp_add]]
  simp only [mul_pow]
  simp_rw [Complex.sq_norm]
  simp only [Real.norm_eq_abs, sq_abs, RCLike.star_def,
    Complex.conj_re, Complex.conj_im, neg_neg, neg_sq, Complex.normSq_apply]
  norm_num
  ring

theorem kernel_torus_energy_parseval
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (hlattice : ∃ hd : DiscreteTopology
      (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ),
      letI := hd; IsZLattice ℝ (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ))
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))) :
    Summable (fun ξ => ‖coefficient S D ρ μ f ξ‖ ^ 2 *
      KPCuspFrequencyGap.horizontalEnergy t b ξ) ∧
    (∫ z : KPCuspGenuineMonodromy.KernelTorus S D ρ,
      (∑ i, Real.exp (2 * (t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
        (‖fderiv ℝ (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))
            (Quotient.out z) (Pi.single i 1)‖ ^ 2 +
          ‖fderiv ℝ (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))
            (Quotient.out z) (Pi.single i Complex.I)‖ ^ 2)) ∂μ) =
      ∑' ξ, ‖coefficient S D ρ μ f ξ‖ ^ 2 *
        KPCuspFrequencyGap.horizontalEnergy t b ξ := by
  letI := hprob
  obtain ⟨e, n, hn⟩ := FullRealLatticeTorus.exists_coordinates_and_characters
    (KPCuspFrequencyGap.coordinates (KPCuspLogShape.dimension F))
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ))
    hlattice
  letI : CompactSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    e.toHomeomorph.symm.compactSpace
  letI : T2Space (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    e.toHomeomorph.symm.t2Space
  letI : BorelSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    AddCosetSpace.borelSpace
  let a : Fin (KPCuspLogShape.dimension F) → ℝ :=
    fun i => Real.exp (2 * (t + (b : Fin _ → ℝ) i))
  let g : Fin (KPCuspLogShape.dimension F) →
      KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ :=
    fun i => horizontalDeriv S D ρ f (Pi.single i 1)
  let k : Fin (KPCuspLogShape.dimension F) →
      KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ :=
    fun i => horizontalDeriv S D ρ f (Pi.single i Complex.I)
  have hg i : Continuous (g i) := continuous_horizontalDeriv S D ρ f hf _
  have hk i : Continuous (k i) := continuous_horizontalDeriv S D ρ f hf _
  have hgi i : Integrable (fun z => ‖g i z‖ ^ 2) μ :=
    ((hg i).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hki i : Integrable (fun z => ‖k i z‖ ^ 2) μ :=
    ((hk i).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have pg i := kernel_torus_parseval S D ρ hlattice μ hμ hprob (g i) (hg i)
  have pk i := kernel_torus_parseval S D ρ hlattice μ hμ hprob (k i) (hk i)
  let q : Fin (KPCuspLogShape.dimension F) → KPCuspFrequencyGap.Frequency S D ρ → ℝ :=
    fun i ξ => a i *
      (‖coefficient S D ρ μ (g i) ξ‖ ^ 2 + ‖coefficient S D ρ μ (k i) ξ‖ ^ 2)
  have hq i : Summable (q i) := ((pg i).1.add (pk i).1).mul_left (a i)
  have hqe ξ : (∑ i, q i ξ) = ‖coefficient S D ρ μ f ξ‖ ^ 2 *
      KPCuspFrequencyGap.horizontalEnergy t b ξ :=
    coefficient_energy_eq S D ρ μ hμ hprob b t f hf ξ
  constructor
  · have hs := summable_sum (s := Finset.univ) (fun i _ => hq i)
    simpa only [hqe] using hs
  · change (∫ z, ∑ i, a i * (‖g i z‖ ^ 2 + ‖k i z‖ ^ 2) ∂μ) = _
    rw [integral_finset_sum Finset.univ
      (f := fun i z => a i * (‖g i z‖ ^ 2 + ‖k i z‖ ^ 2))
      (fun i _ => ((hgi i).add (hki i)).const_mul (a i))]
    simp_rw [integral_const_mul]
    have hpi i : (∫ z, ‖g i z‖ ^ 2 + ‖k i z‖ ^ 2 ∂μ) =
        ∑' ξ, (‖coefficient S D ρ μ (g i) ξ‖ ^ 2 + ‖coefficient S D ρ μ (k i) ξ‖ ^ 2) := by
      rw [integral_add (hgi i) (hki i), (pg i).2, (pk i).2,
        (Summable.tsum_add (pg i).1 (pk i).1)]
    simp_rw [hpi, ← tsum_mul_left]
    change (∑ i, ∑' ξ, q i ξ) = _
    rw [← Summable.tsum_finsetSum (fun i _ => hq i)]
    simp_rw [hqe]

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.Fourier

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

variable {F : Type} [Field F] [NumberField F]

def torusHorizontalSq
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (z : KPCuspGenuineMonodromy.KernelTorus S D ρ) : ℝ :=
  let lift : KPCuspCharts.Horizontal F → ℂ := fun y => f (QuotientAddGroup.mk y)
  ∑ i, Real.exp (2 * (t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
    (‖fderiv ℝ lift (Quotient.out z) (Pi.single i 1)‖ ^ 2 +
      ‖fderiv ℝ lift (Quotient.out z) (Pi.single i Complex.I)‖ ^ 2)

theorem lift_fderiv_eq
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (x y : KPCuspCharts.Horizontal F)
    (hxy : (QuotientAddGroup.mk x : KPCuspGenuineMonodromy.KernelTorus S D ρ) =
      QuotientAddGroup.mk y) :
    fderiv ℝ (fun z => f (QuotientAddGroup.mk z)) x =
      fderiv ℝ (fun z => f (QuotientAddGroup.mk z)) y := by
  let L := KPCuspCharts.translationLattice F
    (KPCuspGenuineMonodromy.kernelLattice S D ρ)
  have hd : (QuotientAddGroup.mk (y - x) : KPCuspGenuineMonodromy.KernelTorus S D ρ) = 0 := by
    rw [QuotientAddGroup.mk_sub, ← hxy, sub_self]
  have hshift : (fun z : KPCuspCharts.Horizontal F =>
      f (QuotientAddGroup.mk (z + (y - x)))) =
      (fun z => f (QuotientAddGroup.mk z)) := by
    funext z
    rw [QuotientAddGroup.mk_add, hd, add_zero]
  have hh := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun z : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk z))
    (x := x) (y - x)
  rw [hshift, show x + (y - x) = y by abel] at hh
  exact hh

theorem torusHorizontalSq_mk
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (y : KPCuspCharts.Horizontal F) :
    torusHorizontalSq S D ρ b t f (QuotientAddGroup.mk y) =
      ∑ i, Real.exp (2 * (t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)) *
        (‖fderiv ℝ (fun z => f (QuotientAddGroup.mk z)) y (Pi.single i 1)‖ ^ 2 +
          ‖fderiv ℝ (fun z => f (QuotientAddGroup.mk z)) y
            (Pi.single i Complex.I)‖ ^ 2) := by
  unfold torusHorizontalSq
  dsimp only
  rw [lift_fderiv_eq S D ρ f _ y (Quotient.out_eq _)]

theorem torusHorizontalSq_nonneg
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (z : KPCuspGenuineMonodromy.KernelTorus S D ρ) :
    0 ≤ torusHorizontalSq S D ρ b t f z := by
  unfold torusHorizontalSq
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_nonneg _)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem continuous_torusHorizontalSq
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))) :
    Continuous (torusHorizontalSq S D ρ b t f) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ))).continuous_iff.mpr
  change Continuous (fun y : KPCuspCharts.Horizontal F =>
    torusHorizontalSq S D ρ b t f (QuotientAddGroup.mk y))
  simp_rw [torusHorizontalSq_mk]
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul
    ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2).add
      (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2))

theorem kernel_torus_poincare_nonpos
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (b : KPCuspCharts.Shape F) (t c : ℝ) (hc : c ≤ 0)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ) :
    c * (∫ z, ‖f z‖ ^ 2 ∂μ) ≤
      (∫ z, torusHorizontalSq S D ρ b t f z ∂μ) := by
  exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc
    (integral_nonneg fun z => sq_nonneg _))
    (integral_nonneg (torusHorizontalSq_nonneg S D ρ b t f))

theorem compactSpace_kernelTorus (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (hlattice : ∃ hd : DiscreteTopology
      (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ),
      letI := hd; IsZLattice ℝ (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ)) :
    CompactSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) := by
  obtain ⟨hd, hL⟩ := hlattice
  letI := hd
  letI := hL
  let q : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F) →
      KPCuspGenuineMonodromy.KernelTorus S D ρ :=
    fun y => QuotientAddGroup.mk (KPCuspFrequencyGap.coordinates _ y)
  have hq : Continuous q := QuotientAddGroup.continuous_mk.comp
    (KPCuspFrequencyGap.coordinates _).toContinuousLinearEquiv.continuous
  have hp : ∀ z w, w ∈ KPCuspFrequencyGap.kernelEuclideanLattice S D ρ → q (z + w) = q z := by
    intro z w hw
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    change QuotientAddGroup.mk (KPCuspFrequencyGap.coordinates _
      (z + (KPCuspFrequencyGap.coordinates _).symm u)) = _
    rw [map_add, LinearEquiv.apply_symm_apply, QuotientAddGroup.mk_add]
    rw [(QuotientAddGroup.eq_zero_iff u).mpr hu, add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic
    (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ) q hq hp
  have hs : Function.Surjective q :=
    QuotientAddGroup.mk_surjective.comp (KPCuspFrequencyGap.coordinates _).surjective
  exact isCompact_univ_iff.mp (by simpa [hs.range_eq] using hc)

theorem continuous_of_smooth_lift
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))) :
    Continuous f :=
  (QuotientAddGroup.isQuotientMap_mk
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ))).continuous_iff.mpr
    hf.continuous

theorem opensMeasurableSpace_kernelTorus
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F) :
    OpensMeasurableSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) := by
  constructor
  apply MeasurableSpace.generateFrom_le
  intro u hu
  change MeasurableSet (QuotientAddGroup.mk ⁻¹' u : Set (KPCuspCharts.Horizontal F))
  exact (QuotientAddGroup.continuous_mk.isOpen_preimage u hu).measurableSet

theorem integrable_of_smooth_lift
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (hlattice : ∃ hd : DiscreteTopology
      (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ),
      letI := hd; IsZLattice ℝ (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ))
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    [IsFiniteMeasure μ] (b : KPCuspCharts.Shape F) (t : ℝ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y))) :
    Integrable f μ ∧ Integrable (fun z => ‖f z‖ ^ 2) μ ∧
      Integrable (torusHorizontalSq S D ρ b t f) μ := by
  letI := compactSpace_kernelTorus S D ρ hlattice
  letI := opensMeasurableSpace_kernelTorus S D ρ
  have hfc := continuous_of_smooth_lift S D ρ f hf
  exact ⟨hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f),
    (hfc.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    (continuous_torusHorizontalSq S D ρ b t f hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)⟩

 theorem torusMode_mk
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (ξ : KPCuspFrequencyGap.Frequency S D ρ) (y : KPCuspCharts.Horizontal F) :
    KPCuspFrequencyGap.torusMode S D ρ ξ (QuotientAddGroup.mk y) =
      KPCuspFrequencyGap.fourierCharacter (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) y := rfl

theorem torusMode_zero
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (z : KPCuspGenuineMonodromy.KernelTorus S D ρ) :
    KPCuspFrequencyGap.torusMode S D ρ 0 z = 1 := by
  induction z using Quotient.inductionOn with
  | h y => simp [torusMode_mk, KPCuspFrequencyGap.fourierCharacter]

theorem kernel_torus_poincare_of_parseval
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (b : KPCuspCharts.Shape F) (t c : ℝ)
    (hgap : ∀ ξ : KPCuspFrequencyGap.Frequency S D ρ,
      (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
        c ≤ KPCuspFrequencyGap.horizontalEnergy t b ξ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (a : KPCuspFrequencyGap.Frequency S D ρ → ℂ)
    (ha0 : a 0 = 0)
    (ha : Summable (fun ξ => ‖a ξ‖ ^ 2))
    (haE : Summable (fun ξ => ‖a ξ‖ ^ 2 * KPCuspFrequencyGap.horizontalEnergy t b ξ))
    (hparseval : (∫ z, ‖f z‖ ^ 2 ∂μ) = ∑' ξ, ‖a ξ‖ ^ 2)
    (henergy : (∫ z, torusHorizontalSq S D ρ b t f z ∂μ) =
      ∑' ξ, ‖a ξ‖ ^ 2 * KPCuspFrequencyGap.horizontalEnergy t b ξ) :
    c * (∫ z, ‖f z‖ ^ 2 ∂μ) ≤
      (∫ z, torusHorizontalSq S D ρ b t f z ∂μ) := by
  rw [hparseval, henergy, ← tsum_mul_left]
  refine (ha.mul_left c).tsum_le_tsum (fun ξ => ?_) haE
  by_cases hξ : (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) = 0
  · have hξ0 : ξ = 0 := Subtype.ext hξ
    simp [hξ0, ha0]
  · rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hgap ξ hξ) (sq_nonneg _)

theorem kernel_torus_poincare
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (hlattice : ∃ hd : DiscreteTopology
      (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ),
      letI := hd; IsZLattice ℝ (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ))
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (b : KPCuspCharts.Shape F) (t c : ℝ)
    (hgap : ∀ ξ : KPCuspFrequencyGap.Frequency S D ρ,
      (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
        c ≤ KPCuspFrequencyGap.horizontalEnergy t b ξ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : KPCuspCharts.Horizontal F => f (QuotientAddGroup.mk y)))
    (hzero : (∫ z, f z ∂μ) = 0) :
    c * (∫ z, ‖f z‖ ^ 2 ∂μ) ≤
      (∫ z, torusHorizontalSq S D ρ b t f z ∂μ) := by
  by_cases hc : c ≤ 0
  · exact kernel_torus_poincare_nonpos S D ρ μ b t c hc f
  · obtain ⟨ha, hparseval⟩ := Fourier.kernel_torus_parseval S D ρ hlattice μ hμ hprob
      f (continuous_of_smooth_lift S D ρ f hf)
    obtain ⟨haE, henergy⟩ := Fourier.kernel_torus_energy_parseval
      S D ρ hlattice μ hμ hprob b t f hf
    have ha0 : Fourier.coefficient S D ρ μ f 0 = 0 := by
      simpa [Fourier.coefficient, torusMode_zero] using hzero
    exact kernel_torus_poincare_of_parseval S D ρ μ b t c hgap f
      (Fourier.coefficient S D ρ μ f) ha0 ha haE hparseval henergy

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity

end

end
