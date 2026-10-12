module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.SmoothCompactTorusExpansion
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialTests

@[expose] public section

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.FullRealLatticeTorus

theorem exists_coordinates_and_characters
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (c : E ≃ₗ[ℝ] H) (K : AddSubgroup H)
    (hlattice : ∃ hd : DiscreteTopology
      (K.toIntSubmodule.map (c.symm.toLinearMap.restrictScalars ℤ)),
      letI := hd;
      IsZLattice ℝ (K.toIntSubmodule.map (c.symm.toLinearMap.restrictScalars ℤ))) :
    ∃ e : (H ⧸ K) ≃ₜ+ UnitAddTorus (Fin (Module.finrank ℝ E)),
    ∃ n : PoissonArch.dualLattice
      (K.toIntSubmodule.map (c.symm.toLinearMap.restrictScalars ℤ)) ≃
        (Fin (Module.finrank ℝ E) → ℤ),
      ∀ (ξ : PoissonArch.dualLattice
        (K.toIntSubmodule.map (c.symm.toLinearMap.restrictScalars ℤ))) (y : H),
        Complex.exp ((2 * Real.pi * inner ℝ (ξ : E) (c.symm y) : ℝ) * Complex.I) =
          UnitAddTorus.mFourier (n ξ) (e (QuotientAddGroup.mk y)) := by
  classical
  obtain ⟨hd, hl⟩ := hlattice
  let L := K.toIntSubmodule.map (c.symm.toLinearMap.restrictScalars ℤ)
  letI : DiscreteTopology L := hd
  letI : IsZLattice ℝ L := hl
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ L :=
    (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
      simp))
  let B := b.ofZLatticeBasis ℝ L
  letI : FiniteDimensional ℝ H := c.finiteDimensional
  let a := c.symm.trans B.equivFun
  let q : (Fin (Module.finrank ℝ E) → ℝ) →+ UnitAddTorus (Fin (Module.finrank ℝ E)) :=
    { toFun := fun x i => (x i : UnitAddCircle)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; exact AddCircle.coe_add _ _ _ }
  let f : H →+ UnitAddTorus (Fin (Module.finrank ℝ E)) := q.comp a.toAddHom
  have hq : Function.Surjective q := by
    intro t
    choose x hx using fun i => QuotientAddGroup.mk_surjective (t i)
    exact ⟨x, funext hx⟩
  have hf : Function.Surjective f := hq.comp a.surjective
  have hker : K = f.ker := by
    ext y
    change y ∈ K ↔ (fun i => (B.repr (c.symm y) i : UnitAddCircle)) = 0
    have hL : c.symm y ∈ L ↔ y ∈ K := by
      simp only [L, Submodule.mem_map, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe]
      change (∃ x, x ∈ K ∧ c.symm x = c.symm y) ↔ y ∈ K
      constructor
      · rintro ⟨x, hx, he⟩
        exact c.symm.injective he ▸ hx
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [← hL, ← b.ofZLatticeBasis_span ℝ]
    rw [B.mem_span_iff_repr_mem ℤ]
    simp only [funext_iff, Pi.zero_apply, AddCircle.coe_eq_zero_iff,
      Set.mem_range, Int.smul_one_eq_cast, Int.cast_eq, Int.cast_one]
    rfl
  let e₀ := QuotientAddGroup.liftEquiv K hf hker
  have hcont : Continuous e₀ := by
    apply (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr
    change Continuous f
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp a.toContinuousLinearEquiv.continuous)
  have hopen : IsOpenMap e₀ := by
    apply (QuotientAddGroup.isOpenQuotientMap_mk (N := K)).isOpenMap_iff.mpr
    change IsOpenMap f
    exact (IsOpenMap.piMap (fun i => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun i => QuotientAddGroup.mk_surjective)).comp
      a.toContinuousLinearEquiv.toHomeomorph.isOpenMap
  let e : (H ⧸ K) ≃ₜ+ UnitAddTorus (Fin (Module.finrank ℝ E)) :=
    { e₀ with
      continuous_toFun := hcont
      continuous_invFun := (e₀.toEquiv.toHomeomorphOfContinuousOpen hcont hopen).continuous_invFun }
  refine ⟨e, (PoissonArch.dualVector_b L b).symm.toEquiv, ?_⟩
  intro ξ y
  let n := (PoissonArch.dualVector_b L b).symm ξ
  have hξ : PoissonArch.dualVector_b L b n = ξ :=
    (PoissonArch.dualVector_b L b).apply_symm_apply ξ
  have hi : inner ℝ (ξ : E) (c.symm y) =
      ∑ i, B.repr (c.symm y) i * (n i : ℝ) := by
    rw [← hξ, real_inner_comm]
    conv_lhs => rw [← B.sum_repr (c.symm y)]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left]
    change B.repr (c.symm y) i * inner ℝ (B i) (PoissonArch.dualVector_b L b n : E) = _
    rw [real_inner_comm]
    simpa only [B, Module.Basis.ofZLatticeBasis_apply] using
      congrArg (fun t : ℝ => B.repr (c.symm y) i * t)
        (PoissonArch.dualVector_b_inner_basis L b n i)
  change Complex.exp ((2 * Real.pi * inner ℝ (ξ : E) (c.symm y) : ℝ) * Complex.I) =
    UnitAddTorus.mFourier n (fun i => (B.repr (c.symm y) i : UnitAddCircle))
  rw [hi]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
    Complex.ofReal_ofNat, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end DedekindZetaZeroFree.FullRealLatticeTorus

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.FullRealLatticeTorus

theorem hasSum_sq_coefficients_of_coordinates
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    {d : Type*} [Fintype d] {I : Type*}
    (e : G ≃ₜ+ UnitAddTorus d) (n : I ≃ (d → ℤ))
    (mode : I → G → ℂ)
    (hmode : ∀ ξ z, mode ξ z = UnitAddTorus.mFourier (n ξ) (e z))
    (μ : Measure G) (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : G → ℂ) (hf : Continuous f) :
    HasSum (fun ξ => ‖∫ z, star (mode ξ z) * f z ∂μ‖ ^ 2)
      (∫ z, ‖f z‖ ^ 2 ∂μ) := by
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  letI : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  letI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  letI := hμ
  letI := hprob
  have he : MeasurePreserving e μ volume :=
    AddMonoidHom.measurePreserving (f := e.toAddMonoidHom) e.continuous
      e.surjective (by simp)
  let g : C(UnitAddTorus d, ℂ) := ⟨f ∘ e.symm, hf.comp e.symm.continuous⟩
  have hcoeff (ξ : I) :
      (∫ z, star (mode ξ z) * f z ∂μ) = UnitAddTorus.mFourierCoeff g (n ξ) := by
    rw [UnitAddTorus.mFourierCoeff]
    rw [← he.integral_comp e.toHomeomorph.measurableEmbedding]
    simp [g, hmode, UnitAddTorus.mFourier_neg]
  have henergy : (∫ t, ‖(g.toLp 2 volume ℂ) t‖ ^ 2) = (∫ z, ‖f z‖ ^ 2 ∂μ) := by
    calc
      _ = ∫ t, ‖g t‖ ^ 2 := integral_congr_ae (by
        filter_upwards [g.coeFn_toLp (p := 2) volume (𝕜 := ℂ)] with t ht
        rw [ht])
      _ = _ := by
        rw [← he.integral_comp e.toHomeomorph.measurableEmbedding]
        simp [g]
  have hs := UnitAddTorus.hasSum_sq_mFourierCoeff (g.toLp 2 volume ℂ)
  simp only [UnitAddTorus.mFourierCoeff_toLp, henergy] at hs
  simpa only [Function.comp_def, ← hcoeff] using n.hasSum_iff.mpr hs

end DedekindZetaZeroFree.FullRealLatticeTorus

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.Fourier

variable {F : Type} [Field F] [NumberField F]

def coefficient
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (ξ : KPCuspFrequencyGap.Frequency S D ρ) : ℂ :=
  ∫ z, star (KPCuspFrequencyGap.torusMode S D ρ ξ z) * f z ∂μ

theorem kernel_torus_parseval
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (D : KPCuspCharts.ParabolicData F S) (ρ : S →* rootsOfUnity 3 F)
    (hlattice : ∃ hd : DiscreteTopology
      (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ),
      letI := hd; IsZLattice ℝ (KPCuspFrequencyGap.kernelEuclideanLattice S D ρ))
    (μ : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ))
    (hμ : μ.IsAddHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (f : KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ)
    (hf : Continuous f) :
    Summable (fun ξ => ‖coefficient S D ρ μ f ξ‖ ^ 2) ∧
      (∫ z, ‖f z‖ ^ 2 ∂μ) = ∑' ξ, ‖coefficient S D ρ μ f ξ‖ ^ 2 := by
  obtain ⟨e, n, hn⟩ := FullRealLatticeTorus.exists_coordinates_and_characters
    (KPCuspFrequencyGap.coordinates (KPCuspLogShape.dimension F))
    (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice S D ρ))
    hlattice
  have hmode : ∀ (ξ : KPCuspFrequencyGap.Frequency S D ρ)
      (z : KPCuspGenuineMonodromy.KernelTorus S D ρ),
      KPCuspFrequencyGap.torusMode S D ρ ξ z =
        UnitAddTorus.mFourier (n ξ) (e z) := by
    intro ξ z
    induction z using Quotient.inductionOn with
    | h y => exact hn ξ y
  letI : T2Space (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    e.toHomeomorph.symm.t2Space
  letI : BorelSpace (KPCuspGenuineMonodromy.KernelTorus S D ρ) :=
    AddCosetSpace.borelSpace
  have hs := FullRealLatticeTorus.hasSum_sq_coefficients_of_coordinates
    e n (KPCuspFrequencyGap.torusMode S D ρ) hmode μ hμ hprob f hf
  exact ⟨hs.summable, hs.tsum_eq.symm⟩

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy.GapCoercivity.Fourier

end

end
