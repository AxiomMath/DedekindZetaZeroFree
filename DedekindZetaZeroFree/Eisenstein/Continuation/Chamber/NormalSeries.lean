module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RationalSummands.ParameterDerivatives

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators Manifold ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualChamberNormalSeries

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)

def E (s : ℂ) (g : G F ζ hζ) : ℂ := ∑' q : Q F, term F ζ hζ U ι f q s g

set_option maxHeartbeats 1200000 in
private theorem scalar_normal_majorant
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    ∃ b : Q F → ℝ≥0, Summable (fun q => (b q : ℝ)) ∧
      ∀ q s, s ∈ K → ∀ g ∈ A, ‖term F ζ hζ U ι f q s g‖ ≤ (b q : ℝ) := by
  let B := Module.finBasis ℂ S
  have hKΩ : K ⊆ KPContinuation.spectralDomain := by
    intro s hs
    have hh := hKV hs
    change (1 : ℝ) / 3 < s.re at hh
    change -(1 : ℝ) / 6 < s.re
    linarith
  have hcoef : ∀ i : Fin (Module.finrank ℂ S), ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ K, ‖B.repr (f s) i‖ ≤ C := by
    intro i
    have hcont : ContinuousOn (fun s => B.repr (f s) i) K :=
      (B.coord i).continuous_of_finiteDimensional.comp_continuousOn
        (hf.continuousOn.mono hKΩ)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
    exact ⟨max 0 C, le_max_left _ _, fun s hs => (hC s hs).trans (le_max_right _ _)⟩
  choose C hC hCb using hcoef
  let K₀ := (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K
  have hK₀ : KPLiteralRaw.IwasawaCompact F ζ hζ K₀ :=
    ⟨(KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).compact,
      (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).decomposition,
      KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ⟩
  have hmajor : ∀ i : Fin (Module.finrank ℂ S), ∃ b : Q F → ℝ,
      Summable b ∧ ∀ q s, s ∈ K → ∀ g ∈ A,
        ‖KPContActualSphericalFlatStage.L F ζ hζ U ι s (B i) (lift F ζ hζ q * g)‖ ≤ b q := by
    intro i
    obtain ⟨φ, hφ⟩ := KPContinuation.ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι (B i)
    obtain ⟨b, hb, hbound⟩ := KPLiteralChamber.chamber_scalar_compact_majorants
      F ζ hζ K₀ hK₀ φ K hK hKV A hA
    refine ⟨b, hb, ?_⟩
    intro q s hs g hg
    have hl : lift F ζ hζ q = KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) := by
      unfold lift KPContFlatRationalCosetCovariance.matrixRationalHom
      change KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F
          (Quotient.out q)) = _
      rw [KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift]
      exact (KPLiteralExceptionalResidue.rationalLift_eq_constructed F ζ hζ (Quotient.out q)).symm
    rw [hl, ← hφ]
    exact hbound q s hs g hg
  choose b hb hbound using hmajor
  let major : Q F → ℝ≥0 := fun q => ⟨∑ i, C i * |b i q|,
    Finset.sum_nonneg (fun i _ => mul_nonneg (hC i) (abs_nonneg _))⟩
  refine ⟨major, ?_, ?_⟩
  · change Summable (fun q => ∑ i : Fin (Module.finrank ℂ S), C i * |b i q|)
    exact summable_sum (fun i _ => (hb i).abs.mul_left (C i))
  · intro q s hs g hg
    have heq : term F ζ hζ U ι f q s g = ∑ i,
        B.repr (f s) i * KPContActualSphericalFlatStage.L F ζ hζ U ι s (B i) (lift F ζ hζ q * g) := by
      unfold term
      conv_lhs => rw [← B.sum_repr (f s)]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul]
    exact mul_le_mul (hCb i s hs) ((hbound i q s hs g hg).trans (le_abs_self _))
      (norm_nonneg _) (hC i)

private theorem term_holomorphic
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (g : G F ζ hζ) :
    DifferentiableOn ℂ (fun s => term F ζ hζ U ι f q s g) KPContinuation.spectralDomain := by
  let ev : S →ₗ[ℂ] ℂ :=
    (LinearMap.proj (lift F ζ hζ q * g)).comp
      (KPContActualSphericalFlatStage.L F ζ hζ U ι 0)
  have hev : DifferentiableOn ℂ (fun s => ev (f s)) KPContinuation.spectralDomain :=
    ((⟨ev, ev.continuous_of_finiteDimensional⟩ : S →L[ℂ] ℂ).differentiable.comp_differentiableOn hf)
  have heq : (fun s => term F ζ hζ U ι f q s g) = fun s =>
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ (lift F ζ hζ q * g) : ℂ)) *
        ev (f s) := by
    funext s
    simp only [term, ev, LinearMap.comp_apply, LinearMap.proj_apply,
      KPContFlatCommonLevelKernel.L_formula, zero_mul, Complex.exp_zero, one_mul]
  rw [heq]
  exact (Differentiable.differentiableOn (by fun_prop)).mul hev

private theorem term_continuous (q : Q F) (s : ℂ) :
    Continuous (term F ζ hζ U ι f q s) := by
  obtain ⟨φ, hφ⟩ := KPContinuation.ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι (f s)
  have hc : Continuous (fun g : G F ζ hζ => φ.val s (lift F ζ hζ q * g)) :=
    ((φ.property.1 s).1.1).comp (continuous_const.mul continuous_id)
  simp only [hφ] at hc
  exact hc

private theorem series_continuous
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (s : ℂ) (hs : s ∈ V) :
    Continuous (E F ζ hζ U ι f s) := by
  letI : LocallyCompactSpace (G F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨A, hA, hAg⟩ := exists_compact_mem_nhds g
  obtain ⟨b, hb, hbound⟩ := scalar_normal_majorant F ζ hζ U ι f hf
    {s} isCompact_singleton (by rintro z rfl; exact hs) A hA
  have hc := continuousOn_tsum (fun q => (term_continuous F ζ hζ U ι f q s).continuousOn)
    hb (fun q x hx => hbound q s rfl x hx)
  exact hc.continuousAt hAg

set_option maxHeartbeats 1200000 in
private theorem parameter_normal_majorant
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    ∃ b : Q F → ℝ≥0, Summable (fun q => (b q : ℝ)) ∧
      ∀ q s, s ∈ K → ∀ g ∈ A,
        ‖mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s g‖ ≤ (b q : ℝ) := by
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open KPChamberL2Defect.chamber_isOpen hKV
  obtain ⟨b, hb, hbound⟩ := scalar_normal_majorant F ζ hζ U ι f hf
    (Metric.cthickening r K) hK.cthickening hrV A hA
  let d : ℝ≥0 := ⟨(k.factorial : ℝ) / r^k, div_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.le _)⟩
  refine ⟨fun q => d * b q, hb.mul_left _, ?_⟩
  intro q s hs g hg
  have hball : Metric.closedBall s r ⊆ KPContinuation.spectralDomain := by
    intro z hz
    have hzV := hrV (Metric.closedBall_subset_cthickening hs r hz)
    change -(1 : ℝ)/6 < z.re
    change (1 : ℝ)/3 < z.re at hzV
    linarith
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
    ((term_holomorphic F ζ hζ U ι f hf q g).diffContOnCl_ball hball)
    (fun z hz => hbound q z (Metric.closedBall_subset_cthickening hs r
      (Metric.sphere_subset_closedBall hz)) g hg)
  change ‖iteratedDerivWithin k (fun z => term F ζ hζ U ι f q z g) V s‖ ≤ _
  rw [iteratedDerivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen (hKV hs)]
  change ‖iteratedDeriv k (fun z => term F ζ hζ U ι f q z g) s‖ ≤
    ((k.factorial : ℝ)/r^k) * (b q : ℝ)
  exact hc.trans_eq (by ring)

private theorem word_left_translate (w : Word F) (u : G F ζ hζ → ℂ) (a g : G F ζ hζ) :
    rightWord F ζ hζ w (fun x => u (a*x)) g = rightWord F ζ hζ w u (a*g) := by
  induction w generalizing u g with
  | nil => rfl
  | cons b w ih =>
    simp only [rightWord, List.foldr_cons, KPMsGreenFlux.rightDerivative]
    congr 1
    funext t
    change rightWord F ζ hζ w (fun x => u (a*x)) _ = rightWord F ζ hζ w u _
    rw [ih, mul_assoc]

set_option maxHeartbeats 1600000 in
private theorem spatial_normal_majorant
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (w : Word F) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    ∃ b : Q F → ℝ≥0, Summable (fun q => (b q : ℝ)) ∧
      ∀ q s, s ∈ K → ∀ g ∈ A, ‖mixedJet F ζ hζ (term F ζ hζ U ι f q) 0 w s g‖ ≤ (b q : ℝ) := by
  let B := Module.finBasis ℂ S
  have hKΩ : K ⊆ KPContinuation.spectralDomain := by
    intro s hs; have hh := hKV hs; change (1 : ℝ)/3 < s.re at hh
    change -(1 : ℝ)/6 < s.re; linarith
  have hcoef : ∀ i : Fin (Module.finrank ℂ S), ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖B.repr (f s) i‖ ≤ C := by
    intro i
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
      ((B.coord i).continuous_of_finiteDimensional.comp_continuousOn (hf.continuousOn.mono hKΩ))
    exact ⟨max 0 C, le_max_left _ _, fun s hs => (hC s hs).trans (le_max_right _ _)⟩
  choose C hC hCb using hcoef
  obtain ⟨n,a,j,_,heq⟩ := KPContinuation.ChamberFlatSource.actual_rightWord_jet_expansion_uniform F ζ hζ w
  let K₀ := (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K
  have hK₀ : KPLiteralRaw.IwasawaCompact F ζ hζ K₀ :=
    ⟨(KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).compact,
      (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).decomposition,
      KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ⟩
  have hmajor : ∀ ij : Fin n × Fin (Module.finrank ℂ S), ∃ b : Q F → ℝ, Summable b ∧
      ∀ q s, s ∈ K → ∀ g ∈ A, ‖KPLiteralChamber.rightJet F ζ hζ (j ij.1)
        (KPContActualSphericalFlatStage.L F ζ hζ U ι s (B ij.2)) (lift F ζ hζ q*g)‖ ≤ b q := by
    intro ij
    obtain ⟨φ,hφ⟩ := KPContinuation.ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι (B ij.2)
    obtain ⟨b,hb,hh⟩ := KPLiteralChamber.chamber_jet_majorants F ζ hζ K₀ hK₀ φ K hK hKV A hA (j ij.1)
    refine ⟨b,hb,?_⟩
    intro q s hs g hg
    have hl : lift F ζ hζ q = KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) := by
      unfold lift KPContFlatRationalCosetCovariance.matrixRationalHom
      change KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F (Quotient.out q)) = _
      rw [KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift]
      exact (KPLiteralExceptionalResidue.rationalLift_eq_constructed F ζ hζ (Quotient.out q)).symm
    have h := hh q s hs g hg
    rw [KPLiteralChamber.rightJet_compactExtension_rational_eq] at h
    have hfun : φ.val s = KPContActualSphericalFlatStage.L F ζ hζ U ι s (B ij.2) := funext (hφ s)
    simpa only [← hl, hfun] using h
  choose b hb hbound using hmajor
  let major : Q F → ℝ≥0 := fun q => ⟨∑ ij : Fin n × Fin (Module.finrank ℂ S),
    ‖a ij.1‖ * C ij.2 * |b ij q|,
    Finset.sum_nonneg (fun ij _ => mul_nonneg (mul_nonneg (norm_nonneg _) (hC _)) (abs_nonneg _))⟩
  refine ⟨major, ?_, ?_⟩
  · exact summable_sum (fun ij _ => (hb ij).abs.mul_left (‖a ij.1‖ * C ij.2))
  · intro q s hs g hg
    obtain ⟨φ,hφ⟩ := KPContinuation.ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι (f s)
    have hfun : φ.val s = KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s) := funext (hφ s)
    change ‖rightWord F ζ hζ w (fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s) (lift F ζ hζ q*x)) g‖ ≤ _
    rw [word_left_translate]
    change ‖w.foldr (fun b v => KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 v)
      (KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)) (lift F ζ hζ q*g)‖ ≤ _
    rw [← hfun, heq]
    have hj (i : Fin n) : KPLiteralChamber.rightJet F ζ hζ (j i) (φ.val s) (lift F ζ hζ q*g) =
        ∑ l, B.repr (f s) l * KPLiteralChamber.rightJet F ζ hζ (j i)
          (KPContActualSphericalFlatStage.L F ζ hζ U ι s (B l)) (lift F ζ hζ q*g) := by
      rw [hfun]
      have hsmooth (l : Fin (Module.finrank ℂ S)) : ContDiffAt ℝ ((j i).1 : WithTop ℕ∞)
          (fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s (B l)
            ((lift F ζ hζ q*g)*KPGlobalResidualConstruction.archChart F ζ hζ x))
            (KPGlobalResidualConstruction.archBase F) := by
        obtain ⟨ψ,hψ⟩ := KPContinuation.ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι (B l)
        have hbase : KPGlobalResidualConstruction.archBase F ∈ KPGlobalResidualConstruction.archDomain F := by
          intro w; simp [KPGlobalResidualConstruction.archBase]
        have hh : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x => ψ.val s ((lift F ζ hζ q*g)*KPGlobalResidualConstruction.archChart F ζ hζ x))
            (KPGlobalResidualConstruction.archBase F) :=
          ((ψ.property.1 s).1.2.1 (lift F ζ hζ q*g)).contDiffAt
            ((KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F).mem_nhds hbase)
        have hh' := hh.of_le (show ((j i).1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)
        simpa only [hψ] using hh'
      unfold KPLiteralChamber.rightJet
      have hsum : (fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
          ((lift F ζ hζ q*g)*KPGlobalResidualConstruction.archChart F ζ hζ x)) =
          fun x => ∑ l, B.repr (f s) l * KPContActualSphericalFlatStage.L F ζ hζ U ι s (B l)
            ((lift F ζ hζ q*g)*KPGlobalResidualConstruction.archChart F ζ hζ x) := by
        funext x
        conv_lhs => rw [← B.sum_repr (f s)]
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsum]
      have hsm (l : Fin (Module.finrank ℂ S)) : ContDiffAt ℝ ((j i).1 : WithTop ℕ∞)
          (fun x => B.repr (f s) l * KPContActualSphericalFlatStage.L F ζ hζ U ι s (B l)
            ((lift F ζ hζ q*g)*KPGlobalResidualConstruction.archChart F ζ hζ x))
            (KPGlobalResidualConstruction.archBase F) := by
        simpa only [smul_eq_mul] using (hsmooth l).const_smul (B.repr (f s) l)
      rw [iteratedFDeriv_fun_sum_apply (fun l _ => hsm l)]
      simp only [ContinuousMultilinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro l _
      change (iteratedFDeriv ℝ (j i).1
        ((B.repr (f s) l) • (fun x => KPContActualSphericalFlatStage.L F ζ hζ U ι s (B l)
          ((lift F ζ hζ q*g)*KPGlobalResidualConstruction.archChart F ζ hζ x))) _ _) = _
      rw [iteratedFDeriv_const_smul_apply (hsmooth l)]
      rfl
    simp_rw [hj, Finset.mul_sum]
    rw [← Finset.sum_product']
    apply (norm_sum_le _ _).trans
    change ∑ ij : Fin n × Fin (Module.finrank ℂ S), ‖_‖ ≤ ∑ ij, ‖a ij.1‖ * C ij.2 * |b ij q|
    apply Finset.sum_le_sum
    intro ij _
    rw [norm_mul, norm_mul, Complex.norm_real]
    calc
      _ ≤ ‖a ij.1‖ * (C ij.2 * |b ij q|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hCb ij.2 s hs)
          ((hbound ij q s hs g hg).trans (le_abs_self _)) (norm_nonneg _) (hC _)) (norm_nonneg _)
      _ = _ := by ring

set_option maxHeartbeats 1200000 in

theorem normal_majorant (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    ∃ b : Q F → ℝ≥0, Summable (fun q => (b q : ℝ)) ∧
      ∀ (q : Q F) (s : ℂ), s ∈ K → ∀ g ∈ A,
        ‖mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g‖ ≤ (b q : ℝ) := by
  by_cases hk : k = 0
  · subst k
    by_cases hw : w = []
    · subst w
      change ∃ b : Q F → ℝ≥0, Summable (fun q => (b q : ℝ)) ∧
        ∀ (q : Q F) (s : ℂ), s ∈ K → ∀ g ∈ A,
          ‖term F ζ hζ U ι f q s g‖ ≤ (b q : ℝ)
      exact scalar_normal_majorant F ζ hζ U ι f hf K hK hKV A hA
    · exact spatial_normal_majorant F ζ hζ U ι f hf w K hK hKV A hA
  · by_cases hw : w = []
    · subst w
      exact parameter_normal_majorant F ζ hζ U ι f hf k K hK hKV A hA
    · obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open KPChamberL2Defect.chamber_isOpen hKV
      obtain ⟨b, hb, hbound⟩ := spatial_normal_majorant F ζ hζ U ι f hf w
        (Metric.cthickening r K) hK.cthickening hrV A hA
      let d : ℝ≥0 := ⟨(k.factorial : ℝ) / r^k, div_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.le _)⟩
      refine ⟨fun q => d * b q, hb.mul_left _, ?_⟩
      intro q s hs g hg
      have hd : DifferentiableOn ℂ (fun z => rightWord F ζ hζ w (term F ζ hζ U ι f q z) g) V := by
        intro z hz
        have hh := (KPContinuation.ChamberNormalTerm.actual_term_word_parameter F ζ hζ U ι f hι hf q 0 w z hz g).2
        simpa only [mixedJet, iteratedDerivWithin_zero] using hh.differentiableAt.differentiableWithinAt
      have hball : Metric.closedBall s r ⊆ V := fun z hz => hrV (Metric.closedBall_subset_cthickening hs r hz)
      have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr
        (hd.diffContOnCl_ball hball)
        (fun z hz => hbound q z (Metric.closedBall_subset_cthickening hs r
          (Metric.sphere_subset_closedBall hz)) g hg)
      rw [← (KPContinuation.ChamberNormalTerm.actual_term_word_parameter F ζ hζ U ι f hι hf q k w s (hKV hs) g).1,
        iteratedDerivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen (hKV hs)]
      exact hc.trans_eq (by change _ = ((k.factorial : ℝ)/r^k) * (b q : ℝ); ring)

theorem mixed_summable (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    Summable (fun q : Q F => ‖mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g‖) := by
  obtain ⟨b, hb, hbound⟩ :=
    normal_majorant F ζ hζ U ι f hι hf k w {s} isCompact_singleton
      (by rintro x rfl; exact hs) {g} isCompact_singleton
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (fun q => hbound q s rfl g rfl) hb

private theorem parameterJet_eq_tsum
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    mixedJet F ζ hζ (E F ζ hζ U ι f) k [] s g =
      ∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k [] s g := by
  change iteratedDerivWithin k (fun z => ∑' q : Q F, term F ζ hζ U ι f q z g) V s = _
  apply iteratedDerivWithin_tsum k KPChamberL2Defect.chamber_isOpen hs
  · intro z hz
    obtain ⟨b, hb, hbound⟩ := scalar_normal_majorant F ζ hζ U ι f hf
      {z} isCompact_singleton (by rintro x rfl; exact hz) {g} isCompact_singleton
    exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => hbound q z rfl g rfl) hb).of_norm
  · intro j _ _
    apply SummableLocallyUniformlyOn_of_locally_bounded KPChamberL2Defect.chamber_isOpen
    intro K hKV hK
    obtain ⟨b, hb, hbound⟩ := parameter_normal_majorant F ζ hζ U ι f hf j K hK hKV
      {g} isCompact_singleton
    exact ⟨fun q => (b q : ℝ), hb, fun q z hz => hbound q z hz g rfl⟩
  · intro q j z _ hz
    have hd := ((term_holomorphic F ζ hζ U ι f hf q g).mono (show V ⊆ KPContinuation.spectralDomain from by
      intro x hx; change -(1 : ℝ)/6 < x.re; change (1 : ℝ)/3 < x.re at hx; linarith))
    exact ((hd.contDiffOn (n := ⊤) KPChamberL2Defect.chamber_isOpen).differentiableOn_iteratedDerivWithin
      (by simp) KPChamberL2Defect.chamber_isOpen.uniqueDiffOn).differentiableAt
        (KPChamberL2Defect.chamber_isOpen.mem_nhds hz)

private theorem term_flow_deriv
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (q : Q F) (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V)
    (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ) (t : ℝ) :
    HasDerivAt (fun r => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b r)))
      (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s
        (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t))) t := by
  let a := fun r => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b r)
  have hadd (x y : ℝ) : a (x+y) = a x*a y := by
    dsimp only [a]
    rw [(KPSmoothActualFlowData.flow_properties F b).2.1,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hh := (KPContinuation.ChamberNormalTerm.actual_term_mixed_flow F ζ hζ U ι f hι hf q k w s hs).2 b (g*a t)
  have hh' : HasDerivAt (fun r => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s ((g*a t)*a r))
    (mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s (g*a t)) (t-t) := by
    simpa only [sub_self] using hh
  have hc := hh'.comp_sub_const t t
  simpa only [Function.comp_def, sub_self, mul_assoc, ← hadd, add_sub_cancel] using hc

private theorem flow_tsum_hasDeriv
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V)
    (b : KPSmoothActualFlowData.B F) (g : G F ζ hζ) :
    HasDerivAt (fun t => ∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)))
      (∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k (b :: w) s g) 0 := by
  let a := fun t : ℝ => g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)
  have ha : Continuous a := continuous_const.mul
    ((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
      (KPSmoothActualFlowData.flow_properties F b).2.2)
  obtain ⟨c, hc, hbound⟩ := normal_majorant F ζ hζ U ι f hι hf k (b :: w)
    {s} isCompact_singleton (by rintro z rfl; exact hs)
    (a '' Metric.closedBall 0 1) ((isCompact_closedBall (0 : ℝ) 1).image ha)
  have h0 : a 0 = g := by
    simp only [a, (KPSmoothActualFlowData.flow_properties F b).1,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, mul_one]
  have H := hasDerivAt_tsum_of_isPreconnected hc Metric.isOpen_ball (convex_ball (0 : ℝ) 1).isPreconnected
    (fun q t ht => term_flow_deriv F ζ hζ U ι f hι hf q k w s hs b g t)
    (fun q t ht => hbound q s rfl (a t) ⟨t, Metric.ball_subset_closedBall ht, rfl⟩)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
    (show Summable (fun q : Q F => mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s (a 0)) from
      h0.symm ▸ (mixed_summable F ζ hζ U ι f hι hf k w s hs g).of_norm)
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  simpa only [(KPSmoothActualFlowData.flow_properties F b).1,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, mul_one] using H

theorem mixedJet_eq_tsum (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    mixedJet F ζ hζ (E F ζ hζ U ι f) k w s g =
      ∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g := by
  induction w generalizing g with
  | nil => exact parameterJet_eq_tsum F ζ hζ U ι f hf k s hs g
  | cons b w ih =>
    change deriv (fun t : ℝ => mixedJet F ζ hζ (E F ζ hζ U ι f) k w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t))) 0 = _
    simp_rw [ih]
    exact (flow_tsum_hasDeriv F ζ hζ U ι f hι hf k w s hs b g).deriv

private theorem parameter_tsum_hasDeriv
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    HasDerivAt (fun z => ∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w z g)
      (∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) (k+1) w s g) s := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp KPChamberL2Defect.chamber_isOpen s hs
  obtain ⟨c, hc, hbound⟩ := normal_majorant F ζ hζ U ι f hι hf (k+1) w
    (Metric.closedBall s (r/2)) (isCompact_closedBall s (r/2))
    (fun z hz => hrV (Metric.mem_ball.mpr (lt_of_le_of_lt hz (by linarith))))
    {g} isCompact_singleton
  exact hasDerivAt_tsum_of_isPreconnected hc Metric.isOpen_ball (convex_ball s (r/2)).isPreconnected
    (fun q z hz => KPContinuation.ChamberNormalTerm.actual_mixedTerm_hasDeriv F ζ hζ U ι f hf q k w z
      (hrV (Metric.mem_ball.mpr (lt_trans hz (by linarith)))) g)
    (fun q z hz => hbound q z (Metric.ball_subset_closedBall hz) g rfl)
    (Metric.mem_ball_self (by linarith : (0 : ℝ) < r/2))
    (mixed_summable F ζ hζ U ι f hι hf k w s hs g).of_norm
    (Metric.mem_ball_self (by linarith : (0 : ℝ) < r/2))

private theorem mixedSeries_hasDeriv
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    HasDerivAt (fun z => mixedJet F ζ hζ (E F ζ hζ U ι f) k w z g)
      (mixedJet F ζ hζ (E F ζ hζ U ι f) (k+1) w s g) s := by
  have hh := parameter_tsum_hasDeriv F ζ hζ U ι f hι hf k w s hs g
  rw [← mixedJet_eq_tsum F ζ hζ U ι f hι hf (k+1) w s hs g] at hh
  exact hh.congr_of_eventuallyEq (Filter.Eventually.mono (KPChamberL2Defect.chamber_isOpen.mem_nhds hs)
    (fun z hz => mixedJet_eq_tsum F ζ hζ U ι f hι hf k w z hz g))

theorem mixedJet_commute (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) (g : G F ζ hζ) :
    iteratedDerivWithin k (fun z => rightWord F ζ hζ w (E F ζ hζ U ι f z) g) V s =
      mixedJet F ζ hζ (E F ζ hζ U ι f) k w s g := by
  induction k generalizing s with
  | zero => simp only [iteratedDerivWithin_zero, mixedJet]
  | succ k ih =>
    rw [iteratedDerivWithin_succ, derivWithin_congr (fun z hz => ih z hz) (ih s hs)]
    exact (mixedSeries_hasDeriv F ζ hζ U ι f hι hf k w s hs g).hasDerivWithinAt.derivWithin
      (KPChamberL2Defect.chamber_isOpen.uniqueDiffWithinAt hs)

theorem mixed_uniform (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    TendstoUniformlyOn
      (fun J : Finset (Q F) => fun p : ℂ × G F ζ hζ =>
        ∑ q ∈ J, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w p.1 p.2)
      (fun p => mixedJet F ζ hζ (E F ζ hζ U ι f) k w p.1 p.2)
      Filter.atTop (K ×ˢ A) := by
  obtain ⟨b, hb, hbound⟩ :=
    normal_majorant F ζ hζ U ι f hι hf k w K hK hKV A hA
  have h := tendstoUniformlyOn_tsum
    (f := fun q (p : ℂ × G F ζ hζ) =>
      mixedJet F ζ hζ (term F ζ hζ U ι f q) k w p.1 p.2)
    (u := fun q : Q F => (b q : ℝ)) hb (s := K ×ˢ A)
    (fun q p hp => hbound q p.1 hp.1 p.2 hp.2)
  refine h.congr_right ?_
  intro p hp
  exact (mixedJet_eq_tsum F ζ hζ U ι f hι hf k w p.1 (hKV hp.1) p.2).symm

theorem mixedJet_continuous (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (s : ℂ) (hs : s ∈ V) :
    Continuous (mixedJet F ζ hζ (E F ζ hζ U ι f) k w s) := by
  letI : LocallyCompactSpace (G F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  have heq : mixedJet F ζ hζ (E F ζ hζ U ι f) k w s = fun g =>
      ∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g :=
    funext (mixedJet_eq_tsum F ζ hζ U ι f hι hf k w s hs)
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro g
  obtain ⟨A, hA, hAg⟩ := exists_compact_mem_nhds g
  obtain ⟨b, hb, hbound⟩ := normal_majorant F ζ hζ U ι f hι hf k w
    {s} isCompact_singleton (by rintro z rfl; exact hs) A hA
  exact (continuousOn_tsum
    (fun q => (KPContinuation.ChamberNormalTerm.actual_term_mixed_flow F ζ hζ U ι f hι hf q k w s hs).1.continuousOn)
    hb (fun q x hx => hbound q s rfl x hx)).continuousAt hAg

theorem smooth (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (s : ℂ) (hs : s ∈ V) :
    KPMsGreenFlux.Smooth F ζ hζ (E F ζ hζ U ι f s) := by
  refine ⟨series_continuous F ζ hζ U ι f hf s hs, ?_⟩
  intro g
  obtain ⟨C, hC⟩ := KPSmoothActualFlowData.actual_archimedean_lie_data F
  letI := C
  obtain ⟨L, D, hD, hbasis, _⟩ := hC
  letI := L
  let q := fun (w : Word F) (a : KPSmoothActualFlowData.GInfinity F) =>
    mixedJet F ζ hζ (E F ζ hζ U ι f) 0 w s
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)
  have hflow (b : KPSmoothActualFlowData.B F) (t : ℝ) :
      D.exponential (t • D.basis b) = KPSmoothActualFlowData.flow F b t := by
    rw [hD]
    congr 1
    funext c
    simp only [Pi.smul_apply, hbasis, smul_eq_mul]
    split_ifs <;> simp
  have hder (w : Word F) (b : KPSmoothActualFlowData.B F) (a : KPSmoothActualFlowData.GInfinity F) :
      HasDerivAt (fun t : ℝ => q w (a * D.exponential (t • D.basis b))) (q (b :: w) a) 0 := by
    have hh := flow_tsum_hasDeriv F ζ hζ U ι f hι hf 0 w s hs b
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)
    have heq (t : ℝ) : q w (a * D.exponential (t • D.basis b)) =
        ∑' r : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f r) 0 w s
          ((g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) *
            KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (KPSmoothActualFlowData.flow F b t)) := by
      dsimp [q]
      rw [hflow, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1, ← mul_assoc,
        mixedJet_eq_tsum F ζ hζ U ι f hι hf 0 w s hs]
    rw [← mixedJet_eq_tsum F ζ hζ U ι f hι hf 0 (b :: w) s hs] at hh
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  have hq (n : ℕ) : ∀ w, ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) 𝓘(ℝ, ℂ) n (q w) := by
    induction n with
    | zero =>
      intro w
      apply contMDiff_zero_iff.mpr
      exact (mixedJet_continuous F ζ hζ U ι f hι hf 0 w s hs).comp
        (show Continuous (fun a : KPSmoothActualFlowData.GInfinity F =>
          g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) from
          continuous_const.mul (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1)
    | succ n ih =>
      intro w
      exact SmoothWordOrbit.DomainToSmooth.contMDiff_succ_of_translated_basis_derivatives
        D.basis D.exponential D.exponential_zero D.exponential_add_ray D.exponential_smooth
        D.exponentialChart D.zero_mem_source D.chart_eq_exponential n (q w) (fun b => q (b::w))
        ((mixedJet_continuous F ζ hζ U ι f hι hf 0 w s hs).comp
          (continuous_const.mul (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1))
        (fun b => ih (b::w)) (hder w)
  have htop : ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (q []) :=
    contMDiff_infty.mpr (fun n => hq n [])
  have he : ContMDiff 𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F)
      𝓘(ℝ, KPSmoothActualFlowData.LieCoordinates F) (⊤ : ℕ∞) (KPSmoothActualFlowData.exponential F) :=
    hD ▸ D.exponential_smooth
  exact (htop.comp he).contDiff

def compactMixedJet (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (A : Set (G F ζ hζ)) (s : ℂ) : C(A, ℂ) :=
  if hs : s ∈ V then
    ⟨fun g => mixedJet F ζ hζ (E F ζ hζ U ι f) k w s g.val,
      (mixedJet_continuous F ζ hζ U ι f hι hf k w s hs).comp continuous_subtype_val⟩
  else 0

private theorem mixedSeries_bound
    (hι : Function.Injective ι) (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ V)
    (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ g ∈ A,
      ‖mixedJet F ζ hζ (E F ζ hζ U ι f) k w z g‖ ≤ B := by
  obtain ⟨b, hb, hbound⟩ := normal_majorant F ζ hζ U ι f hι hf k w K hK hKV A hA
  refine ⟨∑' q, (b q : ℝ), tsum_nonneg (fun q => (b q).property), ?_⟩
  intro z hz g hg
  rw [mixedJet_eq_tsum F ζ hζ U ι f hι hf k w z (hKV hz) g]
  exact (norm_tsum_le_tsum_norm (mixed_summable F ζ hζ U ι f hι hf k w z (hKV hz) g)).trans
    (Summable.tsum_le_tsum (fun q => hbound q z hz g hg)
      (mixed_summable F ζ hζ U ι f hι hf k w z (hKV hz) g) hb)

private theorem complex_taylor_bound
    (H H₁ H₂ : ℂ → ℂ) (s : ℂ) (r : ℝ) (hr : 0 < r) (B : ℝ)
    (hd : ∀ z ∈ Metric.closedBall s r, HasDerivAt H (H₁ z) z)
    (hd₁ : ∀ z ∈ Metric.closedBall s r, HasDerivAt H₁ (H₂ z) z)
    (hB : ∀ z ∈ Metric.closedBall s r, ‖H₂ z‖ ≤ B)
    (t : ℂ) (ht : t ∈ Metric.closedBall s r) :
    ‖H t - H s - (t-s) * H₁ s‖ ≤ B * ‖t-s‖ * ‖t-s‖ := by
  have hs : s ∈ Metric.closedBall s r := Metric.mem_closedBall_self hr.le
  have hseg : segment ℝ s t ⊆ Metric.closedBall s r := (convex_closedBall s r).segment_subset hs ht
  have hdiff (z : ℂ) (hz : z ∈ segment ℝ s t) : ‖H₁ z - H₁ s‖ ≤ B * ‖t-s‖ := by
    have hh := (convex_closedBall s r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := H₁) (f' := fun z => ContinuousLinearMap.toSpanSingleton ℂ (H₂ z))
      (fun z hz => (hd₁ z hz).hasFDerivAt.hasFDerivWithinAt)
      (fun z hz => by simpa only [ContinuousLinearMap.norm_toSpanSingleton] using hB z hz)
      hs (hseg hz)
    exact hh.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz)
      ((norm_nonneg (H₂ s)).trans (hB s hs)))
  have hh := (convex_segment s t).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := H) (f' := fun z => ContinuousLinearMap.toSpanSingleton ℂ (H₁ z))
    (φ := ContinuousLinearMap.toSpanSingleton ℂ (H₁ s))
    (fun z hz => (hd z (hseg hz)).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => by
      have he : ContinuousLinearMap.toSpanSingleton ℂ (H₁ z) - ContinuousLinearMap.toSpanSingleton ℂ (H₁ s) =
          ContinuousLinearMap.toSpanSingleton ℂ (H₁ z - H₁ s) := by ext c; simp [smul_sub]
      rw [he, ContinuousLinearMap.norm_toSpanSingleton]
      exact hdiff z hz)
    (left_mem_segment ℝ s t) (right_mem_segment ℝ s t)
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hh

theorem compactMixedJet_holomorphic (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (k : ℕ) (w : Word F) (A : Set (G F ζ hζ)) (hA : IsCompact A) :
    letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
    DifferentiableOn ℂ (compactMixedJet F ζ hζ U ι f hι hf k w A) V := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  intro s hs
  have hd : HasDerivAt (compactMixedJet F ζ hζ U ι f hι hf k w A)
      (compactMixedJet F ζ hζ U ι f hι hf (k+1) w A s) s := by
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp KPChamberL2Defect.chamber_isOpen s hs
    have hball : Metric.closedBall s (r/2) ⊆ V :=
      fun z hz => hrV (Metric.mem_ball.mpr (lt_of_le_of_lt hz (by linarith)))
    obtain ⟨B, hB, hb⟩ := mixedSeries_bound F ζ hζ U ι f hι hf (k+1+1) w
      (Metric.closedBall s (r/2)) (isCompact_closedBall s (r/2)) hball A hA
    apply HasDerivAt.of_isLittleO
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hδ : 0 < min (r/2) (c / (B+1)) := lt_min (by linarith)
      (div_pos hc (by linarith))
    filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
    have htr : ‖t-s‖ < r/2 := lt_of_lt_of_le (by simpa only [Metric.mem_ball, dist_eq_norm] using ht) (min_le_left _ _)
    have htc : ‖t-s‖ < c/(B+1) := lt_of_lt_of_le
      (by simpa only [Metric.mem_ball, dist_eq_norm] using ht) (min_le_right _ _)
    have htV := hball (Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using htr.le))
    apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg (t-s)))).mpr
    intro g
    have he (j : ℕ) (z : ℂ) (hz : z ∈ V) :
        compactMixedJet F ζ hζ U ι f hι hf j w A z g =
          mixedJet F ζ hζ (E F ζ hζ U ι f) j w z g.val := by
      simp only [compactMixedJet, dif_pos hz]
      rfl
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
      he k t htV, he k s hs, he (k+1) s hs]
    have hh := complex_taylor_bound
      (fun z => mixedJet F ζ hζ (E F ζ hζ U ι f) k w z g.val)
      (fun z => mixedJet F ζ hζ (E F ζ hζ U ι f) (k+1) w z g.val)
      (fun z => mixedJet F ζ hζ (E F ζ hζ U ι f) (k+1+1) w z g.val)
      s (r/2) (by linarith) B
      (fun z hz => mixedSeries_hasDeriv F ζ hζ U ι f hι hf k w z (hball hz) g.val)
      (fun z hz => mixedSeries_hasDeriv F ζ hζ U ι f hι hf (k+1) w z (hball hz) g.val)
      (fun z hz => hb z hz g.val g.property) t
      (Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using htr.le))
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hh' : (B+1)*‖t-s‖ < c := by
      simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < B+1)).mp htc
    nlinarith [norm_nonneg (t-s)]
  exact hd.differentiableAt.differentiableWithinAt

 def cosetRight (γ : Matrix.ProjGenLinGroup (Fin 2) F) : Q F ≃ Q F :=
  Quotient.congr (Equiv.mulRight γ) (by
    intro a b
    simp only [QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F ↔
      (b * γ) * (a * γ)⁻¹ ∈ KPChamberBruhatTwoCells.rationalBorel F
    simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left])

private theorem term_coset (s : ℂ) (g : G F ζ hζ)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    term F ζ hζ U ι f (KPChamberBruhatTwoCells.rationalCoset F γ) s g =
      KPContActualSphericalFlatStage.L F ζ hζ U ι s (f s)
        (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ γ * g) := by
  have h := KPContFlatRationalCosetCovariance.rationalTerm_transport_mk F ζ hζ s
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι (f s)) g γ
  rw [KPContFlatRationalCosetCovariance.rationalTerm_transport] at h
  exact h

theorem covariance (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (s : ℂ) (hs : s ∈ V) :
    (∀ (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ),
      E F ζ hζ U ι f s (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ γ * g) =
        E F ζ hζ U ι f s g) ∧
    (∀ (ε : rootsOfUnity 3 F) (g : G F ζ hζ),
      E F ζ hζ U ι f s (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * E F ζ hζ U ι f s g) ∧
    (∀ (g : G F ζ hζ) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      E F ζ hζ U ι f s (g * u.val) = E F ζ hζ U ι f s g) ∧
    (∀ (g : G F ζ hζ) (k : KPContSectorArchSphericalFibers.KInfinity F),
      E F ζ hζ U ι f s (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
        E F ζ hζ U ι f s g) := by
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ) / 6 < s.re
    change (1 : ℝ) / 3 < s.re at hs
    linarith
  obtain ⟨hU, hK, hχ, hB, hInd⟩ :=
    KPContActualSphericalFlatStage.covariance F ζ hζ U ι s hsΩ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ g
    let e := cosetRight F γ
    unfold E
    rw [← e.tsum_eq (fun q => term F ζ hζ U ι f q s g)]
    apply tsum_congr
    intro q
    have he : e q = KPChamberBruhatTwoCells.rationalCoset F (Quotient.out q * γ) := by
      change cosetRight F γ q = _
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [he, term_coset F ζ hζ U ι f, map_mul, mul_assoc]
    rfl
  · intro ε g
    have hc : ∀ x : G F ζ hζ,
        x * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * x := by
      intro x
      exact Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
          (show KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε ∈
            (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ).range from ⟨ε, rfl⟩)) x
    unfold E
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    unfold term
    rw [← mul_assoc, hc, mul_assoc, hχ]
  · intro g u
    unfold E
    apply tsum_congr
    intro q
    unfold term
    rw [← mul_assoc, hU]
  · intro g k
    unfold E
    apply tsum_congr
    intro q
    unfold term
    rw [← mul_assoc, hK]

abbrev atlasLevel :=
  let _ := C; let _ := R; let _ := P; let _ := H
  EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U

def coveredRepresentative
    (x : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ
      (atlasLevel F ζ hζ C R P H U)) : G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (Quotient.out x).1) *
      ((Quotient.out x).2 : G F ζ hζ)

theorem coveredRepresentative_projection
    (x : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ
      (atlasLevel F ζ hζ C R P H U)) :
    KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
      (atlasLevel F ζ hζ C R P H U)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (coveredRepresentative F ζ hζ C R P H U x)) = x := by
  unfold coveredRepresentative
  rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap]
  rw [KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
  exact Quotient.out_eq x

def componentRepresentative (i : Fin (H.atlas (atlasLevel F ζ hζ C R P H U)).componentCount)
    (x : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F) : G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ x) *
      ((H.atlas (atlasLevel F ζ hζ C R P H U)).representative i : G F ζ hζ)

set_option maxHeartbeats 800000 in

theorem descent_series (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) :
    ∃ e : ℂ → KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
        (atlasLevel F ζ hζ C R P H U),
      (∀ (s : ℂ), s ∈ V → ∀ (g : G F ζ hζ),
        (e s).val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
          (atlasLevel F ζ hζ C R P H U)
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = E F ζ hζ U ι f s g) ∧
      (∀ (s : ℂ), s ∈ V → ∀ x,
        (e s).val x = KPChamberL2Defect.series (lift F ζ hζ)
          (coveredRepresentative F ζ hζ C R P H U)
          (KPContActualSphericalFlatStage.L F ζ hζ U ι) f s x) ∧
      (∀ (s : ℂ), s ∈ V → ∀ i x,
        (KPContSectorScalarLineAlgebra.S F ζ hζ
          (atlasLevel F ζ hζ C R P H U) R P H (e s) i).val x =
            KPChamberL2Defect.series (lift F ζ hζ)
              (componentRepresentative F ζ hζ C R P H U i)
              (KPContActualSphericalFlatStage.L F ζ hζ U ι) f s x) := by
  let U₀ := atlasLevel F ζ hζ C R P H U
  have hex : ∀ s ∈ V, ∃ e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U₀,
      ∀ g, e.val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = E F ζ hζ U ι f s g := by
    intro s hs
    obtain ⟨hr, hc, hu, hk⟩ := covariance F ζ hζ U ι f hι hf s hs
    have hΓ : ∀ a ∈ KPContSectorCoveredQuotientVocabulary.Gamma F ζ hζ, ∀ g,
        E F ζ hζ U ι f s (a * g) = E F ζ hζ U ι f s g := by
      intro a ha g
      obtain ⟨γ, rfl⟩ := ha
      let γ₀ := (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).symm γ
      have hh := hr γ₀ g
      simpa [γ₀, KPContFlatRationalCosetCovariance.matrixRationalHom] using hh
    have hKU : ∀ a ∈ KPContSectorCoveredQuotientVocabulary.K_U F ζ hζ U₀, ∀ g,
        E F ζ hζ U ι f s (g * a) = E F ζ hζ U ι f s g := by
      intro a ha
      induction ha using Subgroup.closure_induction with
      | mem x hx =>
          rcases hx with hx | hx
          · obtain ⟨k, hkmem, rfl⟩ := hx
            exact fun g => hk g ⟨k, hkmem⟩
          · obtain ⟨u, humem, rfl⟩ := hx
            have huval : (u : G F ζ hζ) ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U := by
              rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U]
              exact ⟨u, humem, rfl⟩
            exact fun g => hu g ⟨u, huval⟩
      | one => intro g; simp
      | mul x y hx hy ihx ihy => intro g; rw [← mul_assoc, ihy, ihx]
      | inv x hx ih =>
          intro g
          have hh := ih (g * x⁻¹)
          simpa only [inv_mul_cancel_right] using hh.symm
    let d : KPContSectorCoveredQuotientVocabulary.CoveredActual F ζ hζ U₀ → ℂ :=
      Quotient.lift (E F ζ hζ U ι f s) (by
        intro a b hab
        obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.rel_iff.mp hab
        rw [hKU y hy, hΓ x hx])
    let v : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U₀ → ℂ :=
      d ∘ (KPContSectorQuotientRelationsComparison.e F ζ hζ U₀).symm
    have hv : ∀ g, v (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = E F ζ hζ U ι f s g := by
      intro g
      dsimp [v, KPContSectorQuotientRelationsComparison.piTilde]
      rw [Homeomorph.symm_apply_apply]
      rfl
    refine ⟨⟨v, ?_⟩, hv⟩
    intro ε x
    obtain ⟨y, rfl⟩ := KPContSectorQuotientRelationsComparison.piTilde_surjective F ζ hζ U₀ x
    obtain ⟨g, rfl⟩ := Quotient.exists_rep y
    have hp := congrFun (KPContSectorCentralHaarInvariance.piTilde_t F ζ hζ U₀ ε)
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)
    dsimp [Function.comp_def] at hp
    change v (KPContSectorCoveredQuotientVocabulary.z F ζ hζ U₀ ε
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
        v (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))
    rw [← hp, KPContSectorCentralHaarInvariance.t_quotientMap, hv, hv]
    have hcomm : g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
        KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g :=
      Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) g
    rw [hcomm, hc]
  let e := fun s => if hs : s ∈ V then (hex s hs).choose else 0
  have he : ∀ s ∈ V, ∀ g, (e s).val
      (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = E F ζ hζ U ι f s g := by
    intro s hs g
    dsimp [e]
    rw [dif_pos hs]
    exact (hex s hs).choose_spec g
  refine ⟨e, he, ?_, ?_⟩
  · intro s hs x
    calc
      (e s).val x = (e s).val
          (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
            (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
              (coveredRepresentative F ζ hζ C R P H U x))) :=
        congrArg (e s).val (coveredRepresentative_projection F ζ hζ C R P H U x).symm
      _ = E F ζ hζ U ι f s (coveredRepresentative F ζ hζ C R P H U x) := he s hs _
      _ = _ := rfl
  · intro s hs i x
    rw [KPContSectorScalarLineAlgebra.S_apply]
    have hp : KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U₀
        (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
          (componentRepresentative F ζ hζ C R P H U i x)) =
        Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ U₀)
          (x, (H.atlas U₀).representative i) := by
      unfold componentRepresentative
      rw [KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
        KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection]
    rw [← hp, he s hs]
    rfl

structure ChamberConclusions (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) : Prop where
  majorant : ∀ (k : ℕ) (w : Word F) (K : Set ℂ), IsCompact K → K ⊆ V →
    ∀ (A : Set (G F ζ hζ)), IsCompact A →
    ∃ b : Q F → ℝ≥0, Summable (fun q => (b q : ℝ)) ∧
      ∀ (q : Q F) (s : ℂ), s ∈ K → ∀ g ∈ A,
        ‖mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g‖ ≤ (b q : ℝ)
  absolute : ∀ (k : ℕ) (w : Word F) (s : ℂ), s ∈ V → ∀ (g : G F ζ hζ),
    Summable (fun q : Q F => ‖mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g‖)
  termwise : ∀ (k : ℕ) (w : Word F) (s : ℂ), s ∈ V → ∀ (g : G F ζ hζ),
    mixedJet F ζ hζ (E F ζ hζ U ι f) k w s g =
      ∑' q : Q F, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w s g
  commute : ∀ (k : ℕ) (w : Word F) (s : ℂ), s ∈ V → ∀ (g : G F ζ hζ),
    iteratedDerivWithin k (fun z => rightWord F ζ hζ w (E F ζ hζ U ι f z) g) V s =
      mixedJet F ζ hζ (E F ζ hζ U ι f) k w s g
  uniform : ∀ (k : ℕ) (w : Word F) (K : Set ℂ), IsCompact K → K ⊆ V →
    ∀ (A : Set (G F ζ hζ)), IsCompact A →
    TendstoUniformlyOn
      (fun J : Finset (Q F) => fun p : ℂ × G F ζ hζ =>
        ∑ q ∈ J, mixedJet F ζ hζ (term F ζ hζ U ι f q) k w p.1 p.2)
      (fun p => mixedJet F ζ hζ (E F ζ hζ U ι f) k w p.1 p.2)
      Filter.atTop (K ×ˢ A)
  smooth : ∀ (s : ℂ), s ∈ V → KPMsGreenFlux.Smooth F ζ hζ (E F ζ hζ U ι f s)
  compact_holomorphic : ∀ (k : ℕ) (w : Word F) (A : Set (G F ζ hζ)) (hA : IsCompact A),
    letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
    DifferentiableOn ℂ (compactMixedJet F ζ hζ U ι f hι hf k w A) V
  rational : ∀ (s : ℂ), s ∈ V →
    ∀ (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ),
    E F ζ hζ U ι f s (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ γ * g) =
      E F ζ hζ U ι f s g
  genuine : ∀ (s : ℂ), s ∈ V → ∀ (ε : rootsOfUnity 3 F) (g : G F ζ hζ),
    E F ζ hζ U ι f s (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * E F ζ hζ U ι f s g
  right_level : ∀ (s : ℂ), s ∈ V →
    ∀ (g : G F ζ hζ) (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    E F ζ hζ U ι f s (g * u.val) = E F ζ hζ U ι f s g
  right_spherical : ∀ (s : ℂ), s ∈ V →
    ∀ (g : G F ζ hζ) (k : KPContSectorArchSphericalFibers.KInfinity F),
    E F ζ hζ U ι f s (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) =
      E F ζ hζ U ι f s g
  descent : ∃ e : ℂ → KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
        (atlasLevel F ζ hζ C R P H U),
      (∀ (s : ℂ), s ∈ V → ∀ (g : G F ζ hζ),
        (e s).val (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ
          (atlasLevel F ζ hζ C R P H U)
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) = E F ζ hζ U ι f s g) ∧
      (∀ (s : ℂ), s ∈ V → ∀ x,
        (e s).val x = KPChamberL2Defect.series (lift F ζ hζ)
          (coveredRepresentative F ζ hζ C R P H U)
          (KPContActualSphericalFlatStage.L F ζ hζ U ι) f s x) ∧
      (∀ (s : ℂ), s ∈ V → ∀ i x,
        (KPContSectorScalarLineAlgebra.S F ζ hζ
          (atlasLevel F ζ hζ C R P H U) R P H (e s) i).val x =
            KPChamberL2Defect.series (lift F ζ hζ)
              (componentRepresentative F ζ hζ C R P H U i)
              (KPContActualSphericalFlatStage.L F ζ hζ U ι) f s x)

end DedekindZetaZeroFree.KPContActualChamberNormalSeries

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_normal_series
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) :
    KPContActualChamberNormalSeries.ChamberConclusions F ζ hζ C R P H U ι f hι hf := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k w K hK hKV A hA
    exact KPContActualChamberNormalSeries.normal_majorant F ζ hζ U ι f hι hf
      k w K hK hKV A hA
  · intro k w s hs g
    exact KPContActualChamberNormalSeries.mixed_summable F ζ hζ U ι f hι hf k w s hs g
  · intro k w s hs g
    exact KPContActualChamberNormalSeries.mixedJet_eq_tsum F ζ hζ U ι f hι hf k w s hs g
  · intro k w s hs g
    exact KPContActualChamberNormalSeries.mixedJet_commute F ζ hζ U ι f hι hf k w s hs g
  · intro k w K hK hKV A hA
    exact KPContActualChamberNormalSeries.mixed_uniform F ζ hζ U ι f hι hf
      k w K hK hKV A hA
  · intro s hs
    exact KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf s hs
  · intro k w A hA
    exact KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf
      k w A hA
  · intro s hs γ g
    exact (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1 γ g
  · intro s hs ε g
    exact (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.1 ε g
  · intro s hs g u
    exact (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.2.1 g u
  · intro s hs g k
    exact (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.2.2 g k
  · exact KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf

end DedekindZetaZeroFree

end
