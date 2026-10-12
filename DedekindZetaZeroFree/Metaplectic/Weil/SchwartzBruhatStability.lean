module

public import DedekindZetaZeroFree.Metaplectic.Weil.ThetaAndQuadraticOperators
public import DedekindZetaZeroFree.Metaplectic.Weil.FiniteQuadraticFourierKernel
public import DedekindZetaZeroFree.Metaplectic.Weil.Complex.QuadraticKernelAndPhase

@[expose] public section

noncomputable section
open scoped NumberField Classical SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable (F : Type) [Field F] [NumberField F]

private theorem phase_eq_traceCharacter
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (x y : PoissonS.Space F S) :
    PoissonS.tracePhase F S (fun v => localFiniteCharacter F v.val) x y =
      (sLocalTraceCharacter F S
        ((PoissonS.localProductToSpace F S).symm x *
          (PoissonS.localProductToSpace F S).symm y) : ℂ) := by
  have harch (u v : InfiniteAdeleRing F) :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u)
          (PoissonArch.infiniteAdeleToSpace F v) : ℂ)) =
        ∏ w : InfinitePlace F, (archTraceCharacter w (u w * v w) : ℂ) := by
    have htrace : PoissonArch.tracePairing F (PoissonArch.infiniteAdeleToSpace F u)
        (PoissonArch.infiniteAdeleToSpace F v) =
        ∑ w : InfinitePlace F, archTrace w (u w * v w) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
      unfold PoissonArch.tracePairing
      rw [PoissonArch.infiniteAdeleToSpace_coordinates,
        PoissonArch.infiniteAdeleToSpace_coordinates]
      dsimp only
      congr 1
      · apply Finset.sum_congr rfl
        intro w hw
        rw [archTrace_of_isReal w.val w.property, map_mul]
        rfl
      · rw [Finset.mul_sum]
        apply Fintype.sum_equiv
          (Equiv.subtypeEquivRight fun w : InfinitePlace F =>
            InfinitePlace.not_isReal_iff_isComplex).symm
        intro w
        change 2 * _ = archTrace w.val (u w.val * v w.val)
        rw [archTrace_of_isComplex w.val w.property, map_mul]
        rfl
    rw [htrace, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro w hw
    change _ = (Circle.exp (2 * Real.pi * archTrace w (u w * v w)) : ℂ)
    rw [Circle.coe_exp]
    push_cast
    ring_nf
  let u := (PoissonS.localProductToSpace F S).symm x
  let v := (PoissonS.localProductToSpace F S).symm y
  have hx : PoissonArch.infiniteAdeleToSpace F u.1 = x.1 :=
    congrArg Prod.fst ((PoissonS.localProductToSpace F S).apply_symm_apply x)
  have hy : PoissonArch.infiniteAdeleToSpace F v.1 = y.1 :=
    congrArg Prod.fst ((PoissonS.localProductToSpace F S).apply_symm_apply y)
  have hx2 : u.2 = x.2 := rfl
  have hy2 : v.2 = y.2 := rfl
  rw [sLocalTraceCharacter_apply]
  simp only [Circle.coe_mul, map_prod, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  unfold PoissonS.tracePhase
  rw [← hx, ← hy, harch]
  change _ = Circle.coeHom (∏ w : InfinitePlace F, archTraceCharacter w (u.1 w * v.1 w)) *
    Circle.coeHom (∏ w : S, localFiniteCharacter F w.val (u.2 w * v.2 w))
  rw [map_prod, map_prod]
  rfl

variable {F : Type} [Field F] [NumberField F]

local instance stabilityCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance stabilityCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem kernel_integrable (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f : PoissonS.Space F T → ℂ)
    (hf : Integrable f (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val)))
    (y : PoissonS.Space F T) :
    Integrable (fun x => f x *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
      ∏ v : T, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ))
      (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val)) := by
  have hc : Continuous (fun x : PoissonS.Space F T =>
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
      ∏ v : T, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ)) := by
    apply Continuous.mul
    · unfold PoissonArch.tracePairing
      fun_prop
    · apply continuous_finset_prod
      intro v hv
      exact continuous_subtype_val.comp ((continuous_localFiniteCharacter F v.val).comp
        ((continuous_apply v).comp continuous_snd |>.neg.mul continuous_const))
  have hn (x : PoissonS.Space F T) :
      ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : T, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ)‖ = 1 := by
    rw [norm_mul]
    rw [show (-2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ) =
        ((-2 * Real.pi * PoissonArch.tracePairing F x.1 y.1 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I, one_mul, norm_prod]
    exact Finset.prod_eq_one fun v _ => Circle.norm_coe _
  simpa only [mul_assoc] using hf.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (hn x).le))

private theorem fourier_stable (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f : PoissonS.Space F T → ℂ) (hf : f ∈ testSpace F T) :
    Integrable f (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val)) ∧
      fourier F T f ∈ testSpace F T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨fArch, φ, hl, hs, rfl⟩ := hf
    refine ⟨PoissonS.tensorFunction_integrable F T _ fArch φ hl hs, ?_⟩
    obtain ⟨g, ψ, hψl, hψs, hψ⟩ := PoissonS.fourierIntegral_tensor_bruhatSchwartz
      F T (fun v => localFiniteCharacter F v.val) (fun v => localNormalizedHaar F v.val)
      (fun v => continuous_localFiniteCharacter F v.val)
      (fun v => by simpa using localFiniteCharacter_right_nondegenerate F v.val 1 one_ne_zero)
      fArch φ hl hs
    have heq : fourier F T (PoissonS.tensorFunction F T fArch φ) =
        PoissonS.tensorFunction F T g ψ := funext hψ
    rw [heq]
    exact Submodule.subset_span ⟨g, ψ, hψl, hψs, rfl⟩
  | zero =>
    refine ⟨integrable_zero _ _ _, ?_⟩
    have heq : fourier F T 0 = 0 := by
      funext x
      simp [fourier, PoissonS.fourierIntegral]
    rw [heq]
    exact (testSpace F T).zero_mem
  | add f g hf hg ihf ihg =>
    refine ⟨ihf.1.add ihg.1, ?_⟩
    have heq : fourier F T (f + g) = fourier F T f + fourier F T g := by
      funext y
      simp only [fourier, PoissonS.fourierIntegral, Pi.add_apply, add_mul]
      exact integral_add (kernel_integrable T f ihf.1 y) (kernel_integrable T g ihg.1 y)
    rw [heq]
    exact (testSpace F T).add_mem ihf.2 ihg.2
  | smul a f hf ih =>
    refine ⟨ih.1.smul a, ?_⟩
    have heq : fourier F T (a • f) = a • fourier F T f := by
      funext y
      simp only [fourier, PoissonS.fourierIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc,
        integral_const_mul]
    rw [heq]
    exact (testSpace F T).smul_mem a ih.2

private theorem fieldMul_coordinates (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : F) (x : PoissonS.Space F T) :
    (PoissonS.localProductToSpace F T
      (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x)).1 =
      PoissonArch.fieldMul F b x.1 := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  rw [PoissonArch.fieldMul, ContinuousLinearEquiv.apply_symm_apply]
  change NumberField.mixedEmbedding.euclidean.toMixed F
    (PoissonArch.infiniteAdeleToSpace F (algebraMap F (InfiniteAdeleRing F) b *
      (PoissonArch.infiniteAdeleToSpace F).symm x.1)) = _
  rw [PoissonArch.infiniteAdeleToSpace_coordinates, map_mul,
    ← NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm x.1)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  rw [← hx]

private theorem chirp_tensor (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F)
    (fArch : SchwartzMap (PoissonArch.Space F) ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ)
    (hl : ∀ v, IsLocallyConstant (φ v)) (hs : ∀ v, HasCompactSupport (φ v)) :
    chirp F T b (PoissonS.tensorFunction F T fArch φ) ∈ testSpace F T := by
  let p : PoissonArch.Space F → ℂ := fun x => Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F x (PoissonArch.fieldMul F b x) : ℂ))
  have hp : p.HasTemperateGrowth := by
    have hq : (fun x : PoissonArch.Space F =>
        PoissonArch.tracePairing F x (PoissonArch.fieldMul F b x)).HasTemperateGrowth := by
      simp only [PoissonArch.tracePairing_eq_inner]
      apply (innerSL ℝ).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id
      apply (PoissonArch.traceAdapter F).hasTemperateGrowth.comp
      unfold PoissonArch.fieldMul
      fun_prop
    have hp' := Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul hq)
    convert hp' using 1
    funext x
    simp only [p, Function.comp_apply, Pi.mul_apply, Complex.ofReal_mul]
    congr 1
    push_cast
    ring
  let g := SchwartzMap.smulLeftCLM ℂ p fArch
  let ψ : (v : T) → v.val.adicCompletion F → ℂ := fun v x =>
    (localFiniteCharacter F v.val (algebraMap F (v.val.adicCompletion F) b * x ^ 2) : ℂ) * φ v x
  have hψl : ∀ v, IsLocallyConstant (ψ v) := by
    intro v
    exact (((isLocallyConstant_localFiniteCharacter F v.val).comp_continuous
      (continuous_const.mul (continuous_id.pow 2))).comp
      (fun z : Circle => (z : ℂ))).mul (hl v)
  have hψs : ∀ v, HasCompactSupport (ψ v) := fun v => (hs v).mul_left
  have hfun : chirp F T b (PoissonS.tensorFunction F T fArch φ) =
      PoissonS.tensorFunction F T g ψ := by
    funext x
    have hphase := phase_eq_traceCharacter F T x
      (PoissonS.localProductToSpace F T
        (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x))
    rw [AddEquiv.symm_apply_apply] at hphase
    have heq : (PoissonS.localProductToSpace F T).symm x *
        (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x) =
        sLocalDiagonal F T b * ((PoissonS.localProductToSpace F T).symm x) ^ 2 := by ring
    rw [heq] at hphase
    unfold chirp
    rw [← hphase]
    simp only [PoissonS.tracePhase,
      fieldMul_coordinates, PoissonS.tensorFunction, g,
      SchwartzMap.smulLeftCLM_apply_apply hp, smul_eq_mul, ψ, Finset.prod_mul_distrib]
    change _ = _
    have hfin (v : T) : x.2 v *
        (PoissonS.localProductToSpace F T
          (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x)).2 v =
        algebraMap F (v.val.adicCompletion F) b * (x.2 v) ^ 2 := by
      change x.2 v * (algebraMap F (v.val.adicCompletion F) b * x.2 v) = _
      ring
    simp_rw [hfin]
    dsimp [p]
    ring
  rw [hfun]
  exact Submodule.subset_span ⟨g, ψ, hψl, hψs, rfl⟩

theorem fourier_smul (T : Finset (HeightOneSpectrum (𝓞 F))) (c : ℂ)
    (f : PoissonS.Space F T → ℂ) :
    fourier F T (c • f) = c • fourier F T f := by
  funext y
  simp only [fourier, PoissonS.fourierIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← integral_const_mul]

theorem testSpace_integrable (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f : PoissonS.Space F T → ℂ) (hf : f ∈ testSpace F T) :
    Integrable f (PoissonS.productMeasure F T
      (fun v => localNormalizedHaar F v.val)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨fArch, φ, hl, hs, rfl⟩ := hf
    exact PoissonS.tensorFunction_integrable F T _ fArch φ hl hs
  | zero => exact integrable_zero (PoissonS.Space F T) ℂ (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val))
  | add f g hf hg ihf ihg => exact ihf.add ihg
  | smul c f hf ih => exact ih.smul c

theorem testSpace_stability (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F)
    (f : PoissonS.Space F T → ℂ) (hf : f ∈ testSpace F T) :
    fourier F T f ∈ testSpace F T ∧ chirp F T b f ∈ testSpace F T := by
  constructor
  · exact (fourier_stable T f hf).2
  · induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fArch, φ, hl, hs, rfl⟩ := hf
      exact chirp_tensor T b fArch φ hl hs
    | zero =>
      have heq : chirp F T b 0 = 0 := by
        funext x
        simp [chirp]
      rw [heq]
      exact (testSpace F T).zero_mem
    | add f g hf hg ihf ihg =>
      have heq : chirp F T b (f + g) = chirp F T b f + chirp F T b g := by
        funext x
        simp [chirp, mul_add]
      rw [heq]
      exact (testSpace F T).add_mem ihf ihg
    | smul a f hf ih =>
      have heq : chirp F T b (a • f) = a • chirp F T b f := by
        funext x
        simp [chirp, smul_eq_mul, mul_left_comm]
      rw [heq]
      exact (testSpace F T).smul_mem a ih

end DedekindZetaZeroFree.QuadraticRawProduct

end
