module

public import DedekindZetaZeroFree.Metaplectic.Weil.SchwartzBruhatStability
public import DedekindZetaZeroFree.Metaplectic.Weil.ArchimedeanProductQuadraticOperators

@[expose] public section

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

variable {F : Type} [Field F] [NumberField F]

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

 theorem fourier_add_testSpace (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f g : testSpace F T) :
    fourier F T ((f : PoissonS.Space F T → ℂ) + (g : PoissonS.Space F T → ℂ)) =
      fourier F T (f : PoissonS.Space F T → ℂ) +
        fourier F T (g : PoissonS.Space F T → ℂ) := by
  funext y
  simp only [fourier, PoissonS.fourierIntegral, Pi.add_apply, add_mul]
  exact integral_add
    (kernel_integrable T (f : PoissonS.Space F T → ℂ)
      (testSpace_integrable T (f : PoissonS.Space F T → ℂ) f.2) y)
    (kernel_integrable T (g : PoissonS.Space F T → ℂ)
      (testSpace_integrable T (g : PoissonS.Space F T → ℂ) g.2) y)

 def chirpLinearMap (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F) :
    (PoissonS.Space F T → ℂ) →ₗ[ℂ] (PoissonS.Space F T → ℂ) where
  toFun f := chirp F T b f
  map_add' f g := by
    funext x
    simp only [chirp, Pi.add_apply, mul_add]
  map_smul' a f := by
    funext x
    simp only [chirp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

 def dilationLinearMap (T : Finset (HeightOneSpectrum (𝓞 F))) (c : F) :
    (PoissonS.Space F T → ℂ) →ₗ[ℂ] (PoissonS.Space F T → ℂ) where
  toFun f := dilation F T c f
  map_add' f g := by
    funext x
    simp only [dilation, Pi.add_apply]
  map_smul' a f := by
    funext x
    simp only [dilation, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

 def fourT (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    testSpace F T →ₗ[ℂ] testSpace F T where
  toFun f := ⟨fourier F T (f : PoissonS.Space F T → ℂ),
    (testSpace_stability A T 0 (f : PoissonS.Space F T → ℂ) f.2).1⟩
  map_add' f g := by
    apply Subtype.ext
    show fourier F T ((f : PoissonS.Space F T → ℂ) + (g : PoissonS.Space F T → ℂ)) =
      fourier F T (f : PoissonS.Space F T → ℂ) + fourier F T (g : PoissonS.Space F T → ℂ)
    exact fourier_add_testSpace T f g
  map_smul' a f := by
    apply Subtype.ext
    show fourier F T (a • (f : PoissonS.Space F T → ℂ)) =
      a • fourier F T (f : PoissonS.Space F T → ℂ)
    exact fourier_smul T a (f : PoissonS.Space F T → ℂ)

 def fourTest (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    testSpace F T →ₗ[ℂ] (PoissonS.Space F T → ℂ) where
  toFun f := fourier F T (f : PoissonS.Space F T → ℂ)
  map_add' f g := fourier_add_testSpace T f g
  map_smul' a f := fourier_smul T a (f : PoissonS.Space F T → ℂ)

 def chirpT (A : SArithmeticData F) (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F) :
    testSpace F T →ₗ[ℂ] testSpace F T where
  toFun f := ⟨chirp F T b (f : PoissonS.Space F T → ℂ),
    (testSpace_stability A T b (f : PoissonS.Space F T → ℂ) f.2).2⟩
  map_add' f g := by
    apply Subtype.ext
    show chirp F T b ((f : PoissonS.Space F T → ℂ) + (g : PoissonS.Space F T → ℂ)) =
      chirp F T b (f : PoissonS.Space F T → ℂ) + chirp F T b (g : PoissonS.Space F T → ℂ)
    exact (chirpLinearMap T b).map_add _ _
  map_smul' a f := by
    apply Subtype.ext
    show chirp F T b (a • (f : PoissonS.Space F T → ℂ)) =
      a • chirp F T b (f : PoissonS.Space F T → ℂ)
    exact (chirpLinearMap T b).map_smul a _

theorem quadratic_compositions_linear (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (b c d : F) (k : ℂ) :
    ∃ L R : testSpace F T →ₗ[ℂ] (PoissonS.Space F T → ℂ),
      (∀ f : testSpace F T,
        L f = fourier F T (chirp F T b (fourier F T (f : PoissonS.Space F T → ℂ)))) ∧
      (∀ f : testSpace F T,
        R f = fun y => k * chirp F T c
          (dilation F T d
            (fourier F T (chirp F T c (f : PoissonS.Space F T → ℂ)))) y) := by
  refine ⟨(fourTest A T).comp ((chirpT A T b).comp (fourT A T)),
    (k • ((chirpLinearMap T c).comp ((dilationLinearMap T d).comp (fourTest A T)))).comp
      (chirpT A T c), ?_, ?_⟩
  · intro f
    simp only [LinearMap.comp_apply]
    rfl
  · intro f
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, chirpLinearMap, dilationLinearMap, fourTest, chirpT,
      LinearMap.coe_mk, AddHom.coe_mk]

end DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

variable (F : Type) [Field F] [NumberField F]

private theorem recombination_phase_eq_traceCharacter
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

variable {F}

private theorem recombination_fieldMul_coordinates (T : Finset (HeightOneSpectrum (𝓞 F)))
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

local instance recombinationCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance recombinationCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem recombination_fourier_tensor (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hHaar : ∀ v, A.finiteTraceHaar v = localNormalizedHaar F v)
    (hCharacter : ∀ v, ResidueTrace.localTraceCharacter v = localFiniteCharacter F v)
    (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ) :
    fourier F T (fun z => fArch z.1 * ∏ v : T, φ v (z.2 v)) =
      fun y => PoissonArch.traceFourier F fArch y.1 *
        ∏ v : T, A.finiteTraceFourier v.val (φ v) (y.2 v) := by
  haveI : MeasureTheory.SFinite (PoissonArch.traceMeasure F) := by
    unfold PoissonArch.traceMeasure
    infer_instance
  funext y
  unfold fourier PoissonS.fourierIntegral PoissonS.productMeasure
  have hfun : (fun x : PoissonS.Space F T =>
      (fArch x.1 * ∏ v : T, φ v (x.2 v)) *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
          (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : T, (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ)) =
      fun x => (fArch x.1 * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
        (PoissonArch.tracePairing F x.1 y.1 : ℂ))) *
        ∏ v : T, φ v (x.2 v) * (localFiniteCharacter F v.val (-x.2 v * y.2 v) : ℂ) := by
    funext x
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun]
  have hi := MeasureTheory.integral_prod_mul
    (μ := PoissonArch.traceMeasure F)
    (ν := MeasureTheory.Measure.pi (fun v : T => localNormalizedHaar F v.val))
    (fun z => fArch z * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F z y.1 : ℂ)))
    (fun z : PoissonFinite.Space F T => ∏ v : T,
      φ v (z v) * (localFiniteCharacter F v.val (-z v * y.2 v) : ℂ))
  have hj := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun v : T => localNormalizedHaar F v.val)
    (fun (v : T) z => φ v z * (localFiniteCharacter F v.val (-z * y.2 v) : ℂ))
  exact hi.trans (congrArg (fun c => PoissonArch.traceFourier F fArch y.1 * c)
    (by simpa only [SArithmeticData.finiteTraceFourier, hHaar, hCharacter] using hj))

private theorem recombination_chirp_tensor (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hCharacter : ∀ v, ResidueTrace.localTraceCharacter v = localFiniteCharacter F v)
    (b : F) (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ) :
    chirp F T b (fun z => fArch z.1 * ∏ v : T, φ v (z.2 v)) =
      fun z => archChirp F b fArch z.1 * ∏ v : T,
        A.finiteQuadraticMultiplier v.val (algebraMap F (v.val.adicCompletion F) b)
          (φ v) (z.2 v) := by
  funext x
  have hphase := recombination_phase_eq_traceCharacter F T
    (PoissonS.localProductToSpace F T
      (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x)) x
  rw [AddEquiv.symm_apply_apply] at hphase
  have heq : (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x) *
      (PoissonS.localProductToSpace F T).symm x =
      sLocalDiagonal F T b * ((PoissonS.localProductToSpace F T).symm x) ^ 2 := by ring
  rw [heq] at hphase
  unfold chirp
  rw [← hphase]
  simp only [PoissonS.tracePhase, recombination_fieldMul_coordinates, archChirp,
    SArithmeticData.finiteQuadraticMultiplier, hCharacter, Finset.prod_mul_distrib]
  have hfin (v : T) :
      (PoissonS.localProductToSpace F T
        (sLocalDiagonal F T b * (PoissonS.localProductToSpace F T).symm x)).2 v * x.2 v =
      algebraMap F (v.val.adicCompletion F) b * (x.2 v) ^ 2 := by
    change (algebraMap F (v.val.adicCompletion F) b * x.2 v) * x.2 v = _
    ring
  simp_rw [hfin]
  ring

private theorem recombination_dilation_tensor (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : F)
    (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ) :
    dilation F T c (fun z => fArch z.1 * ∏ v : T, φ v (z.2 v)) =
      fun z => archDilation F c fArch z.1 * ∏ v : T,
        A.finiteDilation v.val (algebraMap F (v.val.adicCompletion F) c) (φ v) (z.2 v) := by
  funext x
  simp only [dilation, recombination_fieldMul_coordinates, archDilation,
    SArithmeticData.finiteDilation]
  rfl

theorem quadratic_operator_on_tensor (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (a : Fˣ)
    (fArch : SchwartzMap (PoissonArch.Space F) ℂ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v))
    (hHaar : ∀ v : HeightOneSpectrum (𝓞 F),
      A.finiteTraceHaar v = localNormalizedHaar F v)
    (hCharacter : ∀ v : HeightOneSpectrum (𝓞 F),
      ResidueTrace.localTraceCharacter v = localFiniteCharacter F v)
    (harch : PoissonArch.traceFourier F
        (archChirp F (a : F) (PoissonArch.traceFourier F fArch)) =
      fun y => ((Real.sqrt (∏ w : InfinitePlace F,
          w (2 * (a : F)) ^ w.mult))⁻¹ : ℂ) *
        archChirp F (-1 / (4 * (a : F)))
          (archDilation F (1 / (2 * (a : F)))
            (PoissonArch.traceFourier F
              (archChirp F (-1 / (4 * (a : F))) fArch))) y)
    (hfinite : let aLocal : (v : T) → (v.val.adicCompletion F)ˣ := fun v =>
        Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a
      ∀ y : PoissonFinite.Space F T,
      (∏ v : T, A.finiteTraceFourier v.val
        (A.finiteQuadraticMultiplier v.val (aLocal v : v.val.adicCompletion F)
          (A.finiteTraceFourier v.val (φ v))) (y v)) =
        (∏ v : T, A.finiteGamma v.val (aLocal v)) *
          ((Real.sqrt (∏ v : T,
            ‖(2 : v.val.adicCompletion F) * (aLocal v : v.val.adicCompletion F)‖))⁻¹ : ℂ) *
          (∏ v : T, A.finiteQuadraticMultiplier v.val
            (-1 / (4 * (aLocal v : v.val.adicCompletion F)))
            (A.finiteDilation v.val (1 / (2 * (aLocal v : v.val.adicCompletion F)))
              (A.finiteTraceFourier v.val
                (A.finiteQuadraticMultiplier v.val
                  (-1 / (4 * (aLocal v : v.val.adicCompletion F))) (φ v)))) (y v)))
    (hmodule : ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ) =
        ((Real.sqrt (∏ w : InfinitePlace F, w (2 * (a : F)) ^ w.mult))⁻¹ : ℂ) *
          ∏ v : T, ((Real.sqrt
            ‖algebraMap F (v.val.adicCompletion F) (2 * (a : F))‖)⁻¹ : ℂ)) :
    fourier F T (chirp F T (a : F)
        (fourier F T (PoissonS.tensorFunction F T fArch φ))) =
      fun y =>
        ((∏ v ∈ T, A.finiteGamma v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) *
          ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ)) *
        chirp F T (-1 / (4 * (a : F)))
          (dilation F T (1 / (2 * (a : F)))
            (fourier F T (chirp F T (-1 / (4 * (a : F)))
              (PoissonS.tensorFunction F T fArch φ)))) y := by
  unfold PoissonS.tensorFunction
  rw [recombination_fourier_tensor A T hHaar hCharacter,
    recombination_chirp_tensor A T hCharacter,
    recombination_fourier_tensor A T hHaar hCharacter,
    recombination_chirp_tensor A T hCharacter,
    recombination_fourier_tensor A T hHaar hCharacter,
    recombination_dilation_tensor A T,
    recombination_chirp_tensor A T hCharacter]
  funext y
  rw [harch]
  have hf := hfinite y.2
  dsimp only at hf
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hf
  simp only [map_div₀, map_neg, map_one, map_mul, map_ofNat] at *
  rw [hf, hmodule]
  have hg : (∏ v ∈ T, A.finiteGamma v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) =
      ∏ v : T, A.finiteGamma v.val
        (Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a) := by
    exact (Finset.prod_attach T _).symm
  rw [hg]
  rw [Real.sqrt_prod Finset.univ (fun v _ => norm_nonneg _)]
  simp only [Complex.ofReal_prod, Finset.prod_inv_distrib,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  ac_rfl

end DedekindZetaZeroFree.QuadraticRawProduct.TensorKernelSteps

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable {F : Type} [Field F] [NumberField F]

theorem tensor_finiteTraceHaar_eq (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) :
    A.finiteTraceHaar v = localNormalizedHaar F v := by
  apply FiniteOscillatoryStabilization.finiteTraceHaar_eq_localNormalizedHaar_of_integerVolume
  rw [PoissonS.integerVolume,
    FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent F v,
    zpow_natCast, localHalfDifferentFactor_eq_inv_sqrt F v,
    localDifferentNorm, Nat.cast_pow, one_div]

private theorem tensor_primeBelow_eq_adapter (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.rationalPrimeBelow v = PlaceTraceAdapter.prime F v := by
  apply Subtype.ext
  change ringChar (𝓞 F ⧸ v.asIdeal) = _
  apply CharP.ringChar_of_prime_eq_zero (PlaceTraceAdapter.prime F v).2
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h : ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ) ∈
      (PlaceTraceAdapter.rationalPlace F v).asIdeal := by
    have hgen := Rat.HeightOneSpectrum.natGenerator_dvd_iff
      (PlaceTraceAdapter.rationalPlace F v) (n := (PlaceTraceAdapter.prime F v).1)
    have hh := hgen.mp (dvd_refl _)
    rw [Ideal.mem_map_iff_of_surjective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).surjective] at hh
    obtain ⟨x, hx, he⟩ := hh
    have he' : x = ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ) :=
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by simpa using he)
    exact he' ▸ hx
  have h' : (algebraMap (𝓞 ℚ) (𝓞 F) ((PlaceTraceAdapter.prime F v).1 : 𝓞 ℚ)) ∈ v.asIdeal := h
  simpa using h'

theorem tensor_finiteCharacter_eq (v : HeightOneSpectrum (𝓞 F)) :
    ResidueTrace.localTraceCharacter v = localFiniteCharacter F v := by
  letI (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
  have hp := tensor_primeBelow_eq_adapter v
  have hgeneral (p : Nat.Primes) (m : ℚ_[p] →+* v.adicCompletion F)
      (hmc : Continuous m)
      (hmq : ∀ q : ℚ, m (q : ℚ_[p]) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F q))
      (hp : p = PlaceTraceAdapter.prime F v) :
      (letI := m.toAlgebra
       (rationalPadicCharacter p).compAddMonoidHom
        (Algebra.trace ℚ_[p] (v.adicCompletion F)).toAddMonoidHom) = localFiniteCharacter F v := by
    subst p
    have hmap : m = PlaceTraceAdapter.padicMap F v := by
      apply DFunLike.coe_injective
      apply (Padic.denseRange_ratCast (PlaceTraceAdapter.prime F v)).equalizer hmc
      · letI : Algebra ℚ ((PlaceTraceAdapter.rationalPlace F v).adicCompletion ℚ) :=
          HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
        exact (finitePlaceAdicCompletionMap_continuous ℚ F _ _).comp
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (PlaceTraceAdapter.rationalPlace F v)).symm.continuous
      · funext q
        exact (hmq q).trans (by simp [PlaceTraceAdapter.padicMap, map_ratCast])
    subst m
    rfl
  exact hgeneral _ _ (ResidueTrace.baseEmbedding_spec v).1
    (ResidueTrace.baseEmbedding_spec v).2 hp

theorem tensor_finite_quadratic_operator (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (v : T) → (v.val.adicCompletion F)ˣ)
    (φ : (v : T) → v.val.adicCompletion F → ℂ)
    (hφ : ∀ v, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v))
    (y : PoissonFinite.Space F T) :
    (∏ v : T, A.finiteTraceFourier v.val
      (A.finiteQuadraticMultiplier v.val (a v : v.val.adicCompletion F)
        (A.finiteTraceFourier v.val (φ v))) (y v)) =
      (∏ v : T, A.finiteGamma v.val (a v)) *
        ((Real.sqrt (∏ v : T,
          ‖(2 : v.val.adicCompletion F) * (a v : v.val.adicCompletion F)‖))⁻¹ : ℂ) *
        (∏ v : T, A.finiteQuadraticMultiplier v.val
          (-1 / (4 * (a v : v.val.adicCompletion F)))
          (A.finiteDilation v.val (1 / (2 * (a v : v.val.adicCompletion F)))
            (A.finiteTraceFourier v.val
              (A.finiteQuadraticMultiplier v.val
                (-1 / (4 * (a v : v.val.adicCompletion F))) (φ v)))) (y v)) := by
  have hlocal (v : T) := congrFun
    (A.finiteTraceFourier_quadratic_operator v.val (a v) (φ v) (hφ v)) (y v)
  simp_rw [hlocal, Finset.prod_mul_distrib]
  congr 1
  rw [Real.sqrt_prod Finset.univ (fun v _ => norm_nonneg _)]
  simp only [Complex.ofReal_prod, Complex.ofReal_inv, Finset.prod_inv_distrib]

theorem quadratic_module_factorization
    (T : Finset (HeightOneSpectrum (𝓞 F))) (b : F) :
    ((Real.sqrt (PoissonS.productModule F T b))⁻¹ : ℂ) =
      ((Real.sqrt (∏ w : InfinitePlace F, w b ^ w.mult))⁻¹ : ℂ) *
        ∏ v : T, ((Real.sqrt ‖algebraMap F (v.val.adicCompletion F) b‖)⁻¹ : ℂ) := by
  have hfinite : (∏ v ∈ T, FinitePlace.mk v b) =
      ∏ v : T, ‖algebraMap F (v.val.adicCompletion F) b‖ := by
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro v _
    rfl
  unfold PoissonS.productModule
  rw [hfinite, Real.sqrt_mul (Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg w b) _)]
  rw [Complex.ofReal_mul, mul_inv_rev, mul_comm]
  congr 1
  rw [Real.sqrt_prod _ (fun v _ => norm_nonneg _), Finset.prod_inv_distrib,
    ← Complex.ofReal_prod]

theorem tensor_quadratic_operator (A : SArithmeticData F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (a : Fˣ)
    (f : PoissonS.Space F T → ℂ) (hf : f ∈ testSpace F T) :
    fourier F T (chirp F T (a : F) (fourier F T f)) =
      fun y =>
        ((∏ v ∈ T, A.finiteGamma v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) *
          ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ)) *
        chirp F T (-1 / (4 * (a : F)))
          (dilation F T (1 / (2 * (a : F)))
            (fourier F T (chirp F T (-1 / (4 * (a : F))) f))) y := by
  let k : ℂ := (∏ v ∈ T, A.finiteGamma v
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) *
    ((Real.sqrt (PoissonS.productModule F T (2 * (a : F))))⁻¹ : ℂ)
  obtain ⟨L, R, hL, hR⟩ := TensorKernelSteps.quadratic_compositions_linear A T
    (a : F) (-1 / (4 * (a : F))) (1 / (2 * (a : F))) k
  have heq : ∀ g (hg : g ∈ testSpace F T), L ⟨g, hg⟩ = R ⟨g, hg⟩ := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨fArch, φ, hl, hs, rfl⟩ := hg
      rw [hL, hR]
      exact TensorKernelSteps.quadratic_operator_on_tensor A T a fArch φ hl hs
        (tensor_finiteTraceHaar_eq A) tensor_finiteCharacter_eq
        (TensorKernelSteps.archimedean_quadratic_operator A a fArch)
        (fun y => tensor_finite_quadratic_operator A T
          (fun v => Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a)
          φ (fun v => ⟨hl v, hs v⟩) y)
        (quadratic_module_factorization T (2 * (a : F)))
    | zero =>
      change L 0 = R 0
      simp only [map_zero]
    | add g h hg hh ihg ihh =>
      change L (⟨g, hg⟩ + ⟨h, hh⟩) = R (⟨g, hg⟩ + ⟨h, hh⟩)
      rw [map_add, map_add, ihg, ihh]
    | smul c g hg ih =>
      change L (c • ⟨g, hg⟩) = R (c • ⟨g, hg⟩)
      rw [map_smul, map_smul, ih]
  exact (hL ⟨f, hf⟩).symm.trans ((heq f hf).trans (hR ⟨f, hf⟩))

end DedekindZetaZeroFree.QuadraticRawProduct

end

end
