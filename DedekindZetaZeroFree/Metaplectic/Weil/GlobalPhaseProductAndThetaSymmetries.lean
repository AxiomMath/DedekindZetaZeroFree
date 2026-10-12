module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.TensorSummation
public import DedekindZetaZeroFree.Metaplectic.Weil.OddLocalEvaluationAndHilbertDefect
public import DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductors
public import DedekindZetaZeroFree.Arithmetic.Kummer.CofiniteResiduePowerDetection
public import DedekindZetaZeroFree.Metaplectic.Weil.GlobalTensorQuadraticIdentity

@[expose] public section

section

noncomputable section
open scoped NumberField Classical Valued
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable {F : Type} [Field F] [NumberField F]

private theorem localProductToSpace_sLocalDiagonal
    (T : Finset (HeightOneSpectrum (𝓞 F))) (r : F) :
    PoissonS.localProductToSpace F T (sLocalDiagonal F T r) =
      PoissonS.diagonalHom F T r := by
  apply Prod.ext
  · show PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F T r).1 =
      (NumberField.mixedEmbedding.euclidean.toMixed F).symm
        (NumberField.mixedEmbedding F r)
    have h1 : (sLocalDiagonal F T r).1 =
        algebraMap F (NumberField.InfiniteAdeleRing F) r := by
      funext v
      simp only [sLocalDiagonal_infinite]
      exact (NumberField.InfiniteAdeleRing.algebraMap_apply F r v).symm
    rw [h1]
    apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
    rw [PoissonArch.infiniteAdeleToSpace_coordinates,
      ContinuousLinearEquiv.apply_symm_apply,
      NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  · show (sLocalDiagonal F T r).2 = PoissonFinite.diagonal F T r
    funext v
    rw [sLocalDiagonal_finite]
    rfl

private theorem symm_localProductToSpace_diagonal
    (T : Finset (HeightOneSpectrum (𝓞 F))) (r : F) :
    (PoissonS.localProductToSpace F T).symm (PoissonS.diagonalHom F T r) =
      sLocalDiagonal F T r := by
  calc (PoissonS.localProductToSpace F T).symm (PoissonS.diagonalHom F T r)
      = (PoissonS.localProductToSpace F T).symm
          (PoissonS.localProductToSpace F T (sLocalDiagonal F T r)) := by
        rw [localProductToSpace_sLocalDiagonal]
    _ = sLocalDiagonal F T r := (PoissonS.localProductToSpace F T).symm_apply_apply _

private theorem valued_algebraMap_adicCompletion
    (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [show algebraMap F (v.adicCompletion F) t = (t : v.adicCompletion F) from rfl]
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe F v t

private theorem mem_sIntegerRing_of_val (T : Finset (HeightOneSpectrum (𝓞 F))) {t : F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → v.valuation F t ≤ 1) :
    t ∈ sIntegerRing F T := by
  rw [mem_sIntegerRing_iff]
  intro v hv
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    valued_algebraMap_adicCompletion]
  exact h v hv

private theorem chirp_diagonal_eq_one
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : PoissonS.ContainsDifferent F T)
    (b : F) (hb : b ∈ sIntegerRing F T) (m : sIntegerRing F T) :
    sLocalTraceCharacter F T
      (sLocalDiagonal F T b * (sLocalDiagonal F T (m : F)) ^ 2) = 1 := by
  rw [← map_pow, ← map_mul]
  exact sLocalTraceCharacter_sIntegerDiagonal_eq_one F T hT
    ⟨b * (m : F) ^ 2, mul_mem hb (pow_mem m.2 2)⟩

private theorem chirp_theta_eq
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : PoissonS.ContainsDifferent F T)
    (b : F) (hb : b ∈ sIntegerRing F T) (f : PoissonS.Space F T → ℂ) :
    theta F T (chirp F T b f) = theta F T f := by
  show (∑' m : sIntegerRing F T,
      chirp F T b f (PoissonS.diagonalHom F T (m : F))) =
    ∑' m : sIntegerRing F T, f (PoissonS.diagonalHom F T (m : F))
  apply tsum_congr
  intro m
  show (sLocalTraceCharacter F T
      (sLocalDiagonal F T b *
        ((PoissonS.localProductToSpace F T).symm
          (PoissonS.diagonalHom F T (m : F))) ^ 2) : ℂ) *
      f (PoissonS.diagonalHom F T (m : F)) =
    f (PoissonS.diagonalHom F T (m : F))
  rw [symm_localProductToSpace_diagonal, chirp_diagonal_eq_one T hT b hb m,
    Circle.coe_one, one_mul]

theorem theta_auxiliary_symmetries
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : PoissonS.ContainsDifferent F T) (a : Fˣ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → v.valuation F (a : F) = 1)
    (h2a : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
      v.valuation F (2 * (a : F)) = 1) :
    (∀ f : PoissonS.Space F T → ℂ,
      theta F T (chirp F T (a : F) f) = theta F T f) ∧
    (∀ f : PoissonS.Space F T → ℂ,
      theta F T (chirp F T (-1 / (4 * (a : F))) f) = theta F T f) ∧
    (∀ f : PoissonS.Space F T → ℂ,
      theta F T (dilation F T (1 / (2 * (a : F))) f) = theta F T f) := by
  have ha_mem : (a : F) ∈ sIntegerRing F T :=
    mem_sIntegerRing_of_val T (fun v hv => (ha v hv).le)
  have h2a_ne : 2 * (a : F) ≠ 0 := mul_ne_zero (by norm_num) a.ne_zero
  have h2a_mem : (2 * (a : F)) ∈ sIntegerRing F T :=
    mem_sIntegerRing_of_val T (fun v hv => (h2a v hv).le)
  have h2a_inv_mem : (2 * (a : F))⁻¹ ∈ sIntegerRing F T := by
    refine mem_sIntegerRing_of_val T (fun v hv => ?_)
    rw [map_inv₀, h2a v hv, inv_one]

  let u : (sIntegerRing F T)ˣ :=
    ⟨⟨2 * (a : F), h2a_mem⟩, ⟨(2 * (a : F))⁻¹, h2a_inv_mem⟩,
      Subtype.ext (mul_inv_cancel₀ h2a_ne),
      Subtype.ext (inv_mul_cancel₀ h2a_ne)⟩
  have hu : ((u : sIntegerRing F T) : F) = 2 * (a : F) := rfl
  have hu_inv_val : ((↑u⁻¹ : sIntegerRing F T) : F) = (2 * (a : F))⁻¹ := by
    have h := congrArg (fun z : sIntegerRing F T => (z : F)) u.val_inv
    simp only [Subring.coe_mul, Subring.coe_one, hu] at h
    exact eq_inv_of_mul_eq_one_right h
  have hb2 : (-1 / (4 * (a : F))) ∈ sIntegerRing F T := by
    have hb_eq : -1 / (4 * (a : F)) =
        -((a : F) * ((↑u⁻¹ : sIntegerRing F T) : F) ^ 2) := by
      rw [hu_inv_val]
      field_simp
      ring
    rw [hb_eq]
    exact neg_mem (mul_mem ha_mem (pow_mem (↑u⁻¹ : sIntegerRing F T).2 2))
  refine ⟨fun f => chirp_theta_eq T hT (a : F) ha_mem f,
    fun f => chirp_theta_eq T hT (-1 / (4 * (a : F))) hb2 f, ?_⟩
  intro f
  have hc : 1 / (2 * (a : F)) = ((↑u⁻¹ : sIntegerRing F T) : F) := by
    rw [hu_inv_val, one_div]
  have hpt : ∀ m : sIntegerRing F T,
      dilation F T (1 / (2 * (a : F))) f (PoissonS.diagonalHom F T (m : F)) =
        f (PoissonS.diagonalHom F T
          (((↑u⁻¹ : sIntegerRing F T) * m : sIntegerRing F T) : F)) := by
    intro m
    show f (PoissonS.localProductToSpace F T (sLocalDiagonal F T (1 / (2 * (a : F))) *
      (PoissonS.localProductToSpace F T).symm (PoissonS.diagonalHom F T (m : F)))) = _
    rw [symm_localProductToSpace_diagonal, hc, ← map_mul,
      localProductToSpace_sLocalDiagonal]
    simp only [Subring.coe_mul]
  show (∑' m : sIntegerRing F T,
      dilation F T (1 / (2 * (a : F))) f (PoissonS.diagonalHom F T (m : F))) =
    ∑' m : sIntegerRing F T, f (PoissonS.diagonalHom F T (m : F))
  simp_rw [hpt]
  exact (u⁻¹).mulLeft.tsum_eq
    (fun m : sIntegerRing F T => f (PoissonS.diagonalHom F T (m : F)))

end DedekindZetaZeroFree.QuadraticRawProduct

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable {F : Type} [Field F] [NumberField F]

theorem exists_nonzero_theta (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ f : PoissonS.Space F T → ℂ, f ∈ testSpace F T ∧ theta F T f ≠ 0 := by
  obtain ⟨g, -, hgc, hgd, hgn, hg0⟩ :=
    exists_contDiff_tsupport_subset (E := PoissonArch.Space F)
      (x := 0) (n := (⊤ : ℕ∞)) Filter.univ_mem
  let gArch : SchwartzMap (PoissonArch.Space F) ℂ :=
    (hgc.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hgd)
  let φ : (v : T) → v.val.adicCompletion F → ℂ :=
    fun _ z => if ‖z‖ ≤ 1 then 1 else 0
  have hφ (v : T) : IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v) := by
    simpa [φ] using PoissonS.ScaleShift.local_ball_test F v.val 0 0
  let f := PoissonS.tensorFunction F T gArch φ
  have hreal (x : PoissonS.Space F T) :
      f x = Complex.ofReal (g x.1 * ∏ v : T,
        (if ‖x.2 v‖ ≤ 1 then 1 else 0 : ℝ)) := by
    change (g x.1 : ℂ) * (∏ v : T, φ v (x.2 v)) = _
    simp [φ, Complex.ofReal_prod, apply_ite Complex.ofReal]
  have hn (x : PoissonS.Space F T) : 0 ≤ (f x).re := by
    rw [hreal, Complex.ofReal_re]
    apply mul_nonneg (hgn (Set.mem_range_self _)).1
    exact Finset.prod_nonneg (fun v _ => by split_ifs <;> norm_num)
  have hzero : f 0 = 1 := by
    rw [hreal]
    simp [hg0]
  have hs : Summable (fun m : sIntegerRing F T =>
      f (PoissonS.diagonalHom F T (m : F))) := by
    have hnorm := PoissonS.summable_norm_tensorFunction_lattice F T gArch φ
      (fun v => (hφ v).1) (fun v => (hφ v).2) 1 one_ne_zero
    exact ((PoissonS.ScaleShift.diagonalLatticeEquiv F T).summable_iff.mpr
      hnorm).of_norm
  refine ⟨f, Submodule.subset_span ⟨gArch, φ, (fun v => (hφ v).1),
    (fun v => (hφ v).2), rfl⟩, ?_⟩
  have hpos : 0 < (theta F T f).re := by
    rw [theta, Complex.re_tsum hs]
    apply (Complex.reCLM.summable hs).tsum_pos
      (fun m => hn _) (0 : sIntegerRing F T)
    simpa [hzero] using (show (0 : ℝ) < 1 by norm_num)
  intro h
  simpa [h] using hpos

end DedekindZetaZeroFree.QuadraticRawProduct

end

end

section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.QuadraticRawProduct

variable {F : Type} [Field F] [NumberField F]

local instance thetaCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance thetaCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem fourier_add (T : Finset (HeightOneSpectrum (𝓞 F)))
    (f g : PoissonS.Space F T → ℂ)
    (hf : Integrable f (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val)))
    (hg : Integrable g (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val))) :
    fourier F T (f + g) = fourier F T f + fourier F T g := by
  funext y
  have h := PoissonS.ScaleShift.fourierIntegral_finset_sum F T
    (fun v => localFiniteCharacter F v.val) (fun v => localNormalizedHaar F v.val)
    (fun v => continuous_localFiniteCharacter F v.val)
    (Finset.univ : Finset Bool) (fun _ => (1 : ℂ))
    (fun b => if b then g else f)
    (by intro b hb; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption) y
  simpa [fourier, Pi.add_def, add_comm] using h

private theorem theta_symmetry_fourier_smul (T : Finset (HeightOneSpectrum (𝓞 F)))
    (c : ℂ) (f : PoissonS.Space F T → ℂ) :
    fourier F T (c • f) = c • fourier F T f := by
  funext y
  simp only [fourier, PoissonS.fourierIntegral, Pi.smul_apply, smul_eq_mul,
    mul_assoc, integral_const_mul]

theorem theta_fourier (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : PoissonS.ContainsDifferent F T)
    (f : PoissonS.Space F T → ℂ) (hf : f ∈ testSpace F T) :
    theta F T (fourier F T f) = theta F T f := by
  have hnorm : PoissonS.LocalNormalization F T (fun v => localNormalizedHaar F v.val) := by
    intro v
    have hset : {x : v.val.adicCompletion F | ‖x‖ ≤ 1} =
        (v.val.adicCompletionIntegers F : Set (v.val.adicCompletion F)) := by
      ext x
      simp [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [hset, localNormalizedHaar_integerRing]
    congr 1
    rw [localHalfDifferentFactor_eq_inv_sqrt, localDifferentNorm,
      PoissonS.integerVolume,
      FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent]
    simp
  have hmain : ∀ f ∈ testSpace F T,
      Integrable f (PoissonS.productMeasure F T (fun v => localNormalizedHaar F v.val)) ∧
      Summable (fun m : sIntegerRing F T => f (PoissonS.diagonalHom F T (m : F))) ∧
      Summable (fun m : sIntegerRing F T => fourier F T f (PoissonS.diagonalHom F T (m : F))) ∧
      theta F T (fourier F T f) = theta F T f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fArch, φ, hl, hs, rfl⟩ := hf
      have hp := PoissonS.poisson_sum_tensorFunction F T hT
        (fun v => localNormalizedHaar F v.val) hnorm fArch φ hl hs
      exact ⟨PoissonS.tensorFunction_integrable F T _ fArch φ hl hs,
        hp.1.of_norm, hp.2.1.of_norm, hp.2.2.symm⟩
    | zero =>
      have hz : fourier F T 0 = 0 := by
        funext y
        simp [fourier, PoissonS.fourierIntegral]
      simp only [hz]
      exact ⟨integrable_zero _ _ _, summable_zero, summable_zero, trivial⟩
    | add f g hf hg ihf ihg =>
      rcases ihf with ⟨hfi, hfs, hfh, hfp⟩
      rcases ihg with ⟨hgi, hgs, hgh, hgp⟩
      have hh := fourier_add T f g hfi hgi
      refine ⟨hfi.add hgi, hfs.add hgs, ?_, ?_⟩
      · simpa only [hh, Pi.add_apply] using hfh.add hgh
      · simp only [hh, theta, Pi.add_apply]
        rw [hfh.tsum_add hgh, hfs.tsum_add hgs]
        exact congrArg₂ (· + ·) hfp hgp
    | smul c f hf ih =>
      rcases ih with ⟨hi, hs, hh, hp⟩
      refine ⟨hi.smul c, ?_, ?_, ?_⟩
      · simpa only [Pi.smul_apply, smul_eq_mul] using hs.mul_left c
      · simpa only [theta_symmetry_fourier_smul, Pi.smul_apply, smul_eq_mul] using hh.mul_left c
      · simpa only [theta_symmetry_fourier_smul, theta, Pi.smul_apply, smul_eq_mul, tsum_mul_left] using
          congrArg (c * ·) hp
  exact (hmain f hf).2.2.2

end DedekindZetaZeroFree.QuadraticRawProduct

end

end

section

noncomputable section
open scoped NumberField Classical Valued SchwartzMap
open WithZero Multiplicative
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.SArithmeticData

variable {F : Type} [Field F] [NumberField F]

abbrev QuadraticGlobalPlace (F : Type) [Field F] [NumberField F] :=
  InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

def globalQuadraticGamma (A : SArithmeticData F) (a : Fˣ) :
    QuadraticGlobalPlace F → ℂ
  | Sum.inl v => A.complexGamma v
      (Units.map (algebraMap F v.Completion).toMonoidHom a)
  | Sum.inr v => A.finiteGamma v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)

def globalQuadraticWeilPhase (A : SArithmeticData F) (a : Fˣ)
    (v : QuadraticGlobalPlace F) : ℂ :=
  A.globalQuadraticGamma a v / A.globalQuadraticGamma 1 v

theorem globalQuadraticGamma_infinite (A : SArithmeticData F) (a : Fˣ)
    (w : InfinitePlace F) : A.globalQuadraticGamma a (Sum.inl w) = 1 := rfl

theorem globalQuadraticGamma_finprod_eq_finite (A : SArithmeticData F) (a : Fˣ) :
    (∏ᶠ v : QuadraticGlobalPlace F, A.globalQuadraticGamma a v) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        A.finiteGamma v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := by
  have hsub : Function.mulSupport (A.globalQuadraticGamma a) ⊆
      Set.range (Sum.inr : HeightOneSpectrum (𝓞 F) → QuadraticGlobalPlace F) := by
    intro x hx
    cases x with
    | inl w => exact absurd (A.globalQuadraticGamma_infinite a w) hx
    | inr v => exact ⟨v, rfl⟩
  calc ∏ᶠ v : QuadraticGlobalPlace F, A.globalQuadraticGamma a v
      = ∏ᶠ v ∈ Set.range
          (Sum.inr : HeightOneSpectrum (𝓞 F) → QuadraticGlobalPlace F),
            A.globalQuadraticGamma a v := by
        rw [← finprod_mem_univ (A.globalQuadraticGamma a)]
        exact finprod_mem_inter_mulSupport_eq' _ _ _
          (fun x hx => ⟨fun _ => hsub hx, fun _ => trivial⟩)
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          A.finiteGamma v
            (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := by
        rw [finprod_mem_range Sum.inr_injective]
        rfl

private theorem globalGamma_conductorZero (v : HeightOneSpectrum (𝓞 F)) (hself : ResidueTrace.IsSelfDual v)
    (π : v.adicCompletionIntegers F) (hπ : Irreducible π) :
    OddTraceConductor v π hπ 0 := by
  constructor
  · intro x
    simpa using (hself 1).mpr (by simp) x
  · have hnot : ((↑(oddUniformizerUnit v π hπ)⁻¹) :
        v.adicCompletion F) ∉ v.adicCompletionIntegers F := by
      intro hm
      apply hπ.not_isUnit
      apply isUnit_iff_exists_inv.mpr
      refine ⟨⟨_, hm⟩, ?_⟩
      apply Subtype.ext
      exact (oddUniformizerUnit v π hπ).val_inv
    have ht := mt (hself ((↑(oddUniformizerUnit v π hπ)⁻¹) : v.adicCompletion F)).mp hnot
    push Not at ht
    simpa using ht

private theorem globalGamma_localUnit (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (hval : v.valuation F (a : F) = 1) :
    ∃ u : (v.adicCompletionIntegers F)ˣ,
      oddLocalUnit v u = Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a := by
  let b := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  have hv : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (b : v.adicCompletion F) = 1 := by
    change (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
      (algebraMap F (v.adicCompletion F) (a : F)) = 1
    exact (HeightOneSpectrum.adicCompletion.valued_coe F v (a : F)).trans hval
  have hm : (b : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hv.le
  have hi : (↑b⁻¹ : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    change (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (↑b⁻¹ : v.adicCompletion F) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  refine ⟨⟨⟨_, hm⟩, ⟨_, hi⟩, ?_, ?_⟩, ?_⟩
  · exact Subtype.ext b.val_inv
  · exact Subtype.ext b.inv_val
  · exact Units.ext rfl

private theorem globalGamma_odd (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∉ v.asIdeal) : ringChar (OddLocalResidue v) ≠ 2 := by
  let e : (𝓞 F ⧸ v.asIdeal) ≃+* OddLocalResidue v :=
    (finitePlaceIdealResidueEquivCompletion v).trans
      (IsLocalRing.ResidueField.mapEquiv (finitePlaceCompletionIntegerRingEquiv v))
  intro hc
  have hz : (2 : OddLocalResidue v) = 0 := by
    haveI : CharP (OddLocalResidue v) 2 := ringChar.of_eq hc
    exact CharP.cast_eq_zero _ 2
  have hq : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := e.injective (by simpa only [map_ofNat, map_zero] using hz)
  exact hv ((Ideal.Quotient.eq_zero_iff_mem).mp hq)

theorem finiteGamma_diagonal_eq_one_of_good (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hodd : (2 : 𝓞 F) ∉ v.asIdeal) (hself : ResidueTrace.IsSelfDual v)
    (a : Fˣ) (hval : v.valuation F (a : F) = 1) :
    A.finiteGamma v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  obtain ⟨u, hu⟩ := globalGamma_localUnit v a hval
  have hc := globalGamma_conductorZero v hself π hπ
  have he := A.finiteGamma_odd_evaluation v (globalGamma_odd v hodd) π hπ 0 hc u 0
  simpa [hu] using he

theorem finiteGamma_diagonal_cofinite (A : SArithmeticData F) (a : Fˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      A.finiteGamma v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) = 1 := by
  obtain ⟨T, hT⟩ := ArithmeticContext.exists_trace_exclusion_set F
  have hself : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ResidueTrace.IsSelfDual v := by
    have ht : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ T := by
      simpa using Filter.eventually_cofinite.mpr T.finite_toSet
    filter_upwards [ht] with v hv
    exact hT v hv
  have hodd : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (2 : 𝓞 F) ∉ v.asIdeal := by
    apply Filter.eventually_cofinite.mpr
    convert Ideal.finite_factors (show Ideal.span {(2 : 𝓞 F)} ≠ (0 : Ideal (𝓞 F)) by
      simp) using 1
    ext v
    simp only [Set.mem_setOf_eq, not_not, Ideal.dvd_span_singleton]
  filter_upwards [hself, hodd, Detector.FrequencyDetection.valuation_unit_cofinite a] with v hs ho hv
  exact finiteGamma_diagonal_eq_one_of_good A v ho hs a hv

theorem globalQuadraticGamma_hasFiniteMulSupport (A : SArithmeticData F) (a : Fˣ) :
    Function.HasFiniteMulSupport (A.globalQuadraticGamma a) := by
  have hf : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      A.finiteGamma v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) := by
    exact Filter.eventually_cofinite.mp (finiteGamma_diagonal_cofinite A a)
  change (Function.mulSupport (A.globalQuadraticGamma a)).Finite
  apply (hf.image (Sum.inr : HeightOneSpectrum (𝓞 F) → QuadraticGlobalPlace F)).subset
  intro v hv
  cases v with
  | inl w => exact False.elim (hv (A.globalQuadraticGamma_infinite a w))
  | inr v => exact ⟨v, hv, rfl⟩

theorem exists_quadratic_auxiliary_set (A : SArithmeticData F) (a : Fˣ) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), A.Sf ⊆ T ∧
      PoissonS.ContainsDifferent F T ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
        (2 : 𝓞 F) ∉ v.asIdeal ∧ ResidueTrace.IsSelfDual v ∧
          v.valuation F (a : F) = 1 ∧ v.valuation F (2 * (a : F)) = 1 := by
  let two : Fˣ := Units.mk0 2 (by norm_num)
  obtain ⟨T₀, hT₀⟩ := ArithmeticContext.exists_trace_exclusion_set F
  have hg : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ResidueTrace.IsSelfDual v ∧ v.valuation F (a : F) = 1 ∧
        v.valuation F (2 * (a : F)) = 1 := by
    have ht : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v ∉ T₀ := by
      simpa using Filter.eventually_cofinite.mpr T₀.finite_toSet
    filter_upwards [ht, Detector.FrequencyDetection.valuation_unit_cofinite a,
      Detector.FrequencyDetection.valuation_unit_cofinite (two * a)] with v hv ha h2a
    exact ⟨hT₀ v hv, ha, h2a⟩
  let B := (Filter.eventually_cofinite.mp hg).toFinset
  let D := (Ideal.finite_factors
    (show differentIdeal ℤ (𝓞 F) ≠ (0 : Ideal (𝓞 F)) from differentIdeal_ne_bot)).toFinset
  refine ⟨A.Sf ∪ D ∪ B, ?_, ?_, ?_⟩
  · exact fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa [D] using hv))
  · intro v hv
    have hs : v ∉ A.Sf := fun hs => hv (Finset.mem_union_left _ (Finset.mem_union_left _ hs))
    have hb : v ∉ B := fun hb => hv (Finset.mem_union_right _ hb)
    have hgood : ResidueTrace.IsSelfDual v ∧ v.valuation F (a : F) = 1 ∧
        v.valuation F (2 * (a : F)) = 1 := by
      simpa [B] using hb
    refine ⟨?_, hgood⟩
    intro h2
    apply hs
    apply A.above_six
    convert v.asIdeal.mul_mem_left (3 : 𝓞 F) h2 using 1 <;> norm_num

theorem globalQuadraticGamma_finprod_eq_auxiliary (A : SArithmeticData F) (a : Fˣ)
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
      (2 : 𝓞 F) ∉ v.asIdeal ∧ ResidueTrace.IsSelfDual v ∧ v.valuation F (a : F) = 1) :
    (∏ᶠ v : QuadraticGlobalPlace F, A.globalQuadraticGamma a v) =
      ∏ v ∈ T, A.finiteGamma v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := by
  rw [A.globalQuadraticGamma_finprod_eq_finite a]
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hn
  obtain ⟨ho, hs, hu⟩ := hT v hn
  exact hv (A.finiteGamma_diagonal_eq_one_of_good v ho hs a hu)

theorem quadraticAuxiliary_productModule_eq_one
    (T : Finset (HeightOneSpectrum (𝓞 F))) (a : Fˣ)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → v.valuation F (a : F) = 1) :
    PoissonS.productModule F T (a : F) = 1 := by
  have hout (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
      FinitePlace.mk v (a : F) = 1 := by
    rw [FinitePlace.mk_apply, FinitePlace.norm_embedding,
      HeightOneSpectrum.adicAbv_def, hT v hv]
    simp
  have hfin : (∏ᶠ w : FinitePlace F, w (a : F)) =
      ∏ v ∈ T, FinitePlace.mk v (a : F) := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hn
    exact hv (hout v hn)
  unfold PoissonS.productModule
  rw [← hfin]
  exact NumberField.prod_abs_eq_one a.ne_zero

theorem globalQuadraticGamma_product (A : SArithmeticData F) (a : Fˣ) :
    Function.HasFiniteMulSupport (A.globalQuadraticGamma a) ∧
      (∏ᶠ v : QuadraticGlobalPlace F, A.globalQuadraticGamma a v) = 1 := by
  refine ⟨A.globalQuadraticGamma_hasFiniteMulSupport a, ?_⟩
  obtain ⟨T, _hSf, hdiff, hgood⟩ := A.exists_quadratic_auxiliary_set a
  have ha := fun v hv => (hgood v hv).2.2.1
  have h2a := fun v hv => (hgood v hv).2.2.2
  rw [A.globalQuadraticGamma_finprod_eq_auxiliary a T
    (fun v hv => ⟨(hgood v hv).1, (hgood v hv).2.1, ha v hv⟩)]
  let twoa : Fˣ := Units.mk0 (2 * (a : F)) (mul_ne_zero (by norm_num) a.ne_zero)
  have hmodule : PoissonS.productModule F T (2 * (a : F)) = 1 :=
    quadraticAuxiliary_productModule_eq_one T twoa h2a
  obtain ⟨hchirpa, hchirpb, hdilation⟩ :=
    QuadraticRawProduct.theta_auxiliary_symmetries T hdiff a ha h2a
  obtain ⟨f, hf, hnonzero⟩ := QuadraticRawProduct.exists_nonzero_theta (F := F) T
  have hFf := (QuadraticRawProduct.testSpace_stability A T 0 f hf).1
  have hMaFf := (QuadraticRawProduct.testSpace_stability A T (a : F)
    (QuadraticRawProduct.fourier F T f) hFf).2
  have hMbf := (QuadraticRawProduct.testSpace_stability A T (-1 / (4 * (a : F)))
    f hf).2
  have hkernel := congrArg (QuadraticRawProduct.theta F T)
    (QuadraticRawProduct.tensor_quadratic_operator A T a f hf)
  rw [QuadraticRawProduct.theta_fourier T hdiff _ hMaFf, hchirpa,
    QuadraticRawProduct.theta_fourier T hdiff _ hf,
    QuadraticRawProduct.theta_const_mul, hchirpb, hdilation,
    QuadraticRawProduct.theta_fourier T hdiff _ hMbf, hchirpb] at hkernel
  simp only [hmodule, Real.sqrt_one, inv_one, Complex.ofReal_one, mul_one] at hkernel
  exact (mul_eq_right₀ hnonzero).mp hkernel.symm

theorem globalQuadraticWeilPhase_product (A : SArithmeticData F) (a : Fˣ) :
    Function.HasFiniteMulSupport (A.globalQuadraticWeilPhase a) ∧
      (∏ᶠ v : QuadraticGlobalPlace F, A.globalQuadraticWeilPhase a v) = 1 := by
  obtain ⟨hfa, hpa⟩ := A.globalQuadraticGamma_product a
  obtain ⟨hf1, hp1⟩ := A.globalQuadraticGamma_product 1
  have hdiv : A.globalQuadraticWeilPhase a =
      A.globalQuadraticGamma a / A.globalQuadraticGamma 1 := rfl
  constructor
  · rw [hdiv]
    exact hfa.div hf1
  · rw [hdiv]
    simp only [Pi.div_apply]
    rw [finprod_div_distrib hfa hf1, hpa, hp1, div_one]

end DedekindZetaZeroFree.SArithmeticData

end

end
