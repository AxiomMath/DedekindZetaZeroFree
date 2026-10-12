module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.SIntegers.FundamentalDomainScaling
public import DedekindZetaZeroFree.Adeles.Lattices.SIntegerLocalProduct
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.Lattices.TranslateSummability

@[expose] public section

set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical nonZeroDivisors SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS

local instance productCompletionMeasurable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance productCompletionBorel (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem lc_of_test {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] {φ : G → ℂ} (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (hn : φ ≠ 0) : LocallyCompactSpace G := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    apply hn
    funext x
    simpa using (not_exists.mp h x)
  apply hc.isCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (x := x)
  have heq := hl.eventually_eq x
  apply Filter.mem_of_superset heq
  intro y hy
  exact subset_tsupport φ (by change φ y ≠ 0; rw [hy]; exact hx)

def tensorFunction (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ) : Space F S → ℂ :=
  fun x => fArch x.1 * ∏ v : S, φ v (x.2 v)

theorem tensorFunction_integrable
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    Integrable (tensorFunction F S fArch φ) (productMeasure F S μ) := by
  by_cases hz : ∃ v, φ v = 0
  · obtain ⟨v, hv⟩ := hz
    have hzero : tensorFunction F S fArch φ = 0 := by
      funext x
      simp only [tensorFunction, Pi.zero_apply]
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv]), mul_zero]
    rw [hzero]
    exact integrable_zero _ _ _
  have hn : ∀ v, φ v ≠ 0 := by simpa using hz
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI hv (v : S) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : S, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI (v : S) : LocallyCompactSpace (v.val.adicCompletion F) :=
    lc_of_test (hlocal v) (hsupport v) (hn v)
  letI : ∀ v : S, SigmaFinite (μ v) := fun v => inferInstance
  have harch : Integrable fArch (PoissonArch.traceMeasure F) := by
    exact fArch.integrable.smul_measure ENNReal.ofReal_ne_top
  have hfin : Integrable (fun x : PoissonFinite.Space F S => ∏ v : S, φ v (x v))
      (Measure.pi μ) :=
    Integrable.fintype_prod_dep (fun v =>
      (hlocal v).continuous.integrable_of_hasCompactSupport (hsupport v))
  exact harch.mul_prod hfin

set_option backward.isDefEq.respectTransparency false in

theorem fourierIntegral_tensorFunction
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (y : Space F S) :
    fourierIntegral F S e μ (tensorFunction F S fArch φ) y =
      PoissonArch.traceFourier F fArch y.1 *
        ∏ v : S, (∫ x, φ v x * (e v (-x * y.2 v) : ℂ) ∂μ v) := by
  by_cases hz : ∃ v, φ v = 0
  · obtain ⟨v, hv⟩ := hz
    have hzero : tensorFunction F S fArch φ = 0 := by
      funext x
      simp only [tensorFunction, Pi.zero_apply]
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv]), mul_zero]
    have hp : (∏ v : S, (∫ x, φ v x * (e v (-x * y.2 v) : ℂ) ∂μ v)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
    rw [hp, mul_zero, hzero]
    simp only [fourierIntegral, Pi.zero_apply, zero_mul, integral_zero]
  have hn : ∀ v, φ v ≠ 0 := by simpa using hz
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI (v : S) : TopologicalSpace.SeparableSpace (v.val.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.val.denseRange_algebraMap F)
  letI : ∀ v : S, SecondCountableTopology (v.val.adicCompletion F) := fun v => inferInstance
  letI (v : S) : LocallyCompactSpace (v.val.adicCompletion F) :=
    lc_of_test (hlocal v) (hsupport v) (hn v)
  letI : ∀ v : S, SigmaFinite (μ v) := fun v => inferInstance
  unfold fourierIntegral tensorFunction productMeasure
  have hfactor (x : Space F S) :
      (fArch x.1 * ∏ v : S, φ v (x.2 v)) *
          Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
            (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
          ∏ v : S, (e v (-x.2 v * y.2 v) : ℂ) =
      (fArch x.1 * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
            (PoissonArch.tracePairing F x.1 y.1 : ℂ))) *
          ∏ v : S, (φ v (x.2 v) * (e v (-x.2 v * y.2 v) : ℂ)) := by
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hfactor]
  letI : SFinite (PoissonArch.traceMeasure F) := by
    unfold PoissonArch.traceMeasure
    infer_instance
  have hi := integral_prod_mul
    (μ := PoissonArch.traceMeasure F) (ν := Measure.pi μ)
    (fun x : PoissonArch.Space F => fArch x * Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F x y.1 : ℂ)))
    (fun x : PoissonFinite.Space F S => ∏ v : S, φ v (x v) *
      (e v (-x v * y.2 v) : ℂ))
  refine hi.trans ?_
  congr 1
  exact integral_fintype_prod_eq_prod (μ := μ)
    (fun v x => φ v x * (e v (-x * y.2 v) : ℂ))

private theorem unique_fourier (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) [Unique S]
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F)) [∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, ∃ x, e v x ≠ 1)
    (φ : (default : S).val.adicCompletion F → ℂ) (hlocal : IsLocallyConstant φ)
    (hsupport : HasCompactSupport φ) :
    IsLocallyConstant (fun y => ∫ x, φ x * (e default (-x*y) : ℂ) ∂μ default) ∧
    HasCompactSupport (fun y => ∫ x, φ x * (e default (-x*y) : ℂ) ∂μ default) := by
  let h : PoissonFinite.Space F S ≃ₜ (default : S).val.adicCompletion F := Homeomorph.piUnique _
  let Φ : PoissonFinite.Space F S → ℂ := φ ∘ h
  have hΦlocal : IsLocallyConstant Φ := hlocal.comp_continuous h.continuous
  have hΦsupport : HasCompactSupport Φ := hsupport.comp_homeomorph h
  obtain ⟨U, hoU, hpU⟩ := PoissonFinite.BallExpansion.exists_open_phase_annihilator F S e he
    (tsupport Φ) hΦsupport.isCompact
  have hf := PoissonFinite.fourierIntegral_isLocallyConstant_of_open_phase F S e μ Φ U hoU
    (fun u hu x hx => hpU u hu x (subset_tsupport Φ hx))
  obtain ⟨V, hoV, hpV⟩ := PoissonFinite.BallExpansion.exists_open_period_subgroup F S Φ hΦlocal hΦsupport
  letI : ∀ v : S, SigmaCompactSpace (v.val.adicCompletion F) :=
    fun v => PoissonFinite.BallExpansion.finite_completion_sigmaCompact F v.val
  have hg := PoissonFinite.fourierIntegral_hasCompactSupport_of_period F S e μ Φ V hpV
    (PoissonFinite.BallExpansion.isCompact_phase_annihilator F S e he hne V hoV)
  have heq : (PoissonFinite.fourierIntegral F S e μ Φ) ∘ h.symm =
      (fun y => ∫ x, φ x * (e default (-x*y) : ℂ) ∂μ default) := by
    funext y
    unfold PoissonFinite.fourierIntegral
    simp only [Function.comp_apply, Fintype.prod_unique]
    exact (measurePreserving_piUnique μ).integral_comp
      (MeasurableEquiv.piUnique _).measurableEmbedding
      (fun x => φ x * (e default (-x*y) : ℂ))
  rw [← heq]
  exact ⟨hf.comp_continuous h.symm.continuous, hg.comp_homeomorph h.symm⟩
private theorem local_fourier (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : AddChar (v.adicCompletion F) Circle)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (he : Continuous e) (hne : ∃ x, e x ≠ 1)
    (φ : v.adicCompletion F → ℂ) (hlocal : IsLocallyConstant φ)
    (hsupport : HasCompactSupport φ) :
    IsLocallyConstant (fun y => ∫ x, φ x * (e (-x*y) : ℂ) ∂μ) ∧
    HasCompactSupport (fun y => ∫ x, φ x * (e (-x*y) : ℂ) ∂μ) := by
  let S : Finset (HeightOneSpectrum (RingOfIntegers F)) := {v}
  letI : Unique S := ⟨⟨⟨v, Finset.mem_singleton_self v⟩⟩,
    fun w => Subtype.ext (Finset.mem_singleton.mp w.property)⟩
  have hw (w : S) : w.val = v := Finset.mem_singleton.mp w.property
  let e' : (w : S) → AddChar (w.val.adicCompletion F) Circle :=
    fun w => (hw w) ▸ e
  let μ' : (w : S) → Measure (w.val.adicCompletion F) :=
    fun w => (hw w) ▸ μ
  let φ' : (default : S).val.adicCompletion F → ℂ := (hw default) ▸ φ
  letI (w : S) : (μ' w).IsAddHaarMeasure := by
    rcases w with ⟨w, hwm⟩
    have h : w = v := Finset.mem_singleton.mp hwm
    subst w
    exact inferInstance
  have he' (w : S) : Continuous (e' w) := by
    rcases w with ⟨w, hwm⟩
    have h : w = v := Finset.mem_singleton.mp hwm
    subst w
    exact he
  have hne' (w : S) : ∃ x, e' w x ≠ 1 := by
    rcases w with ⟨w, hwm⟩
    have h : w = v := Finset.mem_singleton.mp hwm
    subst w
    exact hne
  have hl : IsLocallyConstant φ' := by dsimp [φ']; cases hw default; exact hlocal
  have hs : HasCompactSupport φ' := by dsimp [φ']; cases hw default; exact hsupport
  have h := unique_fourier F S e' μ' he' hne' φ' hl hs
  have hv : (default : S).val = v := rfl
  change IsLocallyConstant (fun y : v.adicCompletion F =>
    ∫ x, φ x * (e (-x*y) : ℂ) ∂μ) ∧
    HasCompactSupport (fun y : v.adicCompletion F =>
    ∫ x, φ x * (e (-x*y) : ℂ) ∂μ)
  at h
  exact h

theorem fourierIntegral_tensor_bruhatSchwartz
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, ∃ x, e v x ≠ 1)
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) :
    ∃ (gArch : 𝓢(PoissonArch.Space F, ℂ))
      (ψ : (v : S) → v.val.adicCompletion F → ℂ),
      (∀ v, IsLocallyConstant (ψ v)) ∧ (∀ v, HasCompactSupport (ψ v)) ∧
      ∀ y, fourierIntegral F S e μ (tensorFunction F S fArch φ) y =
        tensorFunction F S gArch ψ y := by
  obtain ⟨gArch, hgArch⟩ := PoissonArch.traceFourier_schwartz F fArch
  let ψ : (v : S) → v.val.adicCompletion F → ℂ :=
    fun v y => ∫ x, φ v x * (e v (-x * y) : ℂ) ∂μ v
  have hψ (v : S) : IsLocallyConstant (ψ v) ∧ HasCompactSupport (ψ v) :=
    local_fourier F v.val (e v) (μ v) (he v) (hne v) (φ v) (hlocal v) (hsupport v)
  refine ⟨gArch, ψ, fun v => (hψ v).1, fun v => (hψ v).2, ?_⟩
  intro y
  rw [fourierIntegral_tensorFunction F S e μ he fArch φ hlocal hsupport y]
  simp only [tensorFunction, hgArch, ψ]

private theorem mk_injective (F : Type) [Field F] [NumberField F] :
    Function.Injective (PoissonArch.minkowskiEmbedding F) :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm.injective.comp
    (NumberField.mixedEmbedding_injective (K := F))
private theorem coset_sum (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (f : 𝓢(PoissonArch.Space F, ℂ))
    (I : FractionalIdeal (RingOfIntegers F)⁰ F) (hI : I ≠ 0) (t a : F) (ha : a ≠ 0) :
    Summable (fun m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F =>
      ‖f (PoissonArch.minkowskiEmbedding F (a * m)) * PoissonFinite.idealCosetIndicator F I t m‖) := by
  let J : PoissonArch.NonzeroFractionalIdeal F :=
    Units.mk0 (FractionalIdeal.spanSingleton (RingOfIntegers F)⁰ a * I)
      (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hI)
  let P := {m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F | (m : F) - t ∈ I}
  let idx : P → PoissonArch.idealLattice F J := fun m =>
    ⟨PoissonArch.minkowskiEmbedding F (a * ((m.val : F) - t)),
      (PoissonArch.mem_idealLattice F J _).mpr ⟨_,
        FractionalIdeal.mem_singleton_mul.mpr ⟨_, m.property, rfl⟩, rfl⟩⟩
  have hinj : Function.Injective idx := by
    intro m n h
    apply Subtype.ext
    apply Subtype.ext
    apply sub_left_injective (b := t)
    apply mul_left_cancel₀ ha
    exact mk_injective F (congrArg Subtype.val h)
  have hs := (PoissonArch.summable_norm_schwartz_translate (PoissonArch.idealLattice F J) f
    (PoissonArch.minkowskiEmbedding F (a*t))).comp_injective hinj
  have heq (m : P) : PoissonArch.minkowskiEmbedding F (a*t) + (idx m : PoissonArch.Space F) =
      PoissonArch.minkowskiEmbedding F (a * (m.val : F)) := by
    change _ + PoissonArch.minkowskiEmbedding F (a * ((m.val : F)-t)) = _
    rw [← map_add]
    congr 1
    ring
  simp only [Function.comp_def, heq] at hs
  have hs' := (summable_subtype_iff_indicator (s := P)
    (f := fun m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F =>
      ‖f (PoissonArch.minkowskiEmbedding F (a * m))‖)).mp
    (show Summable ((fun m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F =>
      ‖f (PoissonArch.minkowskiEmbedding F (a * m))‖) ∘ Subtype.val) from hs)
  refine hs'.congr ?_
  intro m
  by_cases hm : (m : F)-t ∈ I <;>
    simp [P, Set.indicator_apply, PoissonFinite.idealCosetIndicator, hm]
private theorem field_sum (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (a : F) (ha : a ≠ 0) :
    Summable (fun m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F =>
      ‖tensorFunction F S fArch φ ((diagonalHom F S) (a*m))‖) := by
  let φa : (v : S) → v.val.adicCompletion F → ℂ :=
    fun v x => φ v (FinitePlace.embedding v.val a * x)
  have hl (v : S) : IsLocallyConstant (φa v) :=
    (hlocal v).comp_continuous (continuous_const.mul continuous_id)
  have hs (v : S) : HasCompactSupport (φa v) :=
    (hsupport v).comp_homeomorph (Homeomorph.mulLeft₀ (FinitePlace.embedding v.val a)
      ((FinitePlace.embedding v.val).injective.ne (by simpa using ha)))
  obtain ⟨I, n, t, c, hI, hcoset⟩ := PoissonFinite.product_exists_ideal_coset_decomposition F S φa hl hs
  have hsum : Summable (fun m : (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F =>
      ∑ j, ‖c j‖ * ‖fArch (PoissonArch.minkowskiEmbedding F (a*m)) *
        PoissonFinite.idealCosetIndicator F I (t j) m‖) := by
    exact summable_sum (fun j _ => (coset_sum F S fArch I hI (t j) a ha).mul_left ‖c j‖)
  apply hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  have ht : tensorFunction F S fArch φ ((diagonalHom F S) (a*m)) =
      ∑ j, c j * (fArch (PoissonArch.minkowskiEmbedding F (a*m)) *
        PoissonFinite.idealCosetIndicator F I (t j) m) := by
    change fArch (PoissonArch.minkowskiEmbedding F (a*m)) *
      (∏ v : S, φ v (FinitePlace.embedding v.val (a*m))) = _
    simp only [map_mul]
    change fArch (PoissonArch.minkowskiEmbedding F (a*m)) *
      (∏ v : S, φa v (FinitePlace.embedding v.val m)) = _
    rw [hcoset, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ht]
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

theorem summable_norm_tensorFunction_lattice
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (a : F) (ha : a ≠ 0) :
    Summable (fun m : lattice F S a => ‖tensorFunction F S fArch φ m‖) := by
  let R := (S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F
  have hex (m : lattice F S a) : ∃ x : R, (diagonalHom F S) (a*x) = m.val := by
    obtain ⟨x, hx, hxm⟩ := AddSubgroup.mem_map.mp m.property
    exact ⟨⟨x, hx⟩, hxm⟩
  let idx : lattice F S a → R := fun m => (hex m).choose
  have hi (m : lattice F S a) : (diagonalHom F S) (a*idx m) = m.val := (hex m).choose_spec
  have hinj : Function.Injective idx := by
    intro m n h
    apply Subtype.ext
    rw [← hi m, ← hi n, h]
  have hs := (field_sum F S fArch φ hlocal hsupport a ha).comp_injective hinj
  simpa only [Function.comp_def, hi] using hs

theorem summable_norm_fourierIntegral_tensorFunction_lattice
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure]
    (he : ∀ v, Continuous (e v)) (hne : ∀ v, ∃ x, e v x ≠ 1)
    (fArch : 𝓢(PoissonArch.Space F, ℂ))
    (φ : (v : S) → v.val.adicCompletion F → ℂ)
    (hlocal : ∀ v, IsLocallyConstant (φ v))
    (hsupport : ∀ v, HasCompactSupport (φ v)) (a : F) (ha : a ≠ 0) :
    Summable (fun h : lattice F S a⁻¹ =>
      ‖fourierIntegral F S e μ (tensorFunction F S fArch φ) h‖) := by
  obtain ⟨gArch, ψ, hψlocal, hψsupport, htransform⟩ :=
    fourierIntegral_tensor_bruhatSchwartz F S e μ he hne fArch φ hlocal hsupport
  have hg := summable_norm_tensorFunction_lattice F S gArch ψ hψlocal hψsupport
    a⁻¹ (inv_ne_zero ha)
  simpa only [htransform] using hg

end DedekindZetaZeroFree.PoissonS

end
