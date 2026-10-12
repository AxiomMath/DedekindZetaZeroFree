module

public import DedekindZetaZeroFree.Adeles.Lattices.ArchimedeanIdealCovolume
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalFieldBallInversion

@[expose] public section

section

noncomputable section
open scoped Classical nonZeroDivisors ENNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.Covolume

attribute [local instance] completionMeasurable completionBorel

namespace DilationArch

variable (F : Type) [Field F] [NumberField F]

theorem fieldModule_eq (a : F) :
    PoissonArch.fieldModule F a = ∏ v : InfinitePlace F, v a ^ v.mult := by
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  unfold PoissonArch.fieldModule
  congr 1
  · apply Fintype.prod_congr
    intro v
    simp only [InfinitePlace.mult_isReal, pow_one]
    simpa only [mixedEmbedding.mixedEmbedding_apply_isReal, Real.norm_eq_abs] using
      InfinitePlace.norm_embedding_of_isReal v.property a
  · apply Fintype.prod_congr
    intro v
    simp only [InfinitePlace.mult_isComplex, mixedEmbedding.mixedEmbedding_apply_isComplex,
      Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]

end DilationArch

def fieldDilation (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : Fˣ) :
    Space F S ≃ₜ+ Space F S where
  toFun x := (PoissonArch.fieldMul F (a : F) x.1,
    fun v => FinitePlace.embedding v.val (a : F) * x.2 v)
  invFun x := (PoissonArch.fieldMul F ((a⁻¹ : Fˣ) : F) x.1,
    fun v => FinitePlace.embedding v.val ((a⁻¹ : Fˣ) : F) * x.2 v)
  left_inv x := by
    apply Prod.ext
    · simp only [PoissonArch.fieldMul, ContinuousLinearEquiv.apply_symm_apply,
        ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul,
        ContinuousLinearEquiv.symm_apply_apply]
    · funext v
      simp only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul,
        ContinuousLinearEquiv.symm_apply_apply]
  right_inv x := by
    apply Prod.ext
    · simp only [PoissonArch.fieldMul, ContinuousLinearEquiv.apply_symm_apply,
        ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul,
        ContinuousLinearEquiv.symm_apply_apply]
    · funext v
      simp only [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul,
        ContinuousLinearEquiv.symm_apply_apply]
  map_add' x y := by
    apply Prod.ext
    · simp [PoissonArch.fieldMul, mul_add]
    · funext v
      simp only [Prod.snd_add, Pi.add_apply, mul_add]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (mixedEmbedding.euclidean.toMixed F).symm.continuous.comp
        (continuous_const.mul ((mixedEmbedding.euclidean.toMixed F).continuous.comp continuous_fst))
    · apply continuous_pi
      intro v
      exact continuous_const.mul ((continuous_apply v).comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact (mixedEmbedding.euclidean.toMixed F).symm.continuous.comp
        (continuous_const.mul ((mixedEmbedding.euclidean.toMixed F).continuous.comp continuous_fst))
    · apply continuous_pi
      intro v
      exact continuous_const.mul ((continuous_apply v).comp continuous_snd)

theorem fieldDilation_diagonal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : Fˣ) (x : F) :
    fieldDilation F S a (diagonalHom F S x) = diagonalHom F S ((a : F) * x) := by
  apply Prod.ext
  · simp [fieldDilation, diagonalHom, PoissonArch.fieldMul]
  · funext v
    simp [fieldDilation, diagonalHom, PoissonFinite.diagonal]

end DedekindZetaZeroFree.PoissonS.Covolume

end

end

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.Covolume

attribute [local instance] completionMeasurable completionBorel

end DedekindZetaZeroFree.PoissonS.Covolume

end

end

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.Covolume

attribute [local instance] completionMeasurable completionBorel

end DedekindZetaZeroFree.PoissonS.Covolume

end

end

section

noncomputable section
open scoped Classical nonZeroDivisors SchwartzMap
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree
namespace PoissonS

variable (F : Type) [Field F] [NumberField F]

local instance completionMeasurable (v : HeightOneSpectrum (RingOfIntegers F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance completionBorel (v : HeightOneSpectrum (RingOfIntegers F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

abbrev Space (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :=
  PoissonArch.Space F × PoissonFinite.Space F S

def diagonalHom (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : F →+ Space F S where
  toFun m := ((NumberField.mixedEmbedding.euclidean.toMixed F).symm
    (NumberField.mixedEmbedding F m), PoissonFinite.diagonal F S m)
  map_zero' := by
    apply Prod.ext
    · simp
    · funext v
      exact map_zero (NumberField.FinitePlace.embedding v.val)
  map_add' m n := by
    ext
    · simp
    · simp [PoissonFinite.diagonal]

def lattice (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : F) :
    AddSubgroup (Space F S) :=
  AddSubgroup.map ((diagonalHom F S).comp
    { toFun := fun m : F => a * m
      map_zero' := mul_zero a
      map_add' := fun m n => mul_add a m n })
    ((S : Set (HeightOneSpectrum (RingOfIntegers F))).integer F).toSubring.toAddSubgroup

def differentExponent (v : HeightOneSpectrum (RingOfIntegers F)) : ℤ :=
  FractionalIdeal.count F v (FractionalIdeal.coeIdeal (differentIdeal ℤ (RingOfIntegers F)))

def integerVolume (v : HeightOneSpectrum (RingOfIntegers F)) : ℝ :=
  ((v.asIdeal.absNorm : ℝ) ^ differentExponent F v).sqrt⁻¹

def ContainsDifferent (S : Finset (HeightOneSpectrum (RingOfIntegers F))) : Prop :=
  ∀ v, v.asIdeal ∣ differentIdeal ℤ (RingOfIntegers F) → v ∈ S

def productModule (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (a : F) : ℝ :=
  (∏ v : InfinitePlace F, v a ^ v.mult) * ∏ v ∈ S, FinitePlace.mk v a

def productMeasure (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F)) : Measure (Space F S) :=
  (PoissonArch.traceMeasure F).prod (Measure.pi μ)

def LocalNormalization (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F)) : Prop :=
  ∀ v, μ v {x | ‖x‖ ≤ 1} = ENNReal.ofReal (integerVolume F v.val)

theorem localMeasure_sigmaFinite
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ)
    (v : S) : SigmaFinite (μ v) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let t : F → Set (v.val.adicCompletion F) :=
    fun a => {x | ‖x - algebraMap F _ a‖ ≤ 1}
  apply Measure.sigmaFinite_of_countable (Set.countable_range t)
  · rintro s ⟨a, rfl⟩
    have ht : t a = (fun x => -algebraMap F (v.val.adicCompletion F) a + x) ⁻¹'
        {x | ‖x‖ ≤ 1} := by
      ext x
      simp only [t, Set.mem_setOf_eq, Set.mem_preimage, sub_eq_neg_add]
    rw [ht, measure_preimage_add, hnorm v]
    exact ENNReal.ofReal_lt_top
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha⟩ := (v.val.denseRange_algebraMap F).exists_dist_lt x
      (show (0 : ℝ) < 1 by norm_num)
    apply Set.mem_sUnion.mpr
    refine ⟨t a, Set.mem_range_self a, ?_⟩
    simpa only [t, Set.mem_setOf_eq, dist_eq_norm, norm_sub_rev] using ha.le

def fourierIntegral (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    (f : Space F S → ℂ) (y : Space F S) : ℂ :=
  ∫ x, f x *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
    ∏ v : S, (e v (-x.2 v * y.2 v) : ℂ) ∂productMeasure F S μ

theorem fourierIntegral_tensor_factorization
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ)
    (fArch : PoissonArch.Space F → ℂ)
    (φ : (v : S) → v.val.adicCompletion F → ℂ) (y : Space F S) :
    fourierIntegral F S e μ (fun z => fArch z.1 * ∏ v : S, φ v (z.2 v)) y =
      PoissonArch.traceFourier F fArch y.1 *
        ∏ v : S, ∫ z, φ v z * (e v (-z * y.2 v) : ℂ) ∂μ v := by
  letI : ∀ v : S, SigmaFinite (μ v) := localMeasure_sigmaFinite F S μ hnorm
  haveI : SFinite (PoissonArch.traceMeasure F) := by
    unfold PoissonArch.traceMeasure
    infer_instance
  unfold fourierIntegral productMeasure
  have hfun : (fun x : Space F S =>
      (fArch x.1 * ∏ v : S, φ v (x.2 v)) *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F x.1 y.1 : ℂ)) *
        ∏ v : S, (e v (-x.2 v * y.2 v) : ℂ)) =
      fun x => (fArch x.1 *
        Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (PoissonArch.tracePairing F x.1 y.1 : ℂ))) *
        (∏ v : S, φ v (x.2 v) * (e v (-x.2 v * y.2 v) : ℂ)) := by
    funext x
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun]
  have hi := integral_prod_mul
    (μ := PoissonArch.traceMeasure F) (ν := Measure.pi μ)
    (fun z => fArch z * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I *
      (PoissonArch.tracePairing F z y.1 : ℂ)))
    (fun z : PoissonFinite.Space F S => ∏ v : S, φ v (z v) * (e v (-z v * y.2 v) : ℂ))
  have hj := integral_fintype_prod_eq_prod (μ := μ)
    (fun (v : S) z => φ v z * (e v (-z * y.2 v) : ℂ))
  exact hi.trans (congrArg (fun c => PoissonArch.traceFourier F fArch y.1 * c) hj)

def TraceConductor (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle) : Prop :=
  ∀ v y, (∀ x : v.val.adicCompletion F, ‖x‖ ≤ 1 → e v (x * y) = 1) ↔
    ‖y‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val

end PoissonS
end DedekindZetaZeroFree

end

end
