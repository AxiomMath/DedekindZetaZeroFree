module

public import DedekindZetaZeroFree.Theta.Profiles.RayParityKernels

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace MeasureTheory
open NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable {K : Type} [Field K] [NumberField K]

def normalizationScale (D : Data K) : ℝ :=
  (Ideal.absNorm D.a : ℝ) ^ (-(Module.finrank ℚ K : ℝ)⁻¹)

theorem normalizationScale_pos (D : Data K) : 0 < normalizationScale D := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot)

private theorem normalizationScale_pow (D : Data K) :
    normalizationScale D ^ Module.finrank ℚ K = (Ideal.absNorm D.a : ℝ)⁻¹ := by
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have ha : 0 < (Ideal.absNorm D.a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot)
  rw [normalizationScale, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  simp [hn, Real.rpow_neg_one]

def normalizedEmbedding (D : Data K) : 𝓞 K →ₗ[ℤ] euclidean.mixedSpace K :=
  normalizationScale D •
    ((Theta.traceEmbeddingIntLinearMap K).comp
      ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ))

@[simp] theorem normalizedEmbedding_apply (D : Data K) (α : 𝓞 K) :
    normalizedEmbedding D α = normalizationScale D • Theta.traceEmbedding K (α : K) := by
  rfl

def normalizedLattice (D : Data K) : Submodule ℤ (euclidean.mixedSpace K) :=
  (D.a * D.m).restrictScalars ℤ |>.map (normalizedEmbedding D)

def normalizedBasepoint (D : Data K) : euclidean.mixedSpace K :=
  normalizedEmbedding D D.b

def normalizedAffineCoset (D : Data K) : Set (euclidean.mixedSpace K) :=
  {x | x - normalizedBasepoint D ∈ normalizedLattice D}

theorem normalizedEmbedding_bijOn (D : Data K) :
    Set.BijOn (normalizedEmbedding D) (C D) (normalizedAffineCoset D) := by
  have hi : Function.Injective (normalizedEmbedding D) := by
    intro x y h
    have ht : Theta.traceEmbedding K (x : K) = Theta.traceEmbedding K (y : K) :=
      (smul_right_injective _ (normalizationScale_pos D).ne').eq_iff.mp h
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    simpa [Theta.traceEmbedding] using congrArg (Theta.traceToMixed K) ht
  refine ⟨?_, hi.injOn, ?_⟩
  · intro α hα
    change normalizedEmbedding D α - normalizedEmbedding D D.b ∈ ((D.a * D.m).restrictScalars ℤ).map (normalizedEmbedding D)
    rw [← map_sub]
    exact Submodule.mem_map.mpr ⟨α - D.b, hα, rfl⟩
  · intro x hx
    change x - normalizedEmbedding D D.b ∈ ((D.a * D.m).restrictScalars ℤ).map (normalizedEmbedding D) at hx
    obtain ⟨α, hα, he⟩ := Submodule.mem_map.mp hx
    refine ⟨α + D.b, ?_, ?_⟩
    · change α + D.b - D.b ∈ D.a * D.m
      change α ∈ D.a * D.m at hα
      simpa only [add_sub_cancel_right] using hα
    · rw [map_add, he]
      abel

 def productIdealUnit (D : Data K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K ⟨D.a * D.m, by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact Ideal.mul_eq_bot.not.mpr (not_or.mpr ⟨D.ideal_ne_bot, D.modulus_ne_bot⟩)⟩

 def scaleEquiv (D : Data K) :
    euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  { LinearEquiv.smulOfNeZero ℝ (euclidean.mixedSpace K)
      (normalizationScale D) (normalizationScale_pos D).ne' with
    continuous_toFun := continuous_const.smul continuous_id
    continuous_invFun := continuous_const.smul continuous_id }

 theorem normalizedLattice_eq_comap (D : Data K) :
    normalizedLattice D = ZLattice.comap ℝ
      (Theta.traceIdealLattice K (productIdealUnit D)) (scaleEquiv D).symm.toLinearMap := by
  ext x
  change (∃ α ∈ D.a * D.m, normalizedEmbedding D α = x) ↔
    (scaleEquiv D).symm x ∈ Theta.traceIdealLattice K (productIdealUnit D)
  constructor
  · rintro ⟨α, hα, rfl⟩
    have he : (scaleEquiv D).symm (normalizedEmbedding D α) =
        Theta.traceEmbedding K (α : K) := by
      exact (scaleEquiv D).symm_apply_apply _
    rw [he, Theta.traceEmbedding_mem_traceIdealLattice, productIdealUnit,
      FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    exact ⟨α, hα, rfl⟩
  · intro hx
    obtain ⟨α, hα, he⟩ := Theta.exists_traceEmbedding_eq_of_mem_traceIdealLattice K _ hx
    rw [productIdealUnit, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hα
    obtain ⟨β, hβ, rfl⟩ := hα
    refine ⟨β, hβ, ?_⟩
    change (scaleEquiv D) (Theta.traceEmbedding K (β : K)) = x
    rw [he, ContinuousLinearEquiv.apply_symm_apply]

instance normalizedLattice_discrete (D : Data K) :
    DiscreteTopology (normalizedLattice D) := by
  rw [normalizedLattice_eq_comap]
  infer_instance

instance normalizedLattice_isZLattice (D : Data K) :
    IsZLattice ℝ (normalizedLattice D) := by
  simpa only [normalizedLattice_eq_comap] using
    (inferInstance : IsZLattice ℝ (ZLattice.comap ℝ
      (Theta.traceIdealLattice K (productIdealUnit D)) (scaleEquiv D).symm.toLinearMap))

def modulusCovolume (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) : ℝ :=
  (Ideal.absNorm m : ℝ) * ZLattice.covolume (Theta.traceIdealLattice K 1) volume

theorem modulusCovolume_pos (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    0 < modulusCovolume K m := by
  apply mul_pos _ (ZLattice.covolume_pos _ volume)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hm)

theorem covolume_normalizedLattice (D : Data K) :
    ZLattice.covolume (normalizedLattice D) volume = modulusCovolume K D.m := by
  have hd : (scaleEquiv D).toLinearMap = normalizationScale D • LinearMap.id := by
    ext x
    rfl
  have hs : LinearMap.det (scaleEquiv D).symm.toLinearMap =
      (LinearMap.det (scaleEquiv D).toLinearMap)⁻¹ :=
    LinearEquiv.det_coe_symm (scaleEquiv D).toLinearEquiv
  rw [normalizedLattice_eq_comap, Theta.covolume_comap_continuousLinearEquiv,
    hs, hd, LinearMap.det_smul, LinearMap.det_id,
    mul_one, euclidean.finrank, normalizationScale_pow, inv_inv,
    abs_of_nonneg (by positivity : 0 ≤ (Ideal.absNorm D.a : ℝ)),
    Theta.covolume_traceIdealLattice]
  unfold modulusCovolume
  rw [Theta.covolume_traceIdealLattice]
  simp only [productIdealUnit, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
    map_mul, Nat.cast_mul, Rat.cast_natCast, Units.val_one, map_one, Rat.cast_one, one_mul]
  have ha : (Ideal.absNorm D.a : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot
  simp only [Rat.cast_mul, Rat.cast_natCast]
  field_simp
  <;> ring

def archimedeanNorm (K : Type) [Field K] [NumberField K]
    (x : euclidean.mixedSpace K) : ℝ :=
  mixedEmbedding.norm (Theta.traceToMixed K x)

theorem archimedeanNorm_normalizedEmbedding (D : Data K) (α : 𝓞 K) :
    archimedeanNorm K (normalizedEmbedding D α) =
      |(Algebra.norm ℚ (α : K) : ℝ)| / (Ideal.absNorm D.a : ℝ) := by
  rw [archimedeanNorm, normalizedEmbedding_apply, map_smul,
    Theta.traceEmbedding, ContinuousLinearEquiv.apply_symm_apply, mixedEmbedding.norm_smul,
    abs_of_pos (normalizationScale_pos D), normalizationScale_pow,
    mixedEmbedding.norm_eq_norm]
  rw [div_eq_mul_inv, mul_comm]
  norm_cast

theorem normWeight_eq_archimedeanNorm (D : Data K) (α : Cx D) :
    normWeight D (orbitMk D α) =
      archimedeanNorm K (normalizedEmbedding D α.val) := by
  rw [normWeight_orbitMk, archimedeanNorm_normalizedEmbedding]
  rfl

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
