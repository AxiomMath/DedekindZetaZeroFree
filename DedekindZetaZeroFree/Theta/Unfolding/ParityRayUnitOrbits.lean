module

public import DedekindZetaZeroFree.Adeles.Lattices.NormalizedRayCosetLattice
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.RayLatticePeriodization
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitHalfOpenDomain
public import DedekindZetaZeroFree.Arithmetic.Units.RayUnitTorsionFibers

@[expose] public section

noncomputable section

open Classical NumberField

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable {K : Type} [Field K] [NumberField K]

def orbitRepresentative (D : Data K) (x : X D) : Cx D := Quotient.out x

@[simp] theorem orbitMk_orbitRepresentative (D : Data K) (x : X D) :
    orbitMk D (orbitRepresentative D x) = x := Quotient.out_eq x

theorem orbitParametrization_bijective (D : Data K) (ρ : X D → Cx D)
    (hρ : ∀ x, orbitMk D (ρ x) = x) :
    Function.Bijective (fun p : X D × U K D.m => p.2 • ρ p.1) := by
  constructor
  · rintro ⟨x, u⟩ ⟨y, v⟩ h
    change u • ρ x = v • ρ y at h
    have horb (z : X D) (w : U K D.m) : orbitMk D (w • ρ z) = z := by
      calc
        orbitMk D (w • ρ z) = orbitMk D (ρ z) := Quotient.sound ⟨w, rfl⟩
        _ = z := hρ z
    have hxy : x = y := by
      rw [← horb x u, ← horb y v, h]
    subst y
    have hv : (u.val : 𝓞 K) = (v.val : 𝓞 K) :=
      mul_right_cancel₀ ((mem_Cnonzero_iff D _).mp (ρ x).property).2
        (congrArg Subtype.val h)
    have huv : u = v := Subtype.ext (Units.val_injective hv)
    subst v
    rfl
  · intro α
    have h : orbitMk D α = orbitMk D (ρ (orbitMk D α)) := (hρ _).symm
    obtain ⟨u, hu⟩ := Quotient.exact h
    exact ⟨(orbitMk D α, u), hu⟩

def orbitProductEquiv (D : Data K) (ρ : X D → Cx D)
    (hρ : ∀ x, orbitMk D (ρ x) = x) : X D × U K D.m ≃ Cx D :=
  Equiv.ofBijective (fun p => p.2 • ρ p.1)
    (orbitParametrization_bijective D ρ hρ)

@[simp] theorem orbitProductEquiv_apply (D : Data K) (ρ : X D → Cx D)
    (hρ : ∀ x, orbitMk D (ρ x) = x) (x : X D) (u : U K D.m) :
    orbitProductEquiv D ρ hρ (x,u) = u • ρ x := rfl

def chosenOrbitProductEquiv (D : Data K) : X D × U K D.m ≃ Cx D :=
  orbitProductEquiv D (orbitRepresentative D) (orbitMk_orbitRepresentative D)

theorem rayUnitLogMap_surjective (m : Ideal (𝓞 K)) :
    Function.Surjective (rayUnitLogMap K m) := by
  intro γ
  obtain ⟨u, hu⟩ := (rayUnitLogEmbedding K m).surjective_rangeRestrict γ.toAdd
  exact ⟨u.toMul, congrArg Multiplicative.ofAdd hu⟩

def absEmbedding (m : Ideal (𝓞 K)) (u : U K m) : InfinitePlace K → ℝ :=
  fun v => v (((u : (𝓞 K)ˣ) : 𝓞 K) : K)

private theorem Q_smul (q : InfinitePlace K → ℝ) (r : ℝ)
    (x : NumberField.mixedEmbedding.euclidean.mixedSpace K) :
    RayParity.Q K q (r • x) = r • RayParity.Q K q x := by
  apply (Theta.traceToMixed K).injective
  simp only [RayParity.Q, ContinuousLinearEquiv.apply_symm_apply, map_smul]
  ext v <;> simp [NumberField.mixedEmbedding.mixedSpaceOfRealSpace, mul_smul_comm]

private theorem Q_realCoordinate (q : InfinitePlace K → ℝ)
    (x : NumberField.mixedEmbedding.euclidean.mixedSpace K) (v : RealPlaces K) :
    Theta.traceRealCoordinateCLM K v (RayParity.Q K q x) =
      q v * Theta.traceRealCoordinateCLM K v x := by
  rw [RayParity.traceRealCoordinateCLM_eq_traceToMixed,
    RayParity.traceRealCoordinateCLM_eq_traceToMixed]
  simp [RayParity.Q, NumberField.mixedEmbedding.mixedSpaceOfRealSpace]

private theorem absEmbedding_real (m : Ideal (𝓞 K)) (u : U K m)
    (v : RealPlaces K) :
    absEmbedding m u v = realEmbedding K v (u.val : K) := by
  change v.val (u.val : K) = _
  rw [← InfinitePlace.norm_embedding_of_isReal v.property, Real.norm_eq_abs]
  exact abs_of_pos (u.property.2 (realEmbedding K v))

private theorem norm_Q_normalized (D : Data K) (q : InfinitePlace K → ℝ)
    (hq : ∀ v, q v ≠ 0) (α : 𝓞 K) :
    ‖RayParity.Q K q (normalizedEmbedding D α)‖ ^ 2 =
      normalizationScale D ^ 2 *
        ∑ v : InfinitePlace K, (v.mult : ℝ) * q v ^ 2 * (v (α : K)) ^ 2 := by
  rw [normalizedEmbedding_apply, Q_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, RayParity.Q_eq_traceRadialScale K q hq,
    Theta.norm_sq_traceRadialScale_traceEmbedding]

theorem gδ_normalizedEmbedding_smul (D : Data K)
    (δ : Finset (RealPlaces K)) (α : Cx D) (u : U K D.m)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, 0 < q v) :
    RayParity.gδ K δ
      (RayParity.Q K q (normalizedEmbedding D (u • α).val)) =
    RayParity.gδ K δ
      (RayParity.Q K (fun v => q v * absEmbedding D.m u v)
        (normalizedEmbedding D α.val)) := by
  have habs (v : InfinitePlace K) : 0 < absEmbedding D.m u v := by
    exact v.pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr u.val.ne_zero)
  have hq' : ∀ v, q v * absEmbedding D.m u v ≠ 0 :=
    fun v => ne_of_gt (mul_pos (hq v) (habs v))
  have hn : ‖RayParity.Q K q (normalizedEmbedding D (u • α).val)‖ ^ 2 =
      ‖RayParity.Q K (fun v => q v * absEmbedding D.m u v)
        (normalizedEmbedding D α.val)‖ ^ 2 := by
    rw [norm_Q_normalized D q (fun v => (hq v).ne'),
      norm_Q_normalized D _ hq', smul_val]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    simp only [map_mul, absEmbedding]
    ring
  unfold RayParity.gδ
  congr 1
  · apply Finset.prod_congr rfl
    intro v hv
    congr 1
    simp only [Q_realCoordinate, normalizedEmbedding_apply, map_smul,
      RayParity.traceRealCoordinateCLM_traceEmbedding, smul_val, map_mul,
      smul_eq_mul, absEmbedding_real]
    ring
  · simp only [Theta.latticeGaussian, ← Complex.ofReal_pow, hn]

theorem countable_Cx (D : Data K) : Countable (Cx D) := by
  letI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  letI : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  infer_instance

theorem countable_U (m : Ideal (𝓞 K)) : Countable (U K m) := by
  letI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  letI : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  letI : Countable ((𝓞 K)ˣ) := Units.val_injective.countable
  infer_instance

theorem countable_rayUnitLogLattice (m : Ideal (𝓞 K)) :
    Countable (rayUnitLogLattice K m) := by
  letI := countable_U (K := K) m
  have hc : Countable (Multiplicative (rayUnitLogLattice K m)) :=
    (rayUnitLogMap_surjective (K := K) m).countable
  exact Multiplicative.ofAdd.injective.countable

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
