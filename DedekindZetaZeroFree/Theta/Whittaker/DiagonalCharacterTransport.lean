module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalCompactOpenAnnihilators
public import DedekindZetaZeroFree.Adeles.Characters.LocalAdditiveCharacterSmoothness
public import DedekindZetaZeroFree.Metaplectic.Kubota.BruhatLiftsAndScalarQuotients
public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.ProjectorGermsAndFrequencySupport

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.RawTransport
private theorem scalar_on_ball (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (χ : AddChar (v.adicCompletion F) Circle)
    (hc : Continuous χ) (n : ℤ) :
    ∃ y : v.adicCompletion F, ∀ x ∈ finiteCompletionBall F v n,
      χ x = localFiniteCharacter F v (x * y) := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  letI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  letI := localNormalizedHaar_isAddHaarMeasure F v
  let U := finiteCompletionBall F v n
  let f : v.adicCompletion F → ℂ := fun x => (χ x : ℂ) * localCosetIndicator F v 0 U x
  have hχlc : IsLocallyConstant χ := by
    obtain ⟨r, hr, hb⟩ := KPFiniteLocal.character_trivial_near_zero χ hc
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    have h := hb (y-x) (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
    rwa [AddChar.map_sub_eq_div, div_eq_one] at h
  have hf : f ∈ localSchwartz F v := by
    have hi := localCosetIndicator_mem_localSchwartz F v U
      (isCompact_finiteCompletionBall F v n) (isOpen_finiteCompletionBall F v n) 0
    exact ⟨(hχlc.comp (fun z : Circle => (z : ℂ))).mul hi.1, hi.2.mul_left⟩
  have hn : ∃ y, localFourierIntegral F v f y ≠ 0 := by
    by_contra h
    have hz : localFourierIntegral F v f = 0 := by
      ext y
      simpa using (not_exists.mp h y)
    have h := congrFun (localInverseFourierIntegral_fourierIntegral F v f hf) 0
    rw [hz] at h
    simp [localInverseFourierIntegral, localFourierIntegral_apply, f, U,
      localCosetIndicator_apply] at h
  obtain ⟨y, hy⟩ := hn
  let δ : AddChar (v.adicCompletion F) Circle :=
    χ * (localFiniteCharacter F v).mulShift (-y)
  have hδ : Continuous δ := hc.mul ((continuous_localFiniteCharacter F v).comp
    (continuous_const.mul continuous_id))
  have heq : localFourierIntegral F v f y =
      ∫ x in (U : Set (v.adicCompletion F)), (δ x : ℂ) ∂localNormalizedHaar F v := by
    rw [localFourierIntegral_apply, ← integral_indicator (isCompact_finiteCompletionBall F v n).measurableSet]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ finiteCompletionBall F v n
    · simp [f, U, localCosetIndicator_apply, hx, Set.indicator_of_mem,
        δ, AddChar.mulShift_apply, mul_comm, mul_assoc]
      exact hx
    · simp [f, U, localCosetIndicator_apply, hx, Set.indicator_of_notMem]
      exact lt_of_not_ge hx
  rw [heq, (compactSubgroup_character_integral (localNormalizedHaar F v) U
    (isCompact_finiteCompletionBall F v n) δ hδ).2] at hy
  have ht : ∀ x ∈ U, δ x = 1 := by
    by_contra h
    simp [h] at hy
  refine ⟨y, fun x hx => ?_⟩
  have h := ht x hx
  change χ x * localFiniteCharacter F v (-y * x) = 1 at h
  have ha : -y * x = -(x * y) := by ring
  rw [ha, AddChar.map_neg_eq_inv, mul_inv_eq_one] at h
  exact h
theorem scalar_global (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (χ : AddChar (v.adicCompletion F) Circle)
    (hc : Continuous χ) :
    ∃ y : v.adicCompletion F, ∀ x, χ x = localFiniteCharacter F v (x * y) := by
  obtain ⟨r, hr, hb⟩ := KPFiniteLocal.character_trivial_near_zero χ hc
  obtain ⟨m, _, hm⟩ := (finiteCompletionBall_hasBasis_nhds F v 0).mem_iff.mp
    (Metric.ball_mem_nhds (0 : v.adicCompletion F) hr)
  have hk : ∀ x ∈ finiteCompletionBall F v m, χ x = 1 := by
    intro x hx
    apply hb
    simpa only [Metric.mem_ball, dist_zero_right] using hm (by simpa using hx)
  let S : ℕ → Set (v.adicCompletion F) := fun n =>
    {y | ∀ x ∈ finiteCompletionBall F v (m - n), χ x = localFiniteCharacter F v (x * y)}
  have hscl (n : ℕ) : IsClosed (S n) := by
    have heq : S n = ⋂ x : finiteCompletionBall F v (m - n),
        {y | χ x.val = localFiniteCharacter F v (x.val * y)} := by
      ext y
      simp only [S, Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x, hx⟩⟩
    rw [heq]
    apply isClosed_iInter
    intro x
    exact isClosed_eq continuous_const ((continuous_localFiniteCharacter F v).comp
      (continuous_const.mul continuous_id))
  have hsne (n : ℕ) : (S n).Nonempty := scalar_on_ball F v χ hc (m-n)
  have hs0 : S 0 = (localFiniteAnnihilator F v (finiteCompletionBall F v m) : Set _) := by
    ext y
    simp only [S, Nat.cast_zero, sub_zero, Set.mem_setOf_eq, SetLike.mem_coe,
      mem_localFiniteAnnihilator]
    exact ⟨fun h x hx => (h x hx).symm.trans (hk x hx),
      fun h x hx => (hk x hx).trans (h x hx).symm⟩
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (by
      intro n y hy x hx
      exact hy x ((finiteCompletionBall_le_iff F v _ _).mpr (by omega) hx))
    hsne (by
      rw [hs0]
      exact isCompact_localFiniteAnnihilator F v _
        (isCompact_finiteCompletionBall F v m) (isOpen_finiteCompletionBall F v m)) hscl
  refine ⟨y, fun x => ?_⟩
  have hu : x ∈ ⋃ n : ℕ, (finiteCompletionBall F v (-(n : ℤ)) : Set _) := by
    rw [iUnion_finiteCompletionBall_neg_nat]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu
  exact (Set.mem_iInter.mp hy (n + m.toNat)) x
    ((finiteCompletionBall_le_iff F v _ _).mpr (by omega) hn)

theorem conjugation_quotient
    {G N V : Type*} [Group G] [Group N] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (n : N →* G) (ψ η : N →* ℂˣ)
    (s : N ≃* N) (g : G)
    (hc : ∀ x, g * n x = n (s x) * g)
    (hψ : ∀ x, ψ x = η (s x)) :
    Nonempty (RootCoinvariants ρ n ψ ≃ₗ[ℂ] RootCoinvariants ρ n η) := by
  let α := rootTwistedRepresentation ρ n ψ
  let β := rootTwistedRepresentation ρ n η
  have hf (x : N) (v : V) : ρ g (α x v) = β (s x) (ρ g v) := by
    dsimp [α, β, rootTwistedRepresentation]
    rw [map_smul, hψ x]
    congr 1
    change ((ρ g * ρ (n x)) v) = ((ρ (n (s x)) * ρ g) v)
    rw [← map_mul, ← map_mul, hc]
  have hi (x : N) (v : V) : ρ g⁻¹ (β x v) = α (s.symm x) (ρ g⁻¹ v) := by
    apply (Representation.apply_bijective ρ g).injective
    change ρ g (ρ g⁻¹ (β x v)) = ρ g (α (s.symm x) (ρ g⁻¹ v))
    rw [hf, s.apply_symm_apply]
    simp [← Module.End.mul_apply, ← mul_assoc, ← map_mul, α, β]
  let f : α.Coinvariants →ₗ[ℂ] β.Coinvariants :=
    Representation.Coinvariants.lift α
      ((Representation.Coinvariants.mk β).comp (ρ g)) (by
        intro x
        ext v
        simp only [LinearMap.comp_apply, hf, Representation.Coinvariants.mk_self_apply])
  let i : β.Coinvariants →ₗ[ℂ] α.Coinvariants :=
    Representation.Coinvariants.lift β
      ((Representation.Coinvariants.mk α).comp (ρ g⁻¹)) (by
        intro x
        ext v
        simp only [LinearMap.comp_apply, hi, Representation.Coinvariants.mk_self_apply])
  refine ⟨{ f with invFun := i, left_inv := ?_, right_inv := ?_ }⟩
  · intro v
    induction v using Representation.Coinvariants.induction_on with
    | h v =>
      change Representation.Coinvariants.mk α (ρ g⁻¹ (ρ g v)) = _
      simp [← Module.End.mul_apply, ← mul_assoc, ← map_mul, α, β]
  · intro v
    induction v using Representation.Coinvariants.induction_on with
    | h v =>
      change Representation.Coinvariants.mk β (ρ g (ρ g⁻¹ v)) = _
      simp [← Module.End.mul_apply, ← mul_assoc, ← map_mul, α, β]

theorem character_scalar (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F)) (χ : AddChar (q.adicCompletion F) ℂˣ)
    (hc : Continuous χ) (hne : χ ≠ 1) :
    ∃ a : (q.adicCompletion F)ˣ, ∀ x,
      χ x = Circle.toUnits (localFiniteCharacter F q ((a : q.adicCompletion F) * x)) := by
  let χC := KPJacquetCharacter.circleCharacter F q χ hc
  obtain ⟨a, ha⟩ := scalar_global F q χC
    (KPJacquetCharacter.continuous_circleCharacter F q χ hc)
  have hphase (x : q.adicCompletion F) :
      χ x = Circle.toUnits (localFiniteCharacter F q (x * a)) := by
    apply Units.ext
    exact congrArg (fun z : Circle => (z : ℂ)) (ha x)
  have hane : a ≠ 0 := by
    intro hz
    apply hne
    ext x
    simp [hphase, hz]
  refine ⟨Units.mk0 a hane, fun x => ?_⟩
  change χ x = Circle.toUnits (localFiniteCharacter F q (a * x))
  simpa only [mul_comm] using hphase x

theorem actual_character_quotient
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ q) V)
    (χ : AddChar (q.adicCompletion F) ℂˣ) (hc : Continuous χ) (hne : χ ≠ 1) :
    Nonempty (RootCoinvariants ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
      χ.toMonoidHom ≃ₗ[ℂ]
      RootCoinvariants ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
        (KPKirillovProjectorGerms.frequencyCharacter F q 1)) := by
  obtain ⟨u, hu⟩ := character_scalar F q χ hc hne
  let a : q.adicCompletion F := u
  have hane : a ≠ 0 := u.ne_zero
  let s : Multiplicative (q.adicCompletion F) ≃* Multiplicative (q.adicCompletion F) :=
    { toFun := fun x => Multiplicative.ofAdd (a * Multiplicative.toAdd x)
      invFun := fun x => Multiplicative.ofAdd (a⁻¹ * Multiplicative.toAdd x)
      left_inv := by intro x; simp [← mul_assoc, hane]
      right_inv := by intro x; simp [← mul_assoc, hane]
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd (a * (x.toAdd + y.toAdd)) = _
        simp [mul_add] }
  have hconj (x : Multiplicative (q.adicCompletion F)) :
      KPPGLLocalCover.A F ζ hζ (Sum.inr q) u *
        KPLocalSmoothRepresentation.upperRoot F ζ hζ q x =
      KPLocalSmoothRepresentation.upperRoot F ζ hζ q (s x) *
        KPPGLLocalCover.A F ζ hζ (Sum.inr q) u := by
    have h := congrArg (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q))
      (KPCorrectedBruhatLifts.upper_diagonal F ζ hζ (Sum.inr q) (a * x.toAdd) u)
    simp only [map_mul] at h
    change KPPGLLocalCover.A F ζ hζ (Sum.inr q) u * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x.toAdd =
      KPPGLLocalCover.N F ζ hζ (Sum.inr q) (a * x.toAdd) * KPPGLLocalCover.A F ζ hζ (Sum.inr q) u
    simpa [KPPGLLocalCover.N, KPPGLLocalCover.A, a, mul_div_cancel_left₀ _ u.ne_zero] using h.symm
  exact conjugation_quotient ρ (KPLocalSmoothRepresentation.upperRoot F ζ hζ q)
    χ.toMonoidHom (KPKirillovProjectorGerms.frequencyCharacter F q 1)
    s (KPPGLLocalCover.A F ζ hζ (Sum.inr q) u) hconj (by
      intro x
      change χ x.toAdd = Circle.toUnits (localFiniteCharacter F q (1 * (a * x.toAdd)))
      simpa only [one_mul] using hu x.toAdd)

end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.TameWhittakerSteps.RawTransport

end
