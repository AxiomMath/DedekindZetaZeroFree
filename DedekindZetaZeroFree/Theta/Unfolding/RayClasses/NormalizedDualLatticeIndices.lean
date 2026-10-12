module

public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.AffineResiduePackets

@[expose] public section

noncomputable section

open Classical
open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

theorem affineResidueScale_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    0 < affineResidueScale I := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (I : FractionalIdeal (𝓞 F)⁰ F))
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr (Units.ne_zero I)))

def commonNormalizedLattice (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Submodule ℤ (NumberField.mixedEmbedding.euclidean.mixedSpace F) :=
  (Theta.traceIdealLattice F (I * rayIdealFractionalIdeal F m hm)).map
    (affineResidueScale I •
      (LinearMap.id : NumberField.mixedEmbedding.euclidean.mixedSpace F →ₗ[ℤ]
        NumberField.mixedEmbedding.euclidean.mixedSpace F))

 theorem mem_commonDual_iff (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (v : NumberField.mixedEmbedding.euclidean.mixedSpace F) :
    v ∈ Theta.dualLattice (commonNormalizedLattice m hm I) ↔
      affineResidueScale I • v ∈ Theta.dualLattice
        (Theta.traceIdealLattice F (I * rayIdealFractionalIdeal F m hm)) := by
  rw [Theta.mem_dualLattice_iff, Theta.mem_dualLattice_iff]
  constructor
  · intro hv x
    obtain ⟨n, hn⟩ := hv ⟨affineResidueScale I • x.val,
      Submodule.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
    refine ⟨n, ?_⟩
    simpa only [real_inner_smul_left, real_inner_smul_right] using hn
  · intro hv x
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp x.property
    obtain ⟨n, hn⟩ := hv ⟨y, hy⟩
    refine ⟨n, ?_⟩
    change affineResidueScale I • y = x.val at he
    rw [← he, real_inner_smul_right]
    simpa only [real_inner_smul_left] using hn

 theorem commonDual_mem (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)}) :
    (affineResidueScale I)⁻¹ • Theta.traceConjugation F (Theta.traceEmbedding F β.val) ∈
      Theta.dualLattice (commonNormalizedLattice m hm I) := by
  rw [mem_commonDual_iff, smul_smul, mul_inv_cancel₀ (affineResidueScale_pos I).ne', one_smul,
    Theta.dualLattice_traceIdealLattice]
  exact Submodule.mem_map.mpr ⟨Theta.traceEmbedding F β.val,
    (Theta.traceEmbedding_mem_traceIdealLattice F _).mpr β.property, rfl⟩

def commonDualIndexEquiv (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    {β : F // β ∈ (Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)} ≃
      Theta.dualLattice (commonNormalizedLattice m hm I) := by
  refine Equiv.ofBijective (fun β ↦ ⟨_, commonDual_mem m hm I β⟩) ⟨?_, ?_⟩
  · intro β γ h
    apply Subtype.ext
    have h₁ := congrArg Subtype.val h
    have h₂ := (smul_right_injective _ (inv_ne_zero (affineResidueScale_pos I).ne')) h₁
    have h₃ := (Theta.traceConjugation F).injective h₂
    apply NumberField.mixedEmbedding_injective F
    simpa [Theta.traceEmbedding] using congrArg (Theta.traceToMixed F) h₃
  · intro v
    have hv := (mem_commonDual_iff m hm I v.val).mp v.property
    rw [Theta.dualLattice_traceIdealLattice] at hv
    obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp hv
    obtain ⟨β, hβ, hβw⟩ := Theta.exists_traceEmbedding_eq_of_mem_traceIdealLattice F _ hw
    refine ⟨⟨β, hβ⟩, ?_⟩
    apply Subtype.ext
    change (affineResidueScale I)⁻¹ • Theta.traceConjugation F (Theta.traceEmbedding F β) = v.val
    rw [hβw]
    change Theta.traceConjugation F w = affineResidueScale I • v.val at he
    rw [he, smul_smul, inv_mul_cancel₀ (affineResidueScale_pos I).ne', one_smul]

@[simp] theorem commonDualIndexEquiv_apply (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)}) :
    (commonDualIndexEquiv m hm I β :
      NumberField.mixedEmbedding.euclidean.mixedSpace F) =
      (affineResidueScale I)⁻¹ •
        Theta.traceConjugation F (Theta.traceEmbedding F β.val) := by
  rfl

theorem commonDualIndex_tracePhase (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (x : F)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)}) :
    Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
      (inner ℝ ((affineResidueScale I)⁻¹ •
        Theta.traceConjugation F (Theta.traceEmbedding F β.val))
        (affineResidueScale I • Theta.traceEmbedding F x) : ℂ)) =
      rationalTracePhase (Algebra.trace ℚ F (x * β.val)) := by
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    inv_mul_cancel₀ (affineResidueScale_pos I).ne', one_mul,
    real_inner_comm, Theta.inner_traceEmbedding_traceConjugation,
    rationalTracePhase_apply_real]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

theorem affineResidueScale_rayIdealFractionalIdeal
    (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) :
    affineResidueScale (rayIdealFractionalIdeal F a ha) =
      (Ideal.absNorm a : ℝ) ^ (-(Module.finrank ℚ F : ℝ)⁻¹) := by
  simp [affineResidueScale, FractionalIdeal.coeIdeal_absNorm]

theorem commonNormalizedLattice_eq_normalizedLattice (D : RayCoset.Data F) :
    commonNormalizedLattice D.m D.modulus_ne_bot
      (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) =
        RayCoset.normalizedLattice D := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨x, hx, rfl⟩ := Theta.exists_traceEmbedding_eq_of_mem_traceIdealLattice F _ hw
    rw [Units.val_mul, rayIdealFractionalIdeal_coe, rayIdealFractionalIdeal_coe,
      ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.mem_coeIdeal] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine Submodule.mem_map.mpr ⟨a, ha, ?_⟩
    change RayCoset.normalizationScale D • Theta.traceEmbedding F (a : F) =
      affineResidueScale (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) • Theta.traceEmbedding F (a : F)
    rw [affineResidueScale_rayIdealFractionalIdeal]
    rfl
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨Theta.traceEmbedding F (a : F), ?_, ?_⟩
    · apply (Theta.traceEmbedding_mem_traceIdealLattice F _).mpr
      rw [Units.val_mul, rayIdealFractionalIdeal_coe, rayIdealFractionalIdeal_coe,
        ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.mem_coeIdeal]
      exact ⟨a, ha, rfl⟩
    · change affineResidueScale (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) •
        Theta.traceEmbedding F (a : F) = RayCoset.normalizationScale D • Theta.traceEmbedding F (a : F)
      rw [affineResidueScale_rayIdealFractionalIdeal]
      rfl

def normalizedCosetDualIndexEquiv (D : RayCoset.Data F) :
    {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F D.a D.ideal_ne_bot *
        rayIdealFractionalIdeal F D.m D.modulus_ne_bot) :
          FractionalIdeal (𝓞 F)⁰ F)} ≃
      Theta.dualLattice (RayCoset.normalizedLattice D) :=
  (commonDualIndexEquiv D.m D.modulus_ne_bot
    (rayIdealFractionalIdeal F D.a D.ideal_ne_bot)).trans
    (Equiv.subtypeEquivRight (fun v ↦ by
      rw [commonNormalizedLattice_eq_normalizedLattice]))

@[simp] theorem normalizedCosetDualIndexEquiv_apply (D : RayCoset.Data F)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F D.a D.ideal_ne_bot *
        rayIdealFractionalIdeal F D.m D.modulus_ne_bot) :
          FractionalIdeal (𝓞 F)⁰ F)}) :
    (normalizedCosetDualIndexEquiv D β :
      NumberField.mixedEmbedding.euclidean.mixedSpace F) =
      (affineResidueScale (rayIdealFractionalIdeal F D.a D.ideal_ne_bot))⁻¹ •
        Theta.traceConjugation F (Theta.traceEmbedding F β.val) := by
  rfl

theorem normalizedCosetDualIndex_tracePhase (D : RayCoset.Data F)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F D.a D.ideal_ne_bot *
        rayIdealFractionalIdeal F D.m D.modulus_ne_bot) :
          FractionalIdeal (𝓞 F)⁰ F)}) :
    Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
      (inner ℝ (normalizedCosetDualIndexEquiv D β :
        NumberField.mixedEmbedding.euclidean.mixedSpace F)
        (RayCoset.normalizedBasepoint D) : ℂ)) =
      rationalTracePhase (Algebra.trace ℚ F ((D.b : F) * β.val)) := by
  rw [normalizedCosetDualIndexEquiv_apply]
  change Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
    (inner ℝ ((affineResidueScale (rayIdealFractionalIdeal F D.a D.ideal_ne_bot))⁻¹ •
      Theta.traceConjugation F (Theta.traceEmbedding F β.val))
      (RayCoset.normalizationScale D • Theta.traceEmbedding F (D.b : F)) : ℂ)) = _
  rw [RayCoset.normalizationScale, ← affineResidueScale_rayIdealFractionalIdeal D.a D.ideal_ne_bot]
  exact commonDualIndex_tracePhase D.m D.modulus_ne_bot
    (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) (D.b : F) β

end DedekindZetaZeroFree.Hecke.Theta

end
