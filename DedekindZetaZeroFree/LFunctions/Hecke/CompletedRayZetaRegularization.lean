module

public import DedekindZetaZeroFree.LFunctions.Hecke.RayGammaPoleRemoval
public import DedekindZetaZeroFree.Theta.Unfolding.NarrowRayParityProjection

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayCompletedRegularization

variable (K : Type) [Field K] [NumberField K]

def amplitude (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) : ℝ :=
  RayCoset.rayUnitDomainVolume K m hm /
    ((RayCoset.rayUnitTorsionCard K m : ℝ) * RayCoset.modulusCovolume K m)

def residue (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) : ℂ :=
  ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
    (amplitude K m hm : ℂ) * RayParity.hδ K ∅ 1

variable {K}

def Eδ (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) : ℂ → ℂ :=
  (RayTheta.Pδ D δ).Λ₀

theorem differentiable_Eδ (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) :
    Differentiable ℂ (Eδ D δ) := by
  exact (RayTheta.Pδ D δ).differentiable_Λ₀

theorem uncompleted_eq (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    RayCoset.Zδ D δ s = RayParity.hδ K δ s *
      (Eδ D δ s + RayParity.εδ K δ * RayTheta.g0δ D δ / (s - 1) -
        RayTheta.f0δ D δ / s) := by
  rw [← RayParity.SeriesMellin.uncompleted_eq D δ s hs]
  congr 1
  simp only [WeakFEPair.Λ, Eδ, RayTheta.Pδ_f₀, RayTheta.Pδ_g₀,
    RayTheta.Pδ_k, RayTheta.Pδ_ε, smul_eq_mul, Complex.ofReal_one]
  have hn : (1 : ℂ) - s = -(s - 1) := by ring
  rw [hn, div_neg]
  ring

theorem g0δ_empty_eq_amplitude (D : RayCoset.Data K) :
    RayTheta.g0δ D ∅ = (amplitude K D.m D.modulus_ne_bot : ℂ) := by
  simp [RayTheta.g0δ, amplitude]

def entirePart (D : RayCoset.Data K) : ℂ → ℂ :=
  fun s ↦ ((2 : ℂ) ^ NumberField.InfinitePlace.nrRealPlaces K)⁻¹ *
    ((∑ δ ∈ (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset,
        RayParity.hδ K δ s * Eδ D δ s) +
      (amplitude K D.m D.modulus_ne_bot : ℂ) *
        entireDividedDifference (RayParity.hδ K ∅) 1 s -
      RayTheta.f0δ D ∅ * entireDividedDifference (RayParity.hδ K ∅) 0 s)

theorem differentiable_entirePart (D : RayCoset.Data K) :
    Differentiable ℂ (entirePart D) := by
  unfold entirePart
  apply Differentiable.mul (differentiable_const _)
  apply Differentiable.sub
  · apply Differentiable.add
    · convert (Differentiable.sum
        (u := (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset)
        (fun δ _ => (RayParity.differentiable_hδ K δ).mul (differentiable_Eδ D δ))) using 1
      ext s
      simp
    · exact (differentiable_const _).mul
        (differentiable_entireDividedDifference _ (RayParity.differentiable_hδ K ∅) 1)
  · exact (differentiable_const _).mul
      (differentiable_entireDividedDifference _ (RayParity.differentiable_hδ K ∅) 0)

theorem hasSum (D : RayCoset.Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some c⁻¹)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum
      (fun I : Ideal (𝓞 K) =>
        if rayIdealClass K D.m D.modulus_ne_bot I = some c then
          (Ideal.absNorm I : ℂ) ^ (-s)
        else 0)
      (entirePart D s + residue K D.m D.modulus_ne_bot / (s - 1)) := by
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hs
  let A : ℂ := (amplitude K D.m D.modulus_ne_bot : ℂ)
  let B : ℂ := RayTheta.f0δ D ∅
  let T : ℂ := A * entireDividedDifference (RayParity.hδ K ∅) 1 s -
    B * entireDividedDifference (RayParity.hδ K ∅) 0 s +
    (A * RayParity.hδ K ∅ 1) / (s - 1)
  have hchannel (δ : Finset (RayCoset.RealPlaces K)) :
      RayCoset.Zδ D δ s = RayParity.hδ K δ s * Eδ D δ s +
        if δ = ∅ then T else 0 := by
    rw [uncompleted_eq D δ s hs]
    by_cases hd : δ = ∅
    · subst δ
      simp only [if_true, RayParity.εδ, Finset.card_empty, pow_zero, one_mul]
      rw [g0δ_empty_eq_amplitude]
      have h := RayGammaPoleRemoval.completed_pole_decomposition
        (RayParity.hδ K ∅) (Eδ D ∅) (RayParity.hδ_empty_zero K) A B s hs0 hs1
      convert h using 1 <;>
        dsimp [RayGammaPoleRemoval.completedEntirePart, T, A, B] <;> ring
    · have hne : δ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hd
      rw [RayTheta.g0δ_of_nonempty D δ hne, RayTheta.f0δ_of_nonempty D δ hne]
      simp [hd]
  have hsum :
      (∑ δ ∈ (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset,
        RayCoset.Zδ D δ s) =
      (∑ δ ∈ (Finset.univ : Finset (RayCoset.RealPlaces K)).powerset,
        RayParity.hδ K δ s * Eδ D δ s) + T := by
    simp_rw [hchannel]
    rw [Finset.sum_add_distrib]
    simp
  have hp := DedekindZetaZeroFree.rayParityProjection D c hc s hs
  rw [hsum] at hp
  convert hp using 1
  dsimp [entirePart, residue, T, A, B]
  ring

end DedekindZetaZeroFree.AbelianQuotient.RayCompletedRegularization

namespace DedekindZetaZeroFree

open AbelianQuotient

theorem rayCompletedRegularization (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    ∀ (D : RayCoset.Data K) (_hDm : D.m = m)
      (c : RayIdealClass K D.m D.modulus_ne_bot),
      rayIdealClass K D.m D.modulus_ne_bot D.a = some c⁻¹ →
      Differentiable ℂ (RayCompletedRegularization.entirePart D) ∧
        ∀ (s : ℂ), 1 < s.re →
          HasSum
            (fun I : Ideal (𝓞 K) =>
              if rayIdealClass K D.m D.modulus_ne_bot I = some c then
                (Ideal.absNorm I : ℂ) ^ (-s)
              else 0)
            (RayCompletedRegularization.entirePart D s +
              RayCompletedRegularization.residue K m hm / (s - 1)) := by
  intro D hDm c hc
  refine ⟨RayCompletedRegularization.differentiable_entirePart D, ?_⟩
  intro s hs
  have hres : RayCompletedRegularization.residue K D.m D.modulus_ne_bot =
      RayCompletedRegularization.residue K m hm := by
    subst m
    rfl
  rw [← hres]
  exact RayCompletedRegularization.hasSum D c hc s hs

end DedekindZetaZeroFree

end
