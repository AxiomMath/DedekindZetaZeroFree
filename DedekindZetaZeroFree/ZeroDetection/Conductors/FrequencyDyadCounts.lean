module

public import DedekindZetaZeroFree.Arithmetic.Ideals.ExteriorIdealAndRepresentativeCounting
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerPrincipalIdealIndex

@[expose] public section

open scoped NumberField
open IsDedekindDomain
namespace DedekindZetaZeroFree.Detector

noncomputable def frequencyNorm (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (u : S.integer F) : ℕ :=
  Nat.card ((S.integer F) ⧸ Ideal.span ({u} : Set (S.integer F)))

def frequencyDyad (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (U : FrequencyRepresentatives F S)
    (X : ℝ) : Set U.carrier :=
  {u | let q : ℝ := (frequencyNorm F S
        ⟨(u.val : F), (U.power_free u.val u.property).1⟩ : ℝ)
    X ≤ q ∧ q < 2 * X}

theorem frequency_dyad_row_count
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)] :
    ∃ C : ℝ, 0 < C ∧ ∀ U : FrequencyRepresentatives F S,
      ∀ X : ℝ, 2 ≤ X →
        (frequencyDyad F S U X).Finite ∧
        ((frequencyDyad F S U X).ncard : ℝ) ≤ C * X := by
  classical
  obtain ⟨Sf, rfl⟩ := hS.exists_finset_coe
  obtain ⟨C, hC, hcount⟩ := ProbeExteriorIdealCount.representative_count_linear F Sf
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro U X hX
  have hnorm (u : U.carrier) :
      ProbeExteriorIdealCount.elementNorm F Sf u.val =
        (frequencyNorm F (Sf : Set (HeightOneSpectrum (𝓞 F)))
          ⟨(u.val : F), (U.power_free u.val u.property).1⟩ : ℝ) := by
    let a : (Sf : Set (HeightOneSpectrum (𝓞 F))).integer F :=
      ⟨(u.val : F), (U.power_free u.val u.property).1⟩
    have ha : a ≠ 0 := by
      intro h
      have hz := congrArg (fun z : (Sf : Set (HeightOneSpectrum (𝓞 F))).integer F =>
        (z : F)) h
      exact u.val.ne_zero hz
    exact (sProductModulus_eq_principalIdeal_index F Sf a ha).2
  obtain ⟨hfin, hcard⟩ := hcount U (2 * X) (by linarith)
  have hsub : frequencyDyad F (Sf : Set (HeightOneSpectrum (𝓞 F))) U X ⊆
      {u : U.carrier | ProbeExteriorIdealCount.elementNorm F Sf u.val ≤ 2 * X} := by
    intro u hu
    change ProbeExteriorIdealCount.elementNorm F Sf u.val ≤ 2 * X
    rw [hnorm]
    exact le_of_lt hu.2
  refine ⟨hfin.subset hsub, ?_⟩
  have hn := Set.ncard_le_ncard hsub hfin
  have hn' : ((frequencyDyad F (Sf : Set (HeightOneSpectrum (𝓞 F))) U X).ncard : ℝ) ≤
      (Nat.card {u : U.carrier //
        ProbeExteriorIdealCount.elementNorm F Sf u.val ≤ 2 * X} : ℝ) := by
    exact_mod_cast hn
  calc
    _ ≤ _ := hn'
    _ ≤ C * (2 * X) := hcard
    _ ≤ (2 * C + 1) * X := by nlinarith

end DedekindZetaZeroFree.Detector
