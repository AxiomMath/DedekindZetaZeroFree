module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.GcdPairCharacterIdentities
public import DedekindZetaZeroFree.LFunctions.Dedekind.PrincipalHeckeData

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)

private lemma principalProducts_top_ne_bot_ringOfIntegers : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by
  intro h
  have h1 : (1 : 𝓞 F) = 0 := by
    have hm : (1 : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) :=
      h ▸ (show (1 : 𝓞 F) ∈ (⊤ : Ideal (𝓞 F)) from Submodule.mem_top)
    simpa using hm
  exact one_ne_zero h1

private lemma mul_ne_bot_of_ne_bot {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I * J ≠ ⊥ := by
  intro h
  rcases Ideal.mul_eq_bot.mp h with h' | h'
  · exact hI h'
  · exact hJ h'

private lemma sup_eq_top_of_dvd {I A M : Ideal (𝓞 F)} (h : I ⊔ M = ⊤) (hdvd : A ∣ M) :
    I ⊔ A = ⊤ := by
  have hle : M ≤ A := Ideal.dvd_iff_le.mp hdvd
  exact le_antisymm le_top (h ▸ sup_le_sup_left hle I)

theorem quadraticFamily_eq_of_sameClass_principal_away
    (hc : c ≠ ⊥) {a b : Ideal (𝓞 F)}
    (ha : Squarefree a) (hac : a ⊔ c = ⊤)
    (hb : Squarefree b) (hbc : b ⊔ c = ⊤)
    (hclass : Q.cls a = Q.cls b)
    (hprincipal : ∃ q : Ideal (𝓞 F), q ≠ ⊥ ∧
      ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
        I ⊔ (Q.cond a * Q.cond b * q) = ⊤ →
        (Q.χ a) I * (Q.χ b) I = 1) :
    a = b := by

  obtain ⟨⟨u, v⟩, ⟨hau, hbv⟩, -⟩ := SquarefreeGcd.existsUnique_strip (F := F) ha hb
  have htrans := rawGcdPairTransport (F := F) (c := c) (a := a) (b := b) (u := u) (v := v)
    hc Q ha hb hac hbc hclass hau hbv
  obtain ⟨hRne, -, hψ, huvdvd, -⟩ := htrans
  obtain ⟨ψ, hψprim, hψval⟩ := hψ
  set R : Ideal (𝓞 F) := c * a * b * Q.cond a * Q.cond b * Q.cond u * Q.cond v with hRdef
  obtain ⟨q, hqne, hq⟩ := hprincipal
  have hcda : Q.cond a ≠ ⊥ := (Q.primitive a ha hac).1
  have hcdb : Q.cond b ≠ ⊥ := (Q.primitive b hb hbc).1
  have hm : u * v ≠ ⊥ := fun h =>
    mul_ne_bot_of_ne_bot hcda hcdb (le_bot_iff.mp (h ▸ Ideal.dvd_iff_le.mp huvdvd))
  have hqR : q * R ≠ ⊥ := mul_ne_bot_of_ne_bot hqne hRne

  have htop_le : (⊤ : Ideal (𝓞 F)) ≤ u * v :=
    rayCharacter_primitive_modulus_le (m := u * v) (f := ⊤) (q := q * R)
      hm principalProducts_top_ne_bot_ringOfIntegers hqR ψ hψprim (principalCharacter F) (by
        intro I hI hIsup
        have hIR : I ⊔ R = ⊤ :=
          sup_eq_top_of_dvd hIsup (dvd_mul_of_dvd_right (dvd_mul_left R q) (u * v * ⊤))
        have hdvdq : Q.cond a * Q.cond b * q ∣ u * v * ⊤ * (q * R) := by
          refine ⟨u * v * ⊤ * (c * a * b * Q.cond u * Q.cond v), ?_⟩
          rw [hRdef]
          ac_rfl
        have hIq : I ⊔ (Q.cond a * Q.cond b * q) = ⊤ := sup_eq_top_of_dvd hIsup hdvdq
        rw [hψval I hI hIR, hq I hI hIq]
        simp [principalCharacter_apply, hI])
  have hv : v = ⊤ := le_antisymm le_top (htop_le.trans Ideal.mul_le_right)
  have hu : u = ⊤ := by
    rw [hv, Ideal.mul_top] at htop_le
    exact le_antisymm le_top htop_le
  calc a = (a ⊔ b) * u := hau
    _ = (a ⊔ b) * ⊤ := by rw [hu]
    _ = a ⊔ b := Ideal.mul_top _
    _ = (a ⊔ b) * ⊤ := (Ideal.mul_top _).symm
    _ = (a ⊔ b) * v := by rw [hv]
    _ = b := hbv.symm

theorem quadraticFamily_principal_product_iff
    (hc : c ≠ ⊥) {a b : Ideal (𝓞 F)}
    (ha : Squarefree a) (hac : a ⊔ c = ⊤)
    (hb : Squarefree b) (hbc : b ⊔ c = ⊤)
    (hclass : Q.cls a = Q.cls b) :
    (RayOperations.mul (Q.χ a) (Q.χ b)).IsPrincipal ↔ a = b := by
  constructor
  · intro h
    refine quadraticFamily_eq_of_sameClass_principal_away (Q := Q) hc ha hac hb hbc hclass ?_
    refine ⟨⊤, principalProducts_top_ne_bot_ringOfIntegers, ?_⟩
    intro I hI hIsup
    have hI' : I ⊔ (Q.cond a * Q.cond b) = ⊤ := by simpa using hIsup
    have hval := h I hI hI'
    simpa using hval
  · intro hab
    rw [hab]
    intro I hI hIsup
    have hcond : I ⊔ Q.cond b = ⊤ :=
      sup_eq_top_of_dvd hIsup (dvd_mul_right (Q.cond b) (Q.cond b))
    have hsq := quadraticFamily_value_sq_eq_one (Q := Q) hb hbc I hI hcond
    simpa [pow_two] using hsq

end DedekindZetaZeroFree.LargeSieve
