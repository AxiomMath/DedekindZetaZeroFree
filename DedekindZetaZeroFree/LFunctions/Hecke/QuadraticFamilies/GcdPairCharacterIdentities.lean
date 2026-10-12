module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.ClassTwists
public import DedekindZetaZeroFree.Arithmetic.Ideals.SquarefreeGcdDecomposition
public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.ProductConductorComparison

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

private theorem coprime_mul_iff (I J K : Ideal (𝓞 F)) :
    I ⊔ J * K = ⊤ ↔ I ⊔ J = ⊤ ∧ I ⊔ K = ⊤ := by
  simp only [← Ideal.isCoprime_iff_sup_eq, IsCoprime.mul_right_iff]

private theorem coprime_of_dvd {I J K : Ideal (𝓞 F)}
    (h : I ⊔ J = ⊤) (hd : K ∣ J) : I ⊔ K = ⊤ := by
  apply top_unique
  rw [← h]
  exact sup_le_sup_left (Ideal.dvd_iff_le.mp hd) I

theorem rawGcdPairTransport
    (hc : c ≠ ⊥) (Q : QuadraticHeckeFamily F c)
    {a b u v : Ideal (𝓞 F)}
    (ha : Squarefree a) (hb : Squarefree b)
    (hac : a ⊔ c = ⊤) (hbc : b ⊔ c = ⊤)
    (hclass : Q.cls a = Q.cls b)
    (hau : a = (a ⊔ b) * u) (hbv : b = (a ⊔ b) * v) :
    let R := c * a * b * Q.cond a * Q.cond b * Q.cond u * Q.cond v
    R ≠ ⊥ ∧
      (∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ R = ⊤ →
        (Q.χ a) n * (Q.χ b) n = (Q.χ u) n * (Q.χ v) n) ∧
      (∃ ψ : RayClassCharacter F (u * v), ψ.IsPrimitive ∧
        ∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ R = ⊤ →
          ψ n = (Q.χ a) n * (Q.χ b) n) ∧
      u * v ∣ Q.cond a * Q.cond b ∧
      Q.cond a ∣ u * v * Q.cond b := by
  letI : Group Q.G := Q.instGroup
  obtain ⟨hd, hu, hv, huv, hdu, hdv⟩ :=
    SquarefreeGcd.strip_squarefree_and_coprime ha hb hau hbv
  obtain ⟨hdc, huc, hvc⟩ :=
    SquarefreeGcd.strip_coprime_aux ha hb hau hbv hac hbc
  have huvclass : Q.cls u = Q.cls v := by
    have hA := congrArg Q.cls hau
    have hB := congrArg Q.cls hbv
    rw [Q.cls_mul _ _ hdc huc] at hA
    rw [Q.cls_mul _ _ hdc hvc] at hB
    rw [hA, hB] at hclass
    exact mul_left_cancel hclass
  have ha0 := SquarefreeGcd.ne_bot_of_squarefree ha
  have hb0 := SquarefreeGcd.ne_bot_of_squarefree hb
  have hu0 := SquarefreeGcd.ne_bot_of_squarefree hu
  have hv0 := SquarefreeGcd.ne_bot_of_squarefree hv
  have hca := (Q.primitive a ha hac).1
  have hcb := (Q.primitive b hb hbc).1
  have hcu := (Q.primitive u hu huc).1
  have hcv := (Q.primitive v hv hvc).1
  let R := c * a * b * Q.cond a * Q.cond b * Q.cond u * Q.cond v
  have hR0 : R ≠ ⊥ := by
    dsimp [R]
    simpa only [Ideal.mul_eq_bot, not_or] using
      ⟨⟨⟨⟨⟨⟨hc, ha0⟩, hb0⟩, hca⟩, hcb⟩, hcu⟩, hcv⟩
  have parts (n : Ideal (𝓞 F)) (hn : n ⊔ R = ⊤) :
      n ⊔ c = ⊤ ∧ n ⊔ a = ⊤ ∧ n ⊔ b = ⊤ ∧
      n ⊔ Q.cond a = ⊤ ∧ n ⊔ Q.cond b = ⊤ ∧
      n ⊔ Q.cond u = ⊤ ∧ n ⊔ Q.cond v = ⊤ := by
    dsimp [R] at hn
    simp only [coprime_mul_iff] at hn
    tauto
  have hu_dvd : u ∣ a := by rw [hau]; exact dvd_mul_left u (a ⊔ b)
  have hv_dvd : v ∣ b := by rw [hbv]; exact dvd_mul_left v (a ⊔ b)
  have prime_eq (p : Ideal (𝓞 F)) (hp : Prime p) (hpR : p ⊔ R = ⊤) :
      (Q.χ a) p * (Q.χ b) p = (Q.χ u) p * (Q.χ v) p := by
    obtain ⟨hpc, hpa, hpb, hpca, hpcb, hpcu, hpcv⟩ := parts p hpR
    have hpu := coprime_of_dvd hpa hu_dvd
    have hpv := coprime_of_dvd hpb hv_dvd
    have rap := Q.reciprocity a p ha hac hp.squarefree hpc (by simpa [sup_comm] using hpa)
    have rbp := Q.reciprocity b p hb hbc hp.squarefree hpc (by simpa [sup_comm] using hpb)
    have rup := Q.reciprocity u p hu huc hp.squarefree hpc (by simpa [sup_comm] using hpu)
    have rvp := Q.reciprocity v p hv hvc hp.squarefree hpc (by simpa [sup_comm] using hpv)
    have hap0 : (Q.χ a) p ≠ 0 := by
      exact fun hz => ((Q.χ a).eq_zero_iff' p).mp hz |>.elim hp.ne_zero
        (fun h => h hpca)
    have hpd0 : (Q.χ p) (a ⊔ b) ≠ 0 := by
      intro hz
      apply hap0
      rw [rap, hau, (Q.χ p).map_mul', hz, zero_mul, zero_mul]
    have hpdsq : ((Q.χ p) (a ⊔ b)) ^ 2 = 1 := by
      have hcube := Q.quadratic p (a ⊔ b) hp.squarefree hpc
      apply mul_left_cancel₀ hpd0
      calc
        (Q.χ p) (a ⊔ b) * ((Q.χ p) (a ⊔ b)) ^ 2 =
            ((Q.χ p) (a ⊔ b)) ^ 3 := by ring
        _ = (Q.χ p) (a ⊔ b) := hcube
        _ = (Q.χ p) (a ⊔ b) * 1 := by ring
    calc
      (Q.χ a) p * (Q.χ b) p =
          ((Q.χ p) (a ⊔ b)) ^ 2 * ((Q.χ p) u * (Q.χ p) v) *
            (Q.C (Q.cls a) (Q.cls p)) ^ 2 := by
        have hA : (Q.χ p) a = (Q.χ p) (a ⊔ b) * (Q.χ p) u := by
          calc (Q.χ p) a = (Q.χ p) ((a ⊔ b) * u) := congrArg (Q.χ p) hau
               _ = _ := (Q.χ p).map_mul' _ _
        have hB : (Q.χ p) b = (Q.χ p) (a ⊔ b) * (Q.χ p) v := by
          calc (Q.χ p) b = (Q.χ p) ((a ⊔ b) * v) := congrArg (Q.χ p) hbv
               _ = _ := (Q.χ p).map_mul' _ _
        rw [rap, rbp, ← hclass, hA, hB]
        ring
      _ = (Q.χ p) u * (Q.χ p) v := by rw [hpdsq, Q.C_sq]; ring
      _ = (Q.χ u) p * (Q.χ v) p := by
        rw [rup, rvp, ← huvclass]
        calc
          (Q.χ p) u * (Q.χ p) v =
              ((Q.χ p) u * (Q.χ p) v) * (Q.C (Q.cls u) (Q.cls p)) ^ 2 := by
                rw [Q.C_sq]; ring
          _ = _ := by ring
  have pair_eq : ∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ R = ⊤ →
      (Q.χ a) n * (Q.χ b) n = (Q.χ u) n * (Q.χ v) n := by
    intro n
    induction n using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro hn; exact (hn rfl).elim
    | h₂ n hn =>
        have hn' : n = ⊤ := Ideal.isUnit_iff.mp hn
        subst n
        simp only [(Q.χ a).map_top', (Q.χ b).map_top', (Q.χ u).map_top', (Q.χ v).map_top']
        intro _ _; trivial
    | h₃ n p hn hp ih =>
        intro _ hnp
        obtain ⟨hpR, hnR⟩ := (Ideal.isCoprime_iff_sup_eq.mp
          ((IsCoprime.mul_left_iff.mp (Ideal.isCoprime_iff_sup_eq.mpr hnp)).1)),
          (Ideal.isCoprime_iff_sup_eq.mp
          ((IsCoprime.mul_left_iff.mp (Ideal.isCoprime_iff_sup_eq.mpr hnp)).2))
        rw [(Q.χ a).map_mul', (Q.χ b).map_mul', (Q.χ u).map_mul', (Q.χ v).map_mul']
        calc
          ((Q.χ a) p * (Q.χ a) n) * ((Q.χ b) p * (Q.χ b) n) =
              ((Q.χ a) p * (Q.χ b) p) * ((Q.χ a) n * (Q.χ b) n) := by ring
          _ = ((Q.χ u) p * (Q.χ v) p) * ((Q.χ u) n * (Q.χ v) n) := by
            rw [prime_eq p hp hpR, ih hn hnR]
          _ = _ := by ring
  obtain ⟨ψ, hψ, hψagree⟩ := Q.product_primitive u v hu huc hv hvc huv huvclass
  have ψeq : ∀ n : Ideal (𝓞 F), n ≠ ⊥ → n ⊔ R = ⊤ →
      ψ n = (Q.χ a) n * (Q.χ b) n := by
    intro n hn hnR
    obtain ⟨_, _, _, _, _, hnu, hnv⟩ := parts n hnR
    rw [hψagree n (by rw [coprime_mul_iff]; exact ⟨hnu, hnv⟩),
      quadraticFamily_conj Q hv hvc]
    exact (pair_eq n hn hnR).symm
  have huv0 : u * v ≠ ⊥ := fun h => (Ideal.mul_eq_bot.mp h).elim hu0 hv0
  have div₁ : u * v ∣ Q.cond a * Q.cond b := by
    apply RayComparison.primitive_product_conductor_dvd huv0 hca hcb hR0 ψ (Q.χ a) (Q.χ b) hψ
    intro n hn hnmod
    apply ψeq n hn
    exact coprime_of_dvd hnmod (dvd_mul_left R _)
  have div₂ : Q.cond a ∣ u * v * Q.cond b := by
    apply RayComparison.primitive_product_conductor_dvd hca huv0 hcb hR0
      (Q.χ a) ψ (Q.χ b) (Q.primitive a ha hac).2
    intro n hn hnmod
    have hnR : n ⊔ R = ⊤ := coprime_of_dvd hnmod (dvd_mul_left R _)
    have hncb := (parts n hnR).2.2.2.2.1
    rw [ψeq n hn hnR]
    have hs := quadraticFamily_value_sq_eq_one Q hb hbc n hn hncb
    calc
      (Q.χ a) n = (Q.χ a) n * ((Q.χ b) n) ^ 2 := by rw [hs]; ring
      _ = _ := by ring
  exact ⟨hR0, pair_eq, ⟨ψ, hψ, ψeq⟩, div₁, div₂⟩

end DedekindZetaZeroFree.LargeSieve
