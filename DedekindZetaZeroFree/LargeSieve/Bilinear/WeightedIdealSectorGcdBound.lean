module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.SectorGcdEnergyDecomposition
public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorNormBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient
open scoped NumberField Classical

theorem sector_gcd_bound
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (M N K : ℝ) (lam : Ideal (𝓞 F) → ℂ)
    (pool : Finset (Ideal (𝓞 F)))
    (hpool : ∀ b1 ∈ paperShell F c N, ∀ b2 ∈ paperShell F c N, b1 ⊔ b2 ∈ pool) :
    letI : Finite Q.G := Q.instFinite
    letI : Fintype Q.G := Fintype.ofFinite Q.G
    Q2 F c Q W M N K lam ≤ (Fintype.card Q.G : ℝ) *
      ∑ g, ∑ d ∈ pool, ‖T3 F c Q W M N K d g lam‖ := by
  letI : Finite Q.G := Q.instFinite
  letI : Fintype Q.G := Fintype.ofFinite Q.G
  let R := ↥(kernelRows F c M K)
  let L := ↥(paperShell F c N)
  let w : R → NNReal := fun a => NNReal.mk (W ((Ideal.absNorm (a : Ideal (𝓞 F)) : ℝ) / M)) (hW.nonneg _)
  let A : R → L → ℂ := fun a b => (Q.χ (b : Ideal (𝓞 F))) (a : Ideal (𝓞 F))
  let sector : L → Q.G := fun b => Q.cls b
  let label : L → L → Ideal (𝓞 F) := fun b1 b2 => (b1 : Ideal (𝓞 F)) ⊔ b2
  let x : L → ℂ := fun b => lam b
  have h := DedekindZetaZeroFree.LargeSieve.Vendor.GcdReduction.weighted_energy_le_sector_gcd_blocks
    w A sector label x pool (fun b1 b2 => hpool b1 b1.property b2 b2.property)
  have hb : ∀ g d, DedekindZetaZeroFree.LargeSieve.Vendor.GcdReduction.gcdBlock w A sector label x g d =
      T3 F c Q W M N K d g lam := by
    intro g d
    unfold DedekindZetaZeroFree.LargeSieve.Vendor.GcdReduction.gcdBlock T3
    rw [← Finset.sum_coe_sort (paperShell F c N)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b1 hb1
    rw [← Finset.sum_coe_sort (paperShell F c N)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b2 hb2
    dsimp only [w, A, sector, label, x]
    by_cases hc : (b1 : Ideal (𝓞 F)) ⊔ (b2 : Ideal (𝓞 F)) = d ∧
        Q.cls b1 = g ∧ Q.cls b2 = g
    · have hc' : Q.cls b1 = g ∧ Q.cls b2 = g ∧
          (b1 : Ideal (𝓞 F)) ⊔ (b2 : Ideal (𝓞 F)) = d := ⟨hc.2.1, hc.2.2, hc.1⟩
      simp only [hc', hc, if_true, true_and]
      simp only [NNReal.coe_mk]
      rw [← Finset.sum_coe_sort (kernelRows F c M K)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      simp only [map_mul, starRingEnd_apply, star_mul]
      ring
    · have hc' : ¬(Q.cls b1 = g ∧ Q.cls b2 = g ∧
          (b1 : Ideal (𝓞 F)) ⊔ (b2 : Ideal (𝓞 F)) = d) :=
        fun hh => hc ⟨hh.2.2, hh.1, hh.2.1⟩
      simp only [hc', hc, if_false, Finset.sum_const_zero]
  simp only [hb] at h
  have hform : (∑ r, (w r : ℝ) * ‖∑ l, A r l * x l‖ ^ 2) = Q2 F c Q W M N K lam := by
    unfold Q2 rowSum
    rw [← Finset.sum_coe_sort (kernelRows F c M K)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_coe_sort (paperShell F c N)]
    simp only [w, A, x, NNReal.coe_mk, mul_comm]
    rfl
  rw [hform] at h
  exact h

end DedekindZetaZeroFree.LargeSieve.Sieve.CoreCoefficient

end
