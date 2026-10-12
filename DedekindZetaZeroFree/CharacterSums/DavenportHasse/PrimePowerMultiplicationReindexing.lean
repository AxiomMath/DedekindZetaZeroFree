module

public import DedekindZetaZeroFree.CharacterSums.DavenportHasse.WeightedMonicPolynomials

@[expose] public section

open Polynomial

namespace DavenportHasse.PolyPart

open scoped Classical

variable {k : Type*} [Field k] [Fintype k]

theorem mul_reindex (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    {P : k[X]} (hP : P.Monic) (j n : ℕ) (hjn : j * P.natDegree ≤ n) :
    wt χ ψ P ^ j * a χ ψ (n - j * P.natDegree) =
      ∑ f ∈ Mon k n, if P ^ j ∣ f then wt χ ψ f else 0 := by
  have ha : a χ ψ (n - j * P.natDegree) =
      ∑ g ∈ Mon k (n - j * P.natDegree), wt χ ψ g := by
    simp only [a, sum_Mon]

  have hset : (Mon k (n - j * P.natDegree)).image (fun g => P ^ j * g) =
      (Mon k n).filter (fun f => P ^ j ∣ f) := by
    ext f
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgm : g.Monic := (mem_Mon.1 hg).1
      have hgd : g.natDegree = n - j * P.natDegree := (mem_Mon.1 hg).2
      refine ⟨mem_Mon.2 ⟨(hP.pow j).mul hgm, ?_⟩, dvd_mul_right _ _⟩
      rw [(hP.pow j).natDegree_mul hgm, hP.natDegree_pow, hgd, Nat.add_sub_cancel' hjn]
    · rintro ⟨hf, hdvd⟩
      obtain ⟨g, rfl⟩ := hdvd
      have hfm : (P ^ j * g).Monic := (mem_Mon.1 hf).1
      have hgm : g.Monic := (hP.pow j).of_mul_monic_left hfm
      have hgd : g.natDegree = n - j * P.natDegree := by
        have h := (hP.pow j).natDegree_mul hgm
        rw [hP.natDegree_pow, (mem_Mon.1 hf).2] at h
        omega
      exact ⟨g, mem_Mon.2 ⟨hgm, hgd⟩, rfl⟩
  rw [ha, Finset.mul_sum]
  trans ∑ g ∈ Mon k (n - j * P.natDegree), wt χ ψ (P ^ j * g)
  · exact Finset.sum_congr rfl fun g hg => by
      rw [← wt_pow χ ψ hP j, ← wt_mul χ ψ (hP.pow j) (mem_Mon.1 hg).1]
  · rw [← Finset.sum_filter, ← hset,
      Finset.sum_image (fun g1 _ g2 _ h => mul_left_cancel₀ (hP.pow j).ne_zero h)]

end DavenportHasse.PolyPart
