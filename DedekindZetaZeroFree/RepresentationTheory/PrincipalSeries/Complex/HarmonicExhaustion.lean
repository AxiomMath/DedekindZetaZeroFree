module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexCompactSphericalCharts
public import DedekindZetaZeroFree.HarmonicAnalysis.Sphere.SmoothPolynomialDensity

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxActualImageProof

open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open scoped BigOperators

open ComplexFractionalInverse

theorem polynomialCompactRestriction_eq_hopf (p : MvPolynomial (Fin 3) ℂ)
    (k : KPCplxCharacterHaar.ComplexSU2) :
    polynomialCompactRestriction p k = polynomialSphere p (hopf k) := by
  change MvPolynomial.eval (compactSphereCoordinate k) p =
    MvPolynomial.eval (fun i => ((compactSphereCoordinate k i).re : ℂ)) p
  have hcoord : compactSphereCoordinate k =
      (fun i => ((compactSphereCoordinate k i).re : ℂ)) := by
    funext i
    fin_cases i <;> simp [compactSphereCoordinate, ← Complex.ofReal_pow]
  rw [← hcoord]

theorem polynomial_profile_mem (s : ℝ) (U : Submodule ℂ (PrincipalSeries s))
    (hall : ∀ ℓ : ℕ, harmonicKType s ℓ ≤ U)
    (f : PrincipalSeries s) (p : MvPolynomial (Fin 3) ℂ)
    (hf : sphereProfile s f = polynomialSphere p) : f ∈ U := by
  classical
  obtain ⟨I, h, hh, heval⟩ := finite_fischer_spanning p
  have hlift : ∀ ℓ, ∃ a : PrincipalSeries s,
      sphereProfile s a = polynomialSphere (h ℓ) := by
    intro ℓ
    exact sphereProfile_surjective s _ (polynomialSphere_smooth _)
  choose a ha using hlift
  have hmem : ∀ ℓ ∈ I, a ℓ ∈ harmonicKType s ℓ := by
    intro ℓ hℓ
    change compactRestriction s (a ℓ) ∈
      (harmonicPolynomials ℓ).map polynomialCompactRestriction
    refine ⟨h ℓ, hh ℓ hℓ, ?_⟩
    funext k
    rw [polynomialCompactRestriction_eq_hopf, (sphereProfile_spec s (a ℓ)).2 k, ha]
  have heq : f = ∑ ℓ ∈ I, a ℓ := by
    apply (harmonicKType_compact_identification s s 0).1
    funext k
    rw [(sphereProfile_spec s f).2 k, hf, heval]
    simp only [map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro ℓ _
    exact ((sphereProfile_spec s (a ℓ)).2 k).trans (congrFun (ha ℓ) (hopf k)) |>.symm
  rw [heq]
  exact U.sum_mem (fun ℓ hℓ => hall ℓ (hmem ℓ hℓ))

theorem sphereProfile_sub (s : ℝ) (f g : PrincipalSeries s) :
    sphereProfile s (f - g) = fun x => sphereProfile s f x - sphereProfile s g x := by
  funext x
  obtain ⟨k, rfl⟩ := hopf_surjective x
  rw [← (sphereProfile_spec s (f - g)).2 k,
    ← (sphereProfile_spec s f).2 k, ← (sphereProfile_spec s g).2 k]
  rfl

theorem polynomial_lifts_tendsto (s : ℝ) (f : PrincipalSeries s)
    (p : ℕ → MvPolynomial (Fin 3) ℂ) (a : ℕ → PrincipalSeries s)
    (ha : ∀ N, sphereProfile s (a N) = polynomialSphere (p N))
    (hlim : ∀ n : ℕ, Filter.Tendsto
      (fun N => rotationSup n (fun x => sphereProfile s f x - polynomialSphere (p N) x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto a Filter.atTop (nhds f) := by
  have hp : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  apply (hp.tendsto_nhds_atTop a f).mpr
  intro n ε hε
  obtain ⟨C, D, hC, hD, hc, hd⟩ := chart_rotation_comparison s n
  have hscaled := (hlim n).const_mul (C : ℝ)
  simp only [mul_zero] at hscaled
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hscaled.eventually_lt_const hε)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hrev : chartSeminorm s n (a N - f) = chartSeminorm s n (f - a N) := by
    simpa only [neg_sub] using map_neg_eq_map (chartSeminorm s n) (f - a N)
  rw [hrev]
  have hb := hc (f - a N)
  rw [sphereProfile_sub, ha N] at hb
  exact hb.trans_lt (hN₀ N hN)

theorem closed_harmonic_exhaustion (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s))
    (hclosed : IsClosed (U : Set (PrincipalSeries s)))
    (hall : ∀ ℓ : ℕ, harmonicKType s ℓ ≤ U) : U = ⊤ := by
  classical
  apply top_unique
  intro f _
  obtain ⟨p, hp⟩ := finite_polynomial_smooth_density (sphereProfile s f)
    (sphereProfile_spec s f).1
  have hlift : ∀ N, ∃ a : PrincipalSeries s,
      sphereProfile s a = polynomialSphere (p N) := by
    intro N
    exact sphereProfile_surjective s _ (polynomialSphere_smooth _)
  choose a ha using hlift
  exact hclosed.mem_of_tendsto (polynomial_lifts_tendsto s f p a ha hp)
    (Filter.Eventually.of_forall (fun N => polynomial_profile_mem s U hall (a N) (p N) (ha N)))

end DedekindZetaZeroFree.KPCplxActualImageProof
