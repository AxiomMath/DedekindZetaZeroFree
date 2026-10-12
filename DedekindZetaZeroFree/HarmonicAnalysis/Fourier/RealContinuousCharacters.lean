module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex

@[expose] public section

namespace DedekindZetaZeroFree

theorem kp_real_continuous_character
    (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    ∃! c : ℝ, ∀ x : ℝ, χ x = Circle.exp (2 * Real.pi * c * x) := by
  obtain ⟨g, ⟨hg0, hgexp⟩, hguniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨χ, hχ⟩ 0 0 (by simp)
  have hgexp' (x : ℝ) : Circle.exp (g x) = χ x := congr_fun hgexp x

  have hgadd (x y : ℝ) : g (x + y) = g x + g y := by
    let F : C(ℝ, ℝ) := ⟨fun t => g (x + t) - g x, by fun_prop⟩
    have hF : F = g := hguniq F ⟨by simp [F], ?_⟩
    · have := DFunLike.congr_fun hF y
      dsimp [F] at this
      linarith
    · funext t
      dsimp [F]
      rw [Circle.exp_sub, hgexp', hgexp', χ.map_add_eq_mul]
      simp
  let G : ℝ →+ ℝ := { toFun := g, map_zero' := hg0, map_add' := hgadd }
  have hglin (x : ℝ) : g x = x * g 1 := by
    simpa [G] using map_real_smul G g.continuous x 1
  refine ⟨g 1 / (2 * Real.pi), ?_, ?_⟩
  · intro x
    rw [← hgexp', hglin]
    congr 1
    field_simp
  · intro c hc
    let F : C(ℝ, ℝ) := ⟨fun x => 2 * Real.pi * c * x, by fun_prop⟩
    have hF : F = g := hguniq F ⟨by simp [F], funext (fun x => (hc x).symm)⟩
    have h1 := DFunLike.congr_fun hF 1
    dsimp [F] at h1
    field_simp
    nlinarith [Real.pi_pos]

end DedekindZetaZeroFree
