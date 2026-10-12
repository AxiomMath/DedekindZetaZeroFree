module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Geometry.Orbifolds.EllipticRegularity.EquivariantLineCharts

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContRightJets

open KPContLocalNorm KPContLocalOrbifold

def scalarLift {n m : ℕ} (π : Space m → Space n) (frame : Space m → ℂ)
    (u : Space n → ℂ) : Space m → ℂ :=
  fun g => frame g * u (π g)

def rightWord {m b : ℕ} (fields : Fin b → Space m → Space m) :
    List (Fin b) → (Space m → ℂ) → Space m → ℂ
  | [], f => f
  | i :: w, f => fun g => fderiv ℝ (rightWord fields w f) g (fields i g)

def rightCombination {m b : ℕ} (fields : Fin b → Space m → Space m)
    (terms : List (ℂ × List (Fin b))) (f : Space m → ℂ) : Space m → ℂ :=
  fun g => (terms.map (fun t => t.1 * rightWord fields t.2 f g)).sum

def combinationOrder {b : ℕ} (terms : List (ℂ × List (Fin b))) : ℕ :=
  (terms.map (fun t => t.2.length)).foldr max 0

 lemma rightWord_smooth {m b : ℕ} (T : LocalBall m)
    (fields : Fin b → Space m → Space m)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T.carrier)
    (w : List (Fin b)) (f : Space m → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f T.carrier) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rightWord fields w f) T.carrier := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (ih.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply (hfields i)

section LocalChart

variable {n m b : ℕ} (T : LocalBall m) (L : LineChart n)
    (π : Space m → Space n) (frame : Space m → ℂ)
    (fields : Fin b → Space m → Space m)
    (hπ : ContDiffOn ℝ (⊤ : ℕ∞) π T.carrier)
    (hframe : ContDiffOn ℝ (⊤ : ℕ∞) frame T.carrier)
    (hfields : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fields i) T.carrier)
    (himage : π '' T.carrier ⊆ L.outer.carrier)

include hπ hframe hfields himage

end LocalChart
end DedekindZetaZeroFree.KPContRightJets

end
