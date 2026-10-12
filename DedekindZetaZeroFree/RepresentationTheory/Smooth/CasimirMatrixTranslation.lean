module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.ChamberCasimir

@[expose] public section

noncomputable section
open scoped Classical Matrix.Norms.Elementwise Topology
namespace DedekindZetaZeroFree.FourierContinuation.ResidualMatrixTranslation
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrixLeftDerivative → matrixLeftDerivative
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming rightOmega → rightOmega
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming leftOmega → leftOmega
open _root_.DedekindZetaZeroFree.KPMsSameContinuationGreen.CanonicalNativeChamberCasimir renaming matrix_omega_left_right → matrix_omega_left_right
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private theorem left_translate (X k : Matrix (Fin 2) (Fin 2) ℂ)
    (f : Matrix (Fin 2) (Fin 2) ℂ → ℂ) :
    matrixLeftDerivative X (fun a => f (a*k)) = fun a => matrixLeftDerivative X f (a*k) := by
  funext a
  simp only [matrixLeftDerivative,Matrix.mul_assoc]

theorem matrix_casimir_right_translate
    (f : Matrix (Fin 2) (Fin 2) ℂ → ℂ)
    (O : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hO : IsOpen O)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O)
    (g k : KPCplxCharacterHaar.ComplexGL2) (hg : g.val*k.val ∈ O) :
    rightOmega (fun a => f (a*k.val)) g.val = rightOmega f (g.val*k.val) := by
  let V := (fun a : Matrix (Fin 2) (Fin 2) ℂ => a*k.val) ⁻¹' O
  have hv : IsOpen V := hO.preimage (by fun_prop)
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun a : Matrix (Fin 2) (Fin 2) ℂ => a*k.val) := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    simp only [Matrix.mul_apply]
    fun_prop
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun a => f (a*k.val)) V :=
    hf.comp hm.contDiffOn (fun _ h => h)
  rw [matrix_omega_left_right _ hv hs g hg]
  have hr := matrix_omega_left_right f hO hf (g*k) hg
  change rightOmega f (g.val*k.val) = leftOmega f (g.val*k.val) at hr
  rw [hr]
  simp only [leftOmega,left_translate]

end DedekindZetaZeroFree.FourierContinuation.ResidualMatrixTranslation

end
