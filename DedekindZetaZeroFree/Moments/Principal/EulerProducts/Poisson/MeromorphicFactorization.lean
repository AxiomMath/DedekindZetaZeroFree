module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerContinuation

open DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def initialRegion : Set Coordinates :=
  {p | 4 < p.1.re ∧ 4 < p.2.1.re ∧ 2 < p.2.2.re}

def OmegaStarRegular : Set Coordinates :=
  {p | p ∈ OmegaStar ∧ p.1 ≠ 1 ∧ p.2.1 ≠ 1 ∧ 6 * p.2.2 ≠ 1}

theorem initialRegion_subset_OmegaStar : initialRegion ⊆ OmegaStar := by
  intro p hp
  simp only [initialRegion, Set.mem_setOf_eq] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  simp only [OmegaStar, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem rowFactor_cross_multiplied_of_ne (u : D.Row) (p : Coordinates)
    (hL : D.Llam u p.1 ≠ 0) :
    PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2 * D.Llam u p.1 =
      D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 * Hu D u p.1 p.2.1 p.2.2 := by
  unfold PoissonKernel.rowFactor
  calc D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 / D.Llam u p.1 * Hu D u p.1 p.2.1 p.2.2
        * D.Llam u p.1
      = (D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 * Hu D u p.1 p.2.1 p.2.2) *
          (D.Llam u p.1 * (D.Llam u p.1)⁻¹) := by ring
    _ = D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 * Hu D u p.1 p.2.1 p.2.2 := by
      rw [mul_inv_cancel₀ hL, mul_one]

theorem rowFactor_cross_multiplied (u : D.Row) :
    ∀ p ∈ initialRegion,
      PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2 * D.Llam u p.1 =
        D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 * Hu D u p.1 p.2.1 p.2.2 := by
  intro p hp
  have hp1 : (1 : ℝ) < p.1.re := by
    simp only [initialRegion, Set.mem_setOf_eq] at hp
    linarith [hp.1]
  exact rowFactor_cross_multiplied_of_ne D u p
    (RightHeckeBounds.Llam_ne_zero_of_one_lt D u p.1 hp1)

theorem Hu_differentiableOn (u : D.Row) :
    DifferentiableOn ℂ (fun p : Coordinates => Hu D u p.1 p.2.1 p.2.2) OmegaStar :=
  (Hu_normal_convergence D u).2.2.1

theorem rowFactor_continuation (u : D.Row) :
    ∃ G : Coordinates → ℂ,
      (∀ p ∈ initialRegion, G p = PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2) ∧
      (∀ p ∈ OmegaStarRegular, D.Llam u p.1 ≠ 0 →
        G p = D.zetaSCont (6 * p.2.2) * D.Lpsi u p.2.1 * Hu D u p.1 p.2.1 p.2.2 /
          D.Llam u p.1) ∧
      DifferentiableOn ℂ G {p | p ∈ OmegaStarRegular ∧ D.Llam u p.1 ≠ 0} := by
  refine ⟨fun p => PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2, fun p _ => rfl, ?_, ?_⟩
  · intro p hp hL
    show PoissonKernel.rowFactor D u p.1 p.2.1 p.2.2 = _
    unfold PoissonKernel.rowFactor
    ring
  · intro p hp
    obtain ⟨⟨hOm, h1, h2, h3⟩, hL⟩ := hp
    have hOm' := hOm
    simp only [OmegaStar, Set.mem_setOf_eq] at hOm'
    obtain ⟨hx, hy, hv, -⟩ := hOm'
    have hz : DifferentiableAt ℂ D.zetaSCont (6 * p.2.2) :=
      (RightHeckeBounds.zetaSCont_analyticOnNhd D (6 * p.2.2)
        ⟨by
          show 0 < (6 * p.2.2).re
          have : (6 * p.2.2).re = 6 * p.2.2.re := by simp
          rw [this]; linarith, h3⟩).differentiableAt
    have hw : DifferentiableAt ℂ (D.Lpsi u) p.2.1 :=
      (D.Lpsi_analyticOnNhd u p.2.1 ⟨hy, h2⟩).differentiableAt
    have hl : DifferentiableAt ℂ (D.Llam u) p.1 :=
      (D.Llam_analyticOnNhd u p.1 ⟨hx, h1⟩).differentiableAt
    have hHu : DifferentiableAt ℂ (fun q : Coordinates => Hu D u q.1 q.2.1 q.2.2) p :=
      (Hu_differentiableOn D u).differentiableAt (OmegaStar_isOpen.mem_nhds hOm)
    have e1 : DifferentiableAt ℂ (fun q : Coordinates => D.zetaSCont (6 * q.2.2)) p :=
      DifferentiableAt.comp p (g := D.zetaSCont) (f := fun q : Coordinates => 6 * q.2.2) hz
        (by fun_prop)
    have e2 : DifferentiableAt ℂ (fun q : Coordinates => D.Lpsi u q.2.1) p :=
      DifferentiableAt.comp p (g := D.Lpsi u) (f := fun q : Coordinates => q.2.1) hw
        (by fun_prop)
    have e3 : DifferentiableAt ℂ (fun q : Coordinates => D.Llam u q.1) p :=
      DifferentiableAt.comp p (g := D.Llam u) (f := fun q : Coordinates => q.1) hl
        (by fun_prop)
    have hL' : (fun q : Coordinates => D.Llam u q.1) p ≠ 0 := hL
    have e3' : DifferentiableAt ℂ (fun q : Coordinates => (D.Llam u q.1)⁻¹) p :=
      DifferentiableAt.fun_inv e3 hL'
    have e5 : DifferentiableAt ℂ (fun q : Coordinates =>
        D.zetaSCont (6 * q.2.2) * D.Lpsi u q.2.1 * (D.Llam u q.1)⁻¹ *
          Hu D u q.1 q.2.1 q.2.2) p :=
      ((e1.mul e2).mul e3').mul hHu
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [PoissonKernel.rowFactor, div_eq_mul_inv]
    exact e5
end

end DedekindZetaZeroFree.Quantitative.EulerContinuation
