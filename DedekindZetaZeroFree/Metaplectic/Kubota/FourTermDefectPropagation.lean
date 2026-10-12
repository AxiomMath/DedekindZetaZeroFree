module

public import DedekindZetaZeroFree.Metaplectic.Kubota.WeylBoundaryDefect
public import DedekindZetaZeroFree.Metaplectic.Kubota.WeylOpenCellDefect

@[expose] public section

namespace DedekindZetaZeroFree
namespace KubotaThirdArgumentPropagation

def defect
    (G : Type*) [Monoid G] (M : Type*) [CommGroup M]
    (f : G → G → M) (g h k : G) : M :=
  f g h * f (g * h) k / (f h k * f g (h * k))

def Good
    (G : Type*) [Monoid G] (M : Type*) [CommGroup M]
    (f : G → G → M) (k : G) : Prop :=
  ∀ g h : G, defect G M f g h k = 1

theorem four_term
    (G : Type*) [Monoid G] (M : Type*) [CommGroup M]
    (f : G → G → M) (g h k l : G) :
    defect G M f g h k * defect G M f g (h * k) l *
        defect G M f h k l =
      defect G M f (g * h) k l * defect G M f g h (k * l) := by
  simp only [defect, mul_assoc, ← mul_div_mul_comm]
  rw [div_eq_div_iff_mul_eq_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem good_mul
    (G : Type*) [Monoid G] (M : Type*) [CommGroup M]
    (f : G → G → M) (k l : G)
    (hk : Good G M f k) (hl : Good G M f l) :
    Good G M f (k * l) := by
  intro g h
  have H := four_term G M f g h k l
  simpa only [hk g h, hl g (h * k), hl h k, hl (g * h) k,
    one_mul] using H.symm

theorem defect_eq_one_iff
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M) (g h k : KubotaRankTwo.GL2 K) :
    KubotaElementaryLastArgument.defect K M B g h k = 1 ↔
      KubotaElementaryLastArgument.tau K M B g h *
          KubotaElementaryLastArgument.tau K M B (g * h) k =
        KubotaElementaryLastArgument.tau K M B h k *
          KubotaElementaryLastArgument.tau K M B g (h * k) := by
  exact div_eq_one

theorem tau_cocycle
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (hSt : ∀ (a : Kˣ) (ha : (a : K) ≠ 1),
      B a (Units.mk0 (1 - (a : K)) (sub_ne_zero.mpr (Ne.symm ha))) = 1)
    (g h k : KubotaRankTwo.GL2 K) :
    KubotaElementaryLastArgument.tau K M B g h *
        KubotaElementaryLastArgument.tau K M B (g * h) k =
      KubotaElementaryLastArgument.tau K M B h k *
        KubotaElementaryLastArgument.tau K M B g (h * k) := by
  classical
  let f := KubotaElementaryLastArgument.tau K M B
  have hn (t : K) : Good (KubotaRankTwo.GL2 K) M f (KubotaRankTwo.n K t) :=
    fun a b => KubotaElementaryLastArgument.defect_n K M B hL hR hAlt hCub a b t
  have hd (u v : Kˣ) : Good (KubotaRankTwo.GL2 K) M f (KubotaRankTwo.d K u v) :=
    fun a b => KubotaElementaryLastArgument.defect_d K M B hL hR hAlt hCub a b u v
  have hw : Good (KubotaRankTwo.GL2 K) M f (KubotaRankTwo.w K) := by
    intro a b
    by_cases hBoundary :
        (a : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨
        (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨
        (b : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 ∨
        (a * b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨
        (a * b : Matrix (Fin 2) (Fin 2) K) 1 1 = 0
    · exact KubotaWeylBoundaryCells.defect_w_boundary K M B hL hR hAlt hCub a b hBoundary
    · push_neg at hBoundary
      exact KubotaWeylOpenCell.defect_w_open K M B hL hR hAlt hCub hSt a b
        hBoundary.1 hBoundary.2.1 hBoundary.2.2.1 hBoundary.2.2.2.1 hBoundary.2.2.2.2
  have hk : Good (KubotaRankTwo.GL2 K) M f k := by
    by_cases hc : (k : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · rw [KubotaRankTwo.bruhat_closed K k hc]
      exact good_mul _ M f _ _ (hd _ _) (hn _)
    · rw [KubotaRankTwo.bruhat_open K k hc]
      exact good_mul _ M f _ _
        (good_mul _ M f _ _ (good_mul _ M f _ _ (hn _) (hd _ _)) hw) (hn _)
  exact (defect_eq_one_iff K M B g h k).mp (hk g h)

end KubotaThirdArgumentPropagation

end DedekindZetaZeroFree
