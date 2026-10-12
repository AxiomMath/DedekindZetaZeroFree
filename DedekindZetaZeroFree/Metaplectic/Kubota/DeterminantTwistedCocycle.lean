module

public import DedekindZetaZeroFree.Metaplectic.Kubota.FourTermDefectPropagation
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization

@[expose] public section

namespace DedekindZetaZeroFree
namespace KubotaCocycleAlgebra

open KubotaRankTwo KubotaElementaryLastArgument

noncomputable def sigmaTwo
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M) (g h : GL2 K) : M :=
  tau K M B g h * B (det K g) (det K h) ^ 2

theorem determinantTwist_cocycle
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (g h k : GL2 K) :
    B (det K g) (det K h) ^ 2 * B (det K (g * h)) (det K k) ^ 2 =
      B (det K h) (det K k) ^ 2 * B (det K g) (det K (h * k)) ^ 2 := by
  simp only [map_mul, hL, hR, mul_pow]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem sigmaTwo_cocycle
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (hSt : ∀ (a : Kˣ) (ha : (a : K) ≠ 1),
      B a (Units.mk0 (1 - (a : K)) (sub_ne_zero.mpr (Ne.symm ha))) = 1)
    (g h k : GL2 K) :
    sigmaTwo K M B g h * sigmaTwo K M B (g * h) k =
      sigmaTwo K M B h k * sigmaTwo K M B g (h * k) := by
  have ht := KubotaThirdArgumentPropagation.tau_cocycle K M B hL hR hAlt hCub hSt g h k
  have hd := determinantTwist_cocycle K M B hL hR g h k
  unfold sigmaTwo
  calc
    (tau K M B g h * B (det K g) (det K h) ^ 2) *
        (tau K M B (g * h) k * B (det K (g * h)) (det K k) ^ 2) =
        (tau K M B g h * tau K M B (g * h) k) *
          (B (det K g) (det K h) ^ 2 * B (det K (g * h)) (det K k) ^ 2) := by ac_rfl
    _ = (tau K M B h k * tau K M B g (h * k)) *
          (B (det K h) (det K k) ^ 2 * B (det K g) (det K (h * k)) ^ 2) := by rw [ht, hd]
    _ = (tau K M B h k * B (det K h) (det K k) ^ 2) *
          (tau K M B g (h * k) * B (det K g) (det K (h * k)) ^ 2) := by ac_rfl

theorem sigmaTwo_one_left
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (g : GL2 K) : sigmaTwo K M B 1 g = 1 := by
  simp only [sigmaTwo, tau, one_mul, X_one, map_one, mul_one]
  rw [show X K g / X K g = 1 by exact div_self' _,
    KubotaDefectSymbolAlgebra.one_right K M B hR,
    KubotaDefectSymbolAlgebra.one_left K M B hL]
  simp

theorem sigmaTwo_one_right
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (g : GL2 K) : sigmaTwo K M B g 1 = 1 := by
  simp only [sigmaTwo, tau_one_right K M B hL g, map_one,
    KubotaDefectSymbolAlgebra.one_right K M B hR, one_pow, mul_one]

theorem sigmaTwo_n_mul_mul_n
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M) (g h : GL2 K) (t t' : K) :
    sigmaTwo K M B (n K t * g) (h * n K t') = sigmaTwo K M B g h := by
  simp only [sigmaTwo, tau_n_mul_mul_n, map_mul, det_n, one_mul, mul_one]

end KubotaCocycleAlgebra

end DedekindZetaZeroFree
