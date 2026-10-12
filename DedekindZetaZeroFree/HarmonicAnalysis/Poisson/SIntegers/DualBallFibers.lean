module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegerTensorCosets
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CompletionDifferentExponent

@[expose] public section

noncomputable section

open scoped NumberField Classical nonZeroDivisors BigOperators WithZero
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PoissonS

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

def finiteBallTraceCharacter : AddChar (PoissonFinite.Space F S) Circle :=
  (sLocalTraceCharacter F S).compAddMonoidHom
    { toFun := fun x => (0, x)
      map_zero' := rfl
      map_add' := fun _ _ => by simp }

theorem finiteBallTraceCharacter_apply (x : PoissonFinite.Space F S) :
    finiteBallTraceCharacter F S x =
      ∏ v : S, localFiniteCharacter F v.val (x v) := by
  have h1 : finiteBallTraceCharacter F S x = sLocalTraceCharacter F S (0, x) := rfl
  rw [h1, sLocalTraceCharacter_apply]
  have hz : (∏ v : InfinitePlace F, archTraceCharacter v
      ((0 : InfiniteAdeleRing F) v)) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    change archTraceCharacter v (0 : v.Completion) = 1
    simp
  show (∏ v : InfinitePlace F, archTraceCharacter v ((0 : InfiniteAdeleRing F) v)) *
      (∏ v : S, localFiniteCharacter F v.val (x v)) =
        ∏ v : S, localFiniteCharacter F v.val (x v)
  rw [hz, one_mul]

def finiteBallAnnihilator (k : (v : S) → ℤ) :
    Set (PoissonFinite.Space F S) :=
  {y | ∀ u : PoissonFinite.Space F S, u ∈ finiteBall F S k →
    finiteBallTraceCharacter F S (u * y) = 1}

def dualBallFractionalIdeal (k : (v : S) → ℤ) :
    FractionalIdeal (𝓞 F)⁰ F :=
  (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) *
    (ballFractionalIdeal F S k)⁻¹

private theorem finiteBallAnnihilator_coordinate_iff (k : (v : S) → ℤ)
    (y : PoissonFinite.Space F S) :
    y ∈ finiteBallAnnihilator F S k ↔
      ∀ v : S, ∀ a : v.val.adicCompletion F,
        ‖a‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v) →
          localFiniteCharacter F v.val (a * y v) = 1 := by
  constructor
  · intro hy v a ha
    let u : PoissonFinite.Space F S := Pi.single v a
    have hu : u ∈ finiteBall F S k := by
      intro w
      by_cases hw : w = v
      · subst w
        simpa [u] using ha
      · have hz : u w = 0 := by simp [u, Pi.single_eq_of_ne hw]
        rw [hz, norm_zero]
        exact (zpow_pos (lt_trans zero_lt_one (by exact_mod_cast
          (HeightOneSpectrum.one_lt_absNorm w.val))) _).le
    have he := hy u hu
    rw [finiteBallTraceCharacter_apply] at he
    have hp : (∏ w : S, localFiniteCharacter F w.val ((u * y) w)) =
        localFiniteCharacter F v.val (a * y v) := by
      rw [Finset.prod_eq_single v]
      · simp [u]
      · intro w _ hw
        simp [u, Pi.single_eq_of_ne hw]
      · simp
    exact hp ▸ he
  · intro hy u hu
    rw [finiteBallTraceCharacter_apply]
    exact Finset.prod_eq_one (fun v _ => hy v (u v) (hu v))

theorem finiteBallAnnihilator_eq (k : (v : S) → ℤ) :
    finiteBallAnnihilator F S k =
      finiteBall F S (fun v => -differentExponent F v.val - k v) := by
  ext y
  rw [finiteBallAnnihilator_coordinate_iff]
  change _ ↔ ∀ v : S, _
  apply forall_congr'
  intro v
  have hb (n : ℤ) :
      (finiteCompletionBall F v.val n : Set (v.val.adicCompletion F)) =
      {x | ‖x‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-n)} :=
    PoissonSLocalBalls.ball_eq_normBall F v.val n
  have ha := (SetLike.ext_iff.mp
    (localFiniteAnnihilator_finiteCompletionBall F v.val (k v))) (y v)
  rw [mem_localFiniteAnnihilator] at ha
  simp_rw [← SetLike.mem_coe, hb] at ha
  rw [← FiniteOscillatoryStabilization.globalDifferentExponent_eq_localDifferentExponent]
    at ha
  simpa only [Set.mem_setOf_eq, sub_eq_add_neg, add_comm] using ha

theorem dualBallFractionalIdeal_subset_sIntegerRing
    (hS : ContainsDifferent F S) (k : (v : S) → ℤ) :
    (dualBallFractionalIdeal F S k : Set F) ⊆ sIntegerRing F S := by
  intro x hx
  have hx' : x ∈ (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) *
      (ballFractionalIdeal F S k)⁻¹ := hx
  rw [ScaleShift.dual_ballFractionalIdeal F S hS k] at hx'
  exact ScaleShift.ballFractionalIdeal_le_sIntegers F S
    (fun v : S => -k v - differentExponent F v.val) hx'

end DedekindZetaZeroFree.PoissonS

end
