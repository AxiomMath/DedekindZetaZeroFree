module

public import DedekindZetaZeroFree.Theta.Whittaker.DiagonalCharacterTransport
public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Arithmetic.LocalFields.PlacesAndCompletions
public import DedekindZetaZeroFree.Arithmetic.LocalFields.SixthPowerCongruenceSubgroups

@[expose] public section

section

namespace DedekindZetaZeroFree.ThetaFiniteCutoff.PhaseSublevels

open NumberField IsDedekindDomain

theorem exists_additive_dual_level
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : ContinuousAddChar (v.adicCompletion F))
    (he : ∃ x, e.toAddChar x ≠ 1)
    (H : AddSubgroup (v.adicCompletion F))
    (hHcompact : IsCompact (H : Set (v.adicCompletion F)))
    (hHopen : IsOpen (H : Set (v.adicCompletion F))) :
    ∃ B : AddSubgroup (v.adicCompletion F),
      IsCompact (B : Set (v.adicCompletion F)) ∧
      IsOpen (B : Set (v.adicCompletion F)) ∧
      ∀ z : v.adicCompletion F,
        (∀ t ∈ B, e.toAddChar (z * t) = 1) ↔ z ∈ H := by
  let χ : AddChar (v.adicCompletion F) Circle :=
    { toFun := fun x => ⟨e.toAddChar x, mem_sphere_zero_iff_norm.mpr (e.unitary x)⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        exact e.toAddChar.map_zero_eq_one
      map_add_eq_mul' := by
        intro x y
        apply Subtype.ext
        exact e.toAddChar.map_add_eq_mul x y }
  have hχ : Continuous χ := e.continuous_toFun.subtype_mk _
  obtain ⟨a, ha⟩ :=
    KPExceptionalRaw.FiniteSource.TameWhittakerSteps.RawTransport.scalar_global F v χ hχ
  have heq (x : v.adicCompletion F) :
      e.toAddChar x = (localFiniteCharacter F v (x * a) : ℂ) :=
    congrArg (fun c : Circle => (c : ℂ)) (ha x)
  have hane : a ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := he
    apply hx
    rw [heq, hz, mul_zero]
    simp
  let A := localFiniteAnnihilator F v H
  let f : v.adicCompletion F →+ v.adicCompletion F :=
    { toFun := fun t => a * t
      map_zero' := mul_zero a
      map_add' := mul_add a }
  let B := A.comap f
  have hAc : IsCompact (A : Set (v.adicCompletion F)) :=
    isCompact_localFiniteAnnihilator F v H hHcompact hHopen
  have hAo : IsOpen (A : Set (v.adicCompletion F)) :=
    isOpen_localFiniteAnnihilator F v H hHcompact hHopen
  refine ⟨B, (Homeomorph.mulLeft₀ a hane).isCompact_preimage.mpr hAc,
    hAo.preimage (continuous_const.mul continuous_id), ?_⟩
  intro z
  have hd : (∀ u ∈ A, localFiniteCharacter F v (u * z) = 1) ↔ z ∈ H := by
    change z ∈ localFiniteAnnihilator F v (localFiniteAnnihilator F v H) ↔ z ∈ H
    rw [localFiniteAnnihilator_localFiniteAnnihilator F v H hHcompact hHopen]
  rw [← hd]
  constructor
  · intro hz u hu
    have ht : a⁻¹ * u ∈ B := by
      change a * (a⁻¹ * u) ∈ A
      simpa [← mul_assoc, hane] using hu
    have h := hz (a⁻¹ * u) ht
    rw [heq] at h
    have hm : z * (a⁻¹ * u) * a = u * z := by
      field_simp
    rw [hm] at h
    exact Subtype.ext (by simpa using h)
  · intro hz t ht
    change a * t ∈ A at ht
    rw [heq]
    have h := hz (a * t) ht
    have hm : z * t * a = a * t * z := by ring
    rw [hm, h]
    rfl

end DedekindZetaZeroFree.ThetaFiniteCutoff.PhaseSublevels

end

section

namespace DedekindZetaZeroFree.ThetaFiniteCutoff.PhaseSublevels

open NumberField IsDedekindDomain

theorem exists_uniform_phase_sublevel
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (e : ContinuousAddChar (v.adicCompletion F))
    (B : AddSubgroup (v.adicCompletion F))
    (hBopen : IsOpen (B : Set (v.adicCompletion F)))
    (M : ℝ) :
    ∃ J : AddSubgroup (v.adicCompletion F), J ≤ B ∧
      IsOpen (J : Set (v.adicCompletion F)) ∧
      ∀ z : v.adicCompletion F, ‖z‖ ≤ M →
        ∀ j ∈ J, e.toAddChar (z * j) = 1 := by
  let ψ : AddChar (v.adicCompletion F) Circle :=
    { toFun := fun x => ⟨e.toAddChar x, mem_sphere_zero_iff_norm.mpr (e.unitary x)⟩
      map_zero_eq_one' := by
        apply Circle.ext
        exact e.toAddChar.map_zero_eq_one
      map_add_eq_mul' := by
        intro x y
        apply Circle.ext
        exact e.toAddChar.map_add_eq_mul x y }
  have hψ : Continuous ψ := e.continuous_toFun.subtype_mk _
  obtain ⟨r, hr, hkill⟩ := KPFiniteLocal.character_trivial_near_zero ψ hψ
  let D : ℝ := max M 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let L : AddSubgroup (v.adicCompletion F) :=
    { carrier := {x | ‖x‖ < r / D}
      zero_mem' := by simpa using div_pos hr hD
      add_mem' := by
        intro x y hx hy
        exact (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
      neg_mem' := by intro x hx; simpa using hx }
  refine ⟨B ⊓ L, inf_le_left, ?_, ?_⟩
  · exact hBopen.inter (by
      change IsOpen {x : v.adicCompletion F | ‖x‖ < r / D}
      simpa only [Metric.ball, dist_zero_right] using
        (Metric.isOpen_ball : IsOpen (Metric.ball (0 : v.adicCompletion F) (r / D))))
  · intro z hz j hj
    have hj' : ‖j‖ < r / D := hj.2
    have hz' : ‖z‖ ≤ D := hz.trans (by dsimp [D]; linarith [le_max_left M 0])
    have hprod : ‖z * j‖ < r := by
      rw [norm_mul]
      calc
        ‖z‖ * ‖j‖ ≤ D * ‖j‖ := mul_le_mul_of_nonneg_right hz' (norm_nonneg j)
        _ < D * (r / D) := mul_lt_mul_of_pos_left hj' hD
        _ = r := mul_div_cancel₀ r (ne_of_gt hD)
    exact congrArg (fun c : Circle => (c : ℂ)) (hkill (z * j) hprod)

end DedekindZetaZeroFree.ThetaFiniteCutoff.PhaseSublevels

end

section

namespace DedekindZetaZeroFree
namespace ThetaFiniteCutoff

noncomputable section
open scoped Classical
open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

abbrev LocalUnits (A : SArithmeticData F) (v : A.Sf) :=
  (v.val.adicCompletion F)ˣ

theorem additive_quotient_character_sum
    {k : Type*} [CommRing k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    (e : AddChar k ℂ) (B J : AddSubgroup k) (hJB : J ≤ B)
    (hB : IsCompact (B : Set k)) (hJ : IsOpen (J : Set k))
    (z : k) (hzJ : ∀ j ∈ J, e (z * j) = 1) :
    letI := KPRootAverage.finite_levelQuotient B J hJB hB hJ
    letI := Fintype.ofFinite (KPRootAverage.LevelQuotient B J)
    (Fintype.card (KPRootAverage.LevelQuotient B J) : ℂ)⁻¹ *
      ∑ q : KPRootAverage.LevelQuotient B J,
        e (z * (KPRootAverage.representative B J q : k)) =
      if ∀ t ∈ B, e (z * t) = 1 then 1 else 0 := by
  letI := KPRootAverage.finite_levelQuotient B J hJB hB hJ
  letI := Fintype.ofFinite (KPRootAverage.LevelQuotient B J)
  let χ := (e.mulShift z).toMonoidHom.toHomUnits
  have hχJ : ∀ j ∈ J, χ (Multiplicative.ofAdd j) = 1 := by
    intro j hj
    apply Units.ext
    simpa [χ, AddChar.mulShift_apply, mul_comm] using hzJ j hj
  let χq := KPRootAverage.quotientCharacter χ B J hχJ
  let f : Multiplicative (KPRootAverage.LevelQuotient B J) →* ℂ :=
    (Units.coeHom ℂ).comp χq
  have hf (q : KPRootAverage.LevelQuotient B J) :
      f (Multiplicative.ofAdd q) =
        e (z * (KPRootAverage.representative B J q : k)) := by
    simp [f, χq, KPRootAverage.quotientCharacter, χ, mul_comm]
  have hiff : f = 1 ↔ ∀ t ∈ B, e (z * t) = 1 := by
    constructor
    · intro h t ht
      have hm := KPRootAverage.quotientCharacter_mk χ B J hχJ (⟨t, ht⟩ : B)
      have hu := congrArg (fun w : ℂˣ => (w : ℂ)) hm
      have hv : f (Multiplicative.ofAdd
          (QuotientAddGroup.mk' (J.addSubgroupOf B) (⟨t, ht⟩ : B))) = 1 := by
        rw [h]; rfl
      rw [show f (Multiplicative.ofAdd
          (QuotientAddGroup.mk' (J.addSubgroupOf B) (⟨t, ht⟩ : B))) =
          e (z * t) by
            change (χq _ : ℂ) = _
            rw [hu]
            simp [χ, mul_comm]] at hv
      exact hv
    · intro h
      apply MonoidHom.ext
      intro q
      exact (hf (Multiplicative.toAdd q)).trans
        (h _ (KPRootAverage.representative B J _).property)
  have hsum : (∑ q : KPRootAverage.LevelQuotient B J,
      e (z * (KPRootAverage.representative B J q : k))) =
      ∑ q : Multiplicative (KPRootAverage.LevelQuotient B J), f q := by
    change (∑ q : KPRootAverage.LevelQuotient B J, _) = _
    simp_rw [← hf]
    exact Fintype.sum_equiv (Multiplicative.ofAdd : _ ≃ _) _ _ (fun _ => rfl)
  rw [hsum]
  by_cases h : ∀ t ∈ B, e (z * t) = 1
  · rw [if_pos h, hiff.mpr h]
    simp only [MonoidHom.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    rw [Fintype.card_congr (Multiplicative.ofAdd :
      KPRootAverage.LevelQuotient B J ≃ Multiplicative (KPRootAverage.LevelQuotient B J)).symm]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr
      (Fintype.card_ne_zero : Fintype.card (KPRootAverage.LevelQuotient B J) ≠ 0))
  · rw [if_neg h, sum_hom_units_eq_zero f (fun he => h (hiff.mp he)), mul_zero]

end
end ThetaFiniteCutoff
end DedekindZetaZeroFree

end
