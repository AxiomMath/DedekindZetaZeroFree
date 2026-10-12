module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PGLHyperbolic.CompactStabilizer

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

theorem product_iwasawa_homeomorph (d : ℕ) :
    ∃ e : G d ≃ₜ (X d × K d),
      (∀ g, (e g).1 = g • o d) ∧
      ∀ x k, e.symm (x, k) = KPArithmeticAction.productProjectiveSection d x * (k : G d) := by
  let s : X d → G d := KPArithmeticAction.productProjectiveSection d
  have hs : Continuous s := KPArithmeticAction.productProjectiveSection_continuous d
  have hso (x : X d) : s x • o d = x :=
    KPArithmeticAction.productProjectiveSection_action d x
  let t : G d → K d := fun g => ⟨(s (g • o d))⁻¹ * g, by
    change ((s (g • o d))⁻¹ * g) • o d = o d
    rw [mul_smul]
    exact inv_smul_eq_iff.mpr (hso (g • o d)).symm⟩
  have ht : Continuous t := by
    apply Continuous.subtype_mk
    exact (hs.comp (continuous_id.smul continuous_const)).inv.mul continuous_id
  let e : G d ≃ₜ (X d × K d) :=
    { toFun := fun g => (g • o d, t g)
      invFun := fun p => s p.1 * (p.2 : G d)
      left_inv := by
        intro g
        change s (g • o d) * ((s (g • o d))⁻¹ * g) = g
        simp
      right_inv := by
        rintro ⟨x, k⟩
        have hk : (k : G d) • o d = o d := k.property
        have hx : (s x * (k : G d)) • o d = x := by
          rw [mul_smul, hk, hso]
        apply Prod.ext
        · exact hx
        · apply Subtype.ext
          change (s ((s x * (k : G d)) • o d))⁻¹ *
            (s x * (k : G d)) = (k : G d)
          rw [hx]
          simp
      continuous_toFun := (continuous_id.smul continuous_const).prodMk ht
      continuous_invFun := (hs.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd) }
  exact ⟨e, fun _ => rfl, fun _ _ => rfl⟩

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
