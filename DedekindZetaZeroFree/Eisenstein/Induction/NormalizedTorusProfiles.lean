module

public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def normalizedTorusProfile (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K) : ℝ :=
  ‖f.val 0 (t.val * k.val)‖ /
    (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^ ((2 : ℝ) / 3)

private theorem torus_delta_pos (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    (0 : ℝ) < ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr
    (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)))

theorem normalizedTorusProfile_R_invariant (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (r : R F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K) :
    normalizedTorusProfile F ζ hζ K f (r.val * t) k =
      normalizedTorusProfile F ζ hζ K f t k := by
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have h := norm_val_covariance F ζ hζ K f 0 r 0 (t.val * k.val)
  simp only [hN, mul_one, Complex.zero_re, add_zero] at h
  unfold normalizedTorusProfile
  rw [Subgroup.coe_mul, mul_assoc, h, map_mul, Units.val_mul, NNReal.coe_mul,
    Real.mul_rpow (torus_delta_pos F ζ hζ r.val).le (torus_delta_pos F ζ hζ t).le]
  exact mul_div_mul_left _ _ (ne_of_gt (Real.rpow_pos_of_pos
    (torus_delta_pos F ζ hζ r.val) _))

theorem normalizedTorusProfile_continuous (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) :
    Continuous (fun p : KPGlobalTorusFunctionData.E F ζ hζ × K =>
      normalizedTorusProfile F ζ hζ K f p.1 p.2) := by
  have hn : Continuous (fun t : KPGlobalTorusFunctionData.E F ζ hζ =>
      ((KPGlobalCenterRationalCharacter.nu F ζ hζ t : NNReal) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp
      (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))
  have hd : Continuous (fun t : KPGlobalTorusFunctionData.E F ζ hζ =>
      ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) := by
    have he : (fun t : KPGlobalTorusFunctionData.E F ζ hζ =>
        ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) =
        (fun t => ((KPGlobalCenterRationalCharacter.nu F ζ hζ t : NNReal) : ℝ) ^
          (6 : ℝ)) := by
      funext t
      rw [KPGlobalCenterRationalCharacter.nu_formula]
      change _ = (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ) ^
        ((1 : ℝ) / 6)) ^ (6 : ℝ)
      rw [← Real.rpow_mul (torus_delta_pos F ζ hζ t).le]
      norm_num
    rw [he]
    exact hn.rpow_const (fun t => Or.inl (ne_of_gt
      (KPGlobalCenterRationalCharacter.nu_positive F ζ hζ t)))
  unfold normalizedTorusProfile
  apply Continuous.div
  · exact ((f.property.1 0).1.1.comp
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))).norm
  · exact (hd.comp continuous_fst).rpow_const (fun p => Or.inl
      (ne_of_gt (torus_delta_pos F ζ hζ p.1)))
  · intro p
    exact ne_of_gt (Real.rpow_pos_of_pos (torus_delta_pos F ζ hζ p.1) _)

theorem norm_val_torus_compact (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (s : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K) :
    ‖f.val s (t.val * k.val)‖ =
      (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) ^
        ((2 : ℝ) / 3 + s.re) * normalizedTorusProfile F ζ hζ K f t k := by
  rw [f.property.2.1 s t k, norm_mul, norm_realLogPower _
    (torus_delta_pos F ζ hζ t), normalizedTorusProfile,
    Real.rpow_add (torus_delta_pos F ζ hζ t)]
  field_simp

end DedekindZetaZeroFree.KPLiteralExceptionalResidue

end
