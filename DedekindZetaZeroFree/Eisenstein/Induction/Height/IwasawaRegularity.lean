module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ComplexProjectiveLogNorm

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators Matrix.Norms.Elementwise NNReal
open NumberField
namespace DedekindZetaZeroFree.HeightGeometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
variable (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ)

def logModulus (g : G) : ℝ :=
  Real.log ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : NNReal) : ℝ)

def finiteFactor (g : G) : G :=
  (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g))⁻¹ * g

private theorem finiteFactor_mem (g : G) :
    finiteFactor F ζ hζ g ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
  apply RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ
  change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (finiteFactor F ζ hζ g) = 1
  unfold finiteFactor
  rw [map_mul, map_inv, PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
  simp

private theorem logModulus_borel_mul
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G) :
    logModulus F ζ hζ D ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      Real.log ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ) + logModulus F ζ hζ D g := by
  unfold logModulus
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul]
  simp only [Units.val_mul, NNReal.coe_mul]
  exact Real.log_mul (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
    (NNReal.coe_ne_zero.mpr (Units.ne_zero _))

theorem logModulus_continuous : Continuous (logModulus F ζ hζ D) := by
  have h := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous F ζ hζ D
  exact h.log (fun g => NNReal.coe_ne_zero.mpr (Units.ne_zero _))

variable (hSU : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2),
  KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈ D.K)

include hSU in
private theorem compact_insertion_mem (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
    PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w))) ∈ D.K := by
  rw [show PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ from rfl,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
  apply list_prod_mem
  intro k hk
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hk
  exact hSU w (u w)

include hSU in

theorem logModulus_eq_arch_sum_add_finite (g : G) :
    logModulus F ζ hζ D g =
      (∑ w : InfinitePlace F, complexProjectiveLogNorm
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w)) +
      logModulus F ζ hζ D (finiteFactor F ζ hζ g) := by
  let a := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g
  obtain ⟨y, x, u, hfac, hy⟩ := archimedean_factorization F ζ hζ a
  let k := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w)))
  have hk : k ∈ D.K := compact_insertion_mem F ζ hζ D hSU u
  have hc : Commute k (finiteFactor F ζ hζ g) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ _ ⟨_, finiteFactor_mem F ζ hζ g⟩
  have hg : g = ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
      (fun w => (y w : ℂ)) * KPGlobalTorusFunctionData.N F ζ hζ x) * finiteFactor F ζ hζ g) * k := by
    calc
      g = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * finiteFactor F ζ hζ g := by
        dsimp [a, finiteFactor]; group
      _ = _ := by rw [hfac]; dsimp [k] at hc ⊢; rw [mul_assoc, hc.eq, ← mul_assoc]
  have hinv : logModulus F ζ hζ D g = logModulus F ζ hζ D
      ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (y w : ℂ)) *
        KPGlobalTorusFunctionData.N F ζ hζ x) * finiteFactor F ζ hζ g) := by
    conv_lhs => rw [hg]
    unfold logModulus
    rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact F ζ hζ D _ ⟨k, hk⟩]
  rw [hinv]
  have hb := logModulus_borel_mul F ζ hζ D (KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (fun w => (y w : ℂ))) x (finiteFactor F ζ hζ g)
  change logModulus F ζ hζ D ((KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ
    (fun w => (y w : ℂ)) * KPGlobalTorusFunctionData.N F ζ hζ x) * finiteFactor F ζ hζ g) = _ at hb
  rw [hb]
  congr 1
  rw [KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ _
    (fun w => (y w).ne_zero)]
  rw [Real.log_prod (fun w _ => pow_ne_zero 2 (norm_ne_zero_iff.mpr (y w).ne_zero))]
  apply Finset.sum_congr rfl
  intro w _
  unfold complexProjectiveLogNorm complexMatrixLogNorm
  rw [hy w]

theorem finiteFactor_right_chart (g : G) (z : KPGlobalResidualConstruction.ArchCoordinates F) :
    finiteFactor F ζ hζ (g * KPGlobalResidualConstruction.archChart F ζ hζ z) = finiteFactor F ζ hζ g := by
  let p := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
  let i := PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
  let b := fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (z w))
  have hm : ∀ u v : PGLComplex.AdelicSlicesRaw.ArchGroup F, i (u*v) = i u * i v :=
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1
  have hc : Commute (i b) (finiteFactor F ζ hζ g) :=
    RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ b ⟨_, finiteFactor_mem F ζ hζ g⟩
  have hχ : KPGlobalResidualConstruction.archChart F ζ hζ z = i b := KPLiteralChamber.right_insertion F ζ hζ z
  have hp : p (i b) = b := PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ b
  change (i (p (g * KPGlobalResidualConstruction.archChart F ζ hζ z)))⁻¹ *
    (g * KPGlobalResidualConstruction.archChart F ζ hζ z) = _
  rw [hχ, map_mul, hp, hm]
  rw [mul_inv_rev, ← mul_assoc, mul_assoc (i b)⁻¹]
  change (i b)⁻¹ * finiteFactor F ζ hζ g * i b = finiteFactor F ζ hζ g
  rw [mul_assoc, ← hc.eq]
  group

include hSU in
set_option maxHeartbeats 800000 in

theorem logModulus_right_chart_smooth (g : G) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => logModulus F ζ hζ D
      (g * KPGlobalResidualConstruction.archChart F ζ hζ z)) (KPGlobalResidualConstruction.archDomain F) := by
  let M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun w => (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g w).out
  let A : InfinitePlace F → KPGlobalResidualConstruction.ArchCoordinates F →
      Matrix.GeneralLinearGroup (Fin 2) ℂ := fun w z => M w * KPLiteralChamber.rightMatrix (z w)
  let B : InfinitePlace F → KPGlobalResidualConstruction.ArchCoordinates F → Matrix (Fin 2) (Fin 2) ℂ :=
    fun w z => (M w : Matrix (Fin 2) (Fin 2) ℂ) * !![z w 1 + z w 0*z w 2, z w 0; z w 2, 1]
  have hBA : ∀ w z, z ∈ KPGlobalResidualConstruction.archDomain F → B w z = (A w z : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro w z hz
    dsimp [B, A]
    rw [KPLiteralChamber.rightMatrix_val _ (hz w)]
  have hA : ∀ z w, Matrix.ProjGenLinGroup.mk (A w z) =
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (g * KPGlobalResidualConstruction.archChart F ζ hζ z) w := by
    intro z w
    rw [KPLiteralChamber.right_insertion]
    change Matrix.ProjGenLinGroup.mk (A w z) = PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (z w)))) w
    rw [map_mul (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ),
      PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion]
    dsimp [A, M]
    rw [map_mul]
    congr 1
    exact Quotient.out_eq _
  have hB : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (B w) := by
    intro w
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have hl : ∀ w, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => complexMatrixLogNorm (B w z))
      (KPGlobalResidualConstruction.archDomain F) := by
    intro w
    apply (complexMatrixLogNorm_contDiffOn.of_le le_top).comp (hB w).contDiffOn
    intro z hz
    rw [Set.mem_setOf_eq, hBA w z hz]
    exact Matrix.GeneralLinearGroup.det_ne_zero (A w z)
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (∑ w : InfinitePlace F, complexMatrixLogNorm (B w z)) +
      logModulus F ζ hζ D (finiteFactor F ζ hζ g)) (KPGlobalResidualConstruction.archDomain F) :=
    (ContDiffOn.sum (fun w _ => hl w)).add contDiffOn_const
  apply hs.congr
  intro z hz
  rw [logModulus_eq_arch_sum_add_finite F ζ hζ D hSU, finiteFactor_right_chart]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [hBA w z hz, ← hA z w, complexProjectiveLogNorm_mk]
end DedekindZetaZeroFree.HeightGeometry

end
