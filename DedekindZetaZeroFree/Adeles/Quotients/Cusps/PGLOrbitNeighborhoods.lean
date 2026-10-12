module

public import DedekindZetaZeroFree.Adeles.Quotients.FinitePGL2AndCubicCoverComponents
public import DedekindZetaZeroFree.Arithmetic.Units.LogarithmicCuspShapesAndTorusActions

@[expose] public section

noncomputable section

open scoped Classical Matrix

namespace DedekindZetaZeroFree

namespace KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

def glAction (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPArch.Space (KPCuspLogShape.dimension F) :=
  KPArch.productAction (KPCuspLogShape.dimension F)
    (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A) z

theorem glAction_mul (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    glAction F (A * B) z = glAction F A (glAction F B z) := by
  funext i
  simp only [glAction, KPArch.productAction, map_mul]
  exact (KPArch.action_laws _ _ _).2

private theorem glAction_eq_of_mk_eq (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) : glAction F A z = glAction F B z := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  rw [glAction_mul]
  congr 1
  funext i
  simp only [glAction, KPArch.productAction]
  rw [Matrix.GeneralLinearGroup.map_scalar]
  exact (KPArch.scalar_action _ _).symm

def action (g : KPCuspArithmetic.PGL2 F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPArch.Space (KPCuspLogShape.dimension F) :=
  glAction F (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective g)) z

theorem action_mk (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    action F (Matrix.ProjGenLinGroup.mk A) z = glAction F A z := by
  exact glAction_eq_of_mk_eq F _ A
    (Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective _)) z

instance : MulAction (KPCuspArithmetic.PGL2 F)
    (KPArch.Space (KPCuspLogShape.dimension F)) where
  smul := action F
  one_smul z := by
    change action F 1 z = z
    rw [← map_one Matrix.ProjGenLinGroup.mk, action_mk]
    funext i
    simp only [glAction, KPArch.productAction, map_one]
    exact (KPArch.action_laws 1 1 (z i)).1
  mul_smul g h z := by
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
    change action F (Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk B) z =
      action F (Matrix.ProjGenLinGroup.mk A) (action F (Matrix.ProjGenLinGroup.mk B) z)
    rw [← map_mul, action_mk, action_mk, action_mk, glAction_mul]

end KPCuspSiegel

end DedekindZetaZeroFree

end

section

noncomputable section
open scoped Classical Matrix

namespace DedekindZetaZeroFree
namespace KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

abbrev OrbitQuotient (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) :=
  Quotient (MulAction.orbitRel Γ (KPArch.Space (KPCuspLogShape.dimension F)))

def projection (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) :
    KPArch.Space (KPCuspLogShape.dimension F) → OrbitQuotient F Γ :=
  Quotient.mk _

def box (P : Set (Fin (KPCuspLogShape.dimension F) → ℂ))
    (B : Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))) (I : Set ℝ) :
    Set (KPArch.Space (KPCuspLogShape.dimension F)) :=
  {z | ∃ x ∈ P, ∃ b ∈ B, ∃ t ∈ I,
    z = fun i => (x i, t + (b : Fin (KPCuspLogShape.dimension F) → ℝ) i)}

def highCusp (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    Set (KPArch.Space (KPCuspLogShape.dimension F)) :=
  (action F σ) '' {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z}

def parabolic (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F) :
    Subgroup (KPCuspArithmetic.PGL2 F) :=
  Γ ⊓ MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q

abbrev CuspQuotient (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (U : Set (KPArch.Space (KPCuspLogShape.dimension F))) :=
  Quotient (Setoid.comap (Subtype.val : U → KPArch.Space (KPCuspLogShape.dimension F))
    (MulAction.orbitRel (parabolic F Γ q) (KPArch.Space (KPCuspLogShape.dimension F))))

end KPCuspSiegel
end DedekindZetaZeroFree

end
end
