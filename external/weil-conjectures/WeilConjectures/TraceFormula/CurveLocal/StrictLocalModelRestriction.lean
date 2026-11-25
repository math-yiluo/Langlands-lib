/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelRestriction

/-!

# Restriction to the closed point of the intersection in the strictly local model

In the strictly local model `M` of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`), the
geometric point `t_Y : Spec k ⟶ Y` of the intersection `Y = G ×_T B` over the closed point is a
closed immersion, and the restriction map `RΓ(Y, K) ⟶ RΓ(Spec k, t_Y^* K)` is an isomorphism
(`AlgebraicGeometry.Etale.CurveLocalModel.isIso_globalSectionsRestriction_tY`), `Y` being
strictly local. A point `z` of the fixed scheme of a square `ι ≫ graph = d ≫ diagonal` over `y`
is `t_Y ≫ τ_Y` (`AlgebraicGeometry.Etale.CurveLocalModel.eq_tY_comp_τY`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

@[reassoc (attr := simp)]
lemma tB_comp_τB : M.tB ≫ M.τB = M.y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma tY_comp_yB : M.tY ≫ M.yB = M.tB :=
  pullback.lift_snd _ _ _

/-- The geometric point `t` of `T` is a section of the structure morphism `T ⟶ Spec k`. -/
@[reassoc]
lemma t_comp_structure : M.t ≫ M.τ ≫ pullback.fst M.f M.f ≫ M.f = 𝟙 _ := by
  rw [t_comp_τ_assoc, diagPoint, pullback.lift_fst_assoc, M.y_comp]

/-- The geometric point `t_Y : Spec k ⟶ Y` is a closed immersion: it is a section of the
structure morphism of `Y` over `Spec k`. -/
instance isClosedImmersion_tY : IsClosedImmersion M.tY :=
  isClosedImmersion_of_comp_eq_id (M.yB ≫ M.b ≫ M.τ ≫ pullback.fst M.f M.f ≫ M.f) M.tY (by
    rw [tY_comp_yB_assoc, tB_comp_b_assoc, t_comp_structure])

instance isAffine_Y : IsAffine M.Y :=
  isAffine_of_isAffineHom (M.yB ≫ M.b)

instance nonempty_Y : Nonempty M.Y :=
  ⟨M.tY (IsLocalRing.closedPoint k)⟩

instance isStrictlyHenselianLocalRing_Y : IsStrictlyHenselianLocalRing Γ(M.Y, ⊤) :=
  isStrictlyHenselianLocalRing_of_isClosedImmersion (M.yB ≫ M.b)

lemma isoSpec_hom_tY_apply_closedPoint :
    (M.tY ≫ M.Y.isoSpec.hom) (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint Γ(M.Y, ⊤) := by
  refine IsLocalRing.eq_closedPoint_of_isClosed ?_
  refine isClosed_singleton_of_isClosedImmersion M.Y.isoSpec.inv ?_
  rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine isClosed_singleton_of_isClosedImmersion (M.yB ≫ M.b) ?_
  rw [← Scheme.Hom.comp_apply, tY_comp_yB_assoc, tB_comp_b, t_apply_closedPoint]
  exact IsLocalRing.isClosed_singleton_closedPoint _

/-- The restriction map `RΓ(Y, K) ⟶ RΓ(Spec k, t_Y^* K)` to the closed point of the strictly
local scheme `Y` is an isomorphism. -/
instance isIso_globalSectionsRestriction_tY {Λ : Type (u + 1)} [CommRing Λ]
    (K : DerivedCategory (Sheaf M.Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (globalSectionsRestriction M.tY K) :=
  isIso_globalSectionsRestriction_of_isStrictlyHenselianLocalRing M.Y.isoSpec M.tY (𝟙 _) (by
    rw [Category.id_comp]
    exact M.isoSpec_hom_tY_apply_closedPoint) K

variable {F : Scheme.{u}} {ι d : F ⟶ M.X} [IsClosedImmersion d]
  (hsq : IsPullback ι d M.graph (pullback.diagonal M.f))

/-- A point `z` of the fixed scheme `F` over `y` is the image of the closed point of `Y` under
`τ_Y : Y ⟶ F`. -/
lemma eq_tY_comp_τY (z : Spec (.of k) ⟶ F) (hz : z ≫ d = M.y) : z = M.tY ≫ M.τY hsq := by
  rw [← cancel_mono d, hz, Category.assoc, τY_d, tY_comp_yB_assoc, tB_comp_τB]

end AlgebraicGeometry.Etale.CurveLocalModel
