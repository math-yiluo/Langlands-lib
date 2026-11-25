/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.CoverCurves
public import WeilConjectures.TraceFormula.CurveLocal.ExchangeRestriction
public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalRestriction

/-!

# Restriction maps of the strictly local model are isomorphisms

In the strictly local model `AlgebraicGeometry.Etale.CurveLocalModel`, the schemes `T`, `G`, `B`
and `Y = G ×_T B` are strictly local with the same closed geometric point
`t : Spec k ⟶ T`. Hence the restriction maps of derived global sections along the closed
immersions `b : B ⟶ T` and `ι' : Y ⟶ G` are isomorphisms
(`AlgebraicGeometry.Etale.CurveLocalModel.isIso_globalSectionsRestriction_b`,
`AlgebraicGeometry.Etale.CurveLocalModel.isIso_globalSectionsRestriction_ιY`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

attribute [reassoc (attr := simp)] y_comp_graph

/-- The geometric point of the graph `G` over the closed point. -/
noncomputable def tG : Spec (.of k) ⟶ M.G :=
  pullback.lift M.y M.t (by rw [y_comp_graph, t_comp_τ])

/-- The geometric point of `G` lies over the geometric point `t` of `T`. -/
@[reassoc (attr := simp)]
lemma tG_comp_a : M.tG ≫ M.a = M.t :=
  pullback.lift_snd _ _ _

/-- The graph `G` is affine, being a closed subscheme of the affine scheme `T`. -/
instance : IsAffine M.G :=
  isAffine_of_isAffineHom M.a

/-- The graph `G` is nonempty: it contains the closed point. -/
instance : Nonempty M.G :=
  ⟨M.tG (IsLocalRing.closedPoint k)⟩

/-- The graph `G` is strictly local, being a nonempty closed subscheme of `T`. -/
instance : IsStrictlyHenselianLocalRing Γ(M.G, ⊤) :=
  isStrictlyHenselianLocalRing_of_isClosedImmersion M.a

/-- The geometric point of `G` lies over the closed point of `Spec Γ(G, ⊤)`. -/
lemma isoSpec_hom_tG_apply_closedPoint :
    (M.tG ≫ M.G.isoSpec.hom) (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint Γ(M.G, ⊤) := by
  refine IsLocalRing.eq_closedPoint_of_isClosed ?_
  refine isClosed_singleton_of_isClosedImmersion M.G.isoSpec.inv ?_
  rw [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine isClosed_singleton_of_isClosedImmersion M.a ?_
  rw [← Scheme.Hom.comp_apply, tG_comp_a, t_apply_closedPoint]
  exact IsLocalRing.isClosed_singleton_closedPoint _

/-- The geometric point of the intersection `Y = G ×_T B` over the closed point. -/
noncomputable def tY : Spec (.of k) ⟶ M.Y :=
  pullback.lift M.tG M.tB (by rw [tG_comp_a, tB_comp_b])

/-- The geometric point of `Y` lies over the geometric point of `G`. -/
@[reassoc (attr := simp)]
lemma tY_comp_ιY : M.tY ≫ M.ιY = M.tG :=
  pullback.lift_fst _ _ _

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The restriction `RΓ(T, K) ⟶ RΓ(B, b^* K)` along the diagonal of the strictly local model is
an isomorphism: both are the stalk at the closed point. -/
lemma isIso_globalSectionsRestriction_b
    (K : DerivedCategory (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (globalSectionsRestriction M.b K) :=
  isIso_globalSectionsRestriction_of_isStrictlyHenselianLocalRing
    (R := strictHenselization M.diagPoint) (Iso.refl _) M.b M.tB
    (by
      rw [Iso.refl_hom, Category.comp_id, tB_comp_b]
      exact M.t_apply_closedPoint) K

/-- The restriction `RΓ(G, K) ⟶ RΓ(Y, ι'^* K)` from the graph to the intersection `Y = G ×_T B`
of the strictly local model is an isomorphism: both are the stalk at the closed point. -/
lemma isIso_globalSectionsRestriction_ιY
    (K : DerivedCategory (Sheaf M.G.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (globalSectionsRestriction M.ιY K) :=
  isIso_globalSectionsRestriction_of_isStrictlyHenselianLocalRing M.G.isoSpec M.ιY M.tY
    (by
      rw [tY_comp_ιY_assoc]
      exact M.isoSpec_hom_tG_apply_closedPoint) K

end AlgebraicGeometry.Etale.CurveLocalModel
