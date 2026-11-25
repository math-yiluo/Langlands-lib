/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.TraceFormula.CurveLocal.RestrictionZeroLocalization

/-!

# The strictly local model of the Frobenius graph and the diagonal

This file sets up the classical étale models of blueprint `lemma-vanishing-local-term-zero-stalk--1`
(in the situation of `lemma-local-term-restriction-map--1`). Let `k` be an algebraically closed
field, `f : X ⟶ Spec k` a separated quasi-compact smooth curve, `h : X ⟶ X` a `k`-endomorphism (in
the blueprint the `m`-th power `Φ_X^m` of the `k`-linear Frobenius) and `y` a `k`-point of `X` fixed
by `h` at which `h` contracts: `h^♯ 𝔪_y ⊆ 𝔪_y²` (for `Φ_X^m` this holds since
`Φ_X^m(t - a) = (t - a)^{q^m}` in a local coordinate `t` with `t(y) = a`, see
`AlgebraicGeometry.map_maximalIdeal_stalkMap_le_sq_of_isFrobenius`).

Let `T` be the strict localization of `X ×_k X` at `(y, y)`
(`AlgebraicGeometry.Etale.CurveLocalModel.T`) and, inside `T`, let
```
G = Γ_{(h, id)},   B = Δ,   V = {y} × X
```
be the pullbacks of the transposed graph, of the diagonal and of the vertical axis, with closed
immersions `a : G ⟶ T`, `b : B ⟶ T`, `v : V ⟶ T`, and let `Y = G ×_T B ⟶ B`, set-theoretically
the closed point `y` of `B` (`AlgebraicGeometry.Etale.CurveLocalModel.yB`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **The data of the strictly local model** (blueprint `lemma-local-term-restriction-map--1`,
`lemma-vanishing-local-term-zero-stalk--1`): a separated smooth curve `f : X ⟶ Spec k` over the
algebraically closed field `k`, a `k`-endomorphism `h` of `X` (the iterate `Φ_X^m` of the
Frobenius in the blueprint) and a `k`-point `y` fixed by `h` at which `h` contracts,
`h^♯ 𝔪_y ⊆ 𝔪_y²`. -/
structure CurveLocalModel where
  /-- The curve. -/
  X : Scheme.{u}
  /-- The structure morphism. -/
  f : X ⟶ Spec (.of k)
  [smoothOfRelativeDimension : SmoothOfRelativeDimension 1 f]
  [isSeparated : IsSeparated f]
  [quasiCompact : QuasiCompact f]
  /-- The endomorphism (the iterate of the Frobenius). -/
  h : X ⟶ X
  h_comp : h ≫ f = f
  /-- The fixed point. -/
  y : Spec (.of k) ⟶ X
  y_comp : y ≫ f = 𝟙 _
  y_comp_h : y ≫ h = y
  /-- `h` contracts at `y`: `h^♯ 𝔪_y ⊆ 𝔪_y²`. -/
  map_maximalIdeal_le : (IsLocalRing.maximalIdeal
      (X.presheaf.stalk (h.base (y.base (default : Spec (.of k)))))).map
        (h.stalkMap (y.base (default : Spec (.of k)))).hom ≤
    IsLocalRing.maximalIdeal (X.presheaf.stalk (y.base (default : Spec (.of k)))) ^ 2

namespace CurveLocalModel

attribute [instance] smoothOfRelativeDimension isSeparated quasiCompact

variable {k} (M : CurveLocalModel k)

/-- The `k`-point `(y, y)` of `X ×_k X`. -/
noncomputable def diagPoint : Spec (.of k) ⟶ pullback M.f M.f :=
  pullback.lift M.y M.y rfl

/-- The strict localization `T` of `X ×_k X` at `(y, y)`. -/
noncomputable abbrev T : Scheme.{u} :=
  strictLocalization M.diagPoint

/-- The canonical morphism `τ : T ⟶ X ×_k X`. -/
noncomputable abbrev τ : M.T ⟶ pullback M.f M.f :=
  strictLocalizationToBase M.diagPoint

/-- The transposed graph `(h, id) : X ⟶ X ×_k X` of `h`. -/
noncomputable def graph : M.X ⟶ pullback M.f M.f :=
  pullback.lift M.h (𝟙 M.X) (by rw [M.h_comp, Category.id_comp])

/-- The vertical axis `x ↦ (y, x)`, `X ⟶ X ×_k X`, with image `{y} × X`. -/
noncomputable def vertical : M.X ⟶ pullback M.f M.f :=
  pullback.lift (M.f ≫ M.y) (𝟙 M.X) (by rw [Category.assoc, M.y_comp, Category.comp_id,
    Category.id_comp])

instance isClosedImmersion_graph : IsClosedImmersion M.graph := by
  have : IsClosedImmersion (M.graph ≫ pullback.snd M.f M.f) := by
    rw [graph, pullback.lift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp M.graph (pullback.snd M.f M.f)

instance isClosedImmersion_vertical : IsClosedImmersion M.vertical := by
  have : IsClosedImmersion (M.vertical ≫ pullback.snd M.f M.f) := by
    rw [vertical, pullback.lift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp M.vertical (pullback.snd M.f M.f)


/-- The horizontal axis `x ↦ (x, y)`, `X ⟶ X ×_k X`, with image `X × {y}`. -/
noncomputable def horizontal : M.X ⟶ pullback M.f M.f :=
  pullback.lift (𝟙 M.X) (M.f ≫ M.y) (by rw [Category.assoc, M.y_comp, Category.comp_id,
    Category.id_comp])

instance isClosedImmersion_horizontal : IsClosedImmersion M.horizontal := by
  have : IsClosedImmersion (M.horizontal ≫ pullback.fst M.f M.f) := by
    rw [horizontal, pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp M.horizontal (pullback.fst M.f M.f)

omit [IsAlgClosed k] in
@[reassoc (attr := simp)]
lemma horizontal_snd : M.horizontal ≫ pullback.snd M.f M.f = M.f ≫ M.y :=
  pullback.lift_snd _ _ _

/-- The horizontal axis `H` inside `T`. -/
noncomputable abbrev H : Scheme.{u} := pullback M.horizontal M.τ

/-- The closed immersion `hH : H ⟶ T`. -/
noncomputable abbrev hH : M.H ⟶ M.T := pullback.snd M.horizontal M.τ
/-- The graph `G` of `h` inside `T`. -/
noncomputable abbrev G : Scheme.{u} := pullback M.graph M.τ

/-- The closed immersion `a : G ⟶ T`. -/
noncomputable abbrev a : M.G ⟶ M.T := pullback.snd M.graph M.τ

/-- The diagonal `B` inside `T`. -/
noncomputable abbrev B : Scheme.{u} := pullback (pullback.diagonal M.f) M.τ

/-- The closed immersion `b : B ⟶ T`. -/
noncomputable abbrev b : M.B ⟶ M.T := pullback.snd (pullback.diagonal M.f) M.τ

/-- The vertical axis `V` inside `T`. -/
noncomputable abbrev V : Scheme.{u} := pullback M.vertical M.τ

/-- The closed immersion `v : V ⟶ T`. -/
noncomputable abbrev v : M.V ⟶ M.T := pullback.snd M.vertical M.τ

/-- The intersection `Y = G ×_T B`, set-theoretically the closed point of `B`. -/
noncomputable abbrev Y : Scheme.{u} := pullback M.a M.b

/-- The closed immersion `Y ⟶ B`. -/
noncomputable abbrev yB : M.Y ⟶ M.B := pullback.snd M.a M.b

/-- The open complement `B ∖ Y` lies over the open complement `T ∖ G`. -/
lemma openComplement_yB_le : M.yB.openComplement ≤ M.b ⁻¹ᵁ M.a.openComplement := by
  intro z hz
  simp only [Scheme.Hom.openComplement, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff,
    Set.mem_range, not_exists, Scheme.Hom.mem_preimage] at hz ⊢
  intro g hg
  have : z ∈ Set.range (pullback.snd M.a M.b).base := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨g, hg⟩
  obtain ⟨w, rfl⟩ := this
  exact hz w rfl

/-- The open subscheme `O = T ∖ (G ∪ V)`. -/
noncomputable def O : M.T.Opens := M.a.openComplement ⊓ M.v.openComplement

end CurveLocalModel

end AlgebraicGeometry.Etale
