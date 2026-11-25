/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteness

/-!
# The closed-support triangle on `Dᵇc(-, ℚ̄_ℓ)`

Let `k` be an algebraically closed field with `ringChar k ≠ ℓ`, `X` a quasi-compact scheme locally
of finite type over `k`, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` the complementary
quasi-compact open immersion. This file proves clauses (1)–(4) of blueprint
`lemma-local-cohomology-right-adjoint--2` at the coefficient stage `ℚ̄_ℓ`.

As in `WeilConjectures.SixFunctors.ClosedImmersionStages`, the stage `Dᵇc(-, ℚ̄_ℓ)` is realised in
the Bhatt–Scholze model, rather than as the `2`-colimit over finite extensions `E ⊆ ℚ̄_ℓ` used in
the blueprint: it is the full subcategory
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic ℓ X` of the derived category
of pro-étale sheaves of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`, of bounded complexes
with constructible cohomology sheaves. On it:

1. `Rj_*` carries `Dᵇc(U, ℚ̄_ℓ)` into `Dᵇc(X, ℚ̄_ℓ)`
   (`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj`,
   from the finiteness theorem `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`);
2. `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` has a right adjoint `Ri^!`
   (`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedUpperShriekAdjunction`);
3. for `K ∈ Dᵇc(X, ℚ̄_ℓ)` the counit `i_* Ri^! K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a
   distinguished triangle, with a unique third arrow
   (`ProEtale.existsUnique_distTriang_boundedConstructibleAdicClosedSupportTriangle`),
   functorial in `K`, because `Hom(i_* Q[m], Rj_* G) = 0`;
4. `Ri^! Rj_* = 0`, and the unit `Q ⟶ Ri^! i_* Q` is an isomorphism
   (`AlgebraicGeometry.ProEtale.isZero_boundedConstructibleAdicClosedUpperShriek_obj`,
   `AlgebraicGeometry.ProEtale.isIso_boundedConstructibleAdicClosedUpperShriekAdjunction_unit`).

The proof is the generic recollement argument `CategoryTheory.Pretriangulated.Recollement`
applied to the full subcategories `Dᵇc(-, ℚ̄_ℓ)`: the inputs are that `Ri_*` is fully faithful,
that `D(j^*) ⊣ Rj_*` has invertible counit, that `D(j^*) Ri_* = 0`, and that a complex killed by
`D(j^*)` is `Ri_*` of its pullback `D(i^*)`
(`WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport`),
together with the stability of `Dᵇc(-, ℚ̄_ℓ)` under `D(i^*)`, `D(j^*)`, `Ri_*` and `Rj_*`.

The categories `Dᵇc(-, ℚ̄_ℓ)` are triangulated over locally noetherian schemes, constructible
sheaves being closed under kernels, cokernels and extensions there; the statements that involve
the triangulated structure on `Dᵇc(Z, ℚ̄_ℓ)` or `Dᵇc(U, ℚ̄_ℓ)` assume `Z` and `U` locally
noetherian, which follows from `X` being locally of finite type over `k`
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-- Bounded complexes of `ℓ`-adic sheaves with constructible cohomology sheaves form a triangulated
subcategory over a locally noetherian scheme: constructible sheaves are closed under kernels,
cokernels and extensions there. -/
instance ProEtale.DerivedCategory.isTriangulated_boundedConstructibleAdic (X : Scheme.{u})
    [IsLocallyNoetherian X] :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l X).IsTriangulated :=
  inferInstance

/-- The pullback `D(g^*)` preserves `Dᵇc(-, ℚ̄_ℓ)`: it is exact, so
`𝓗ⁿ(D(g^*) K) ≅ g^* 𝓗ⁿ(K)`, and pullbacks of constructible sheaves are constructible. -/
lemma ProEtale.DerivedCategory.boundedConstructibleAdic.mapDerivedCategory_adicUpperStar
    {X Y : Scheme.{u}} (g : Y ⟶ X) {K : DerivedCategory (ProEtale.AdicSheaf l X)}
    (hK : ProEtale.DerivedCategory.boundedConstructibleAdic l X K) :
    ProEtale.DerivedCategory.boundedConstructibleAdic l Y
      ((ProEtale.adicUpperStar l g).mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
    (ProEtale.adicConstructibleSheaf l Y).prop_of_iso
      (((ProEtale.adicUpperStar l g).mapDerivedCategoryHomologyFunctorIso n).app K)
      ((hK.2 n).upperStar g)⟩

section Finiteness

variable {k : Type u} [Field k] [IsAlgClosed k] {Y X : Scheme.{u}} (s : X ⟶ Spec (.of k))
  [LocallyOfFiniteType s] [QuasiCompact s] (hk : ringChar k ≠ l)

include s hk in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (1) at the stage `ℚ̄_ℓ` (for any
quasi-compact quasi-separated `f` locally of finite type, e.g. an open immersion `j`): for `X`
quasi-compact and locally of finite type over an algebraically closed field `k` with
`ringChar k ≠ ℓ`, `Rf_*` carries `Dᵇc(Y, ℚ̄_ℓ)` into `Dᵇc(X, ℚ̄_ℓ)`. This is the finiteness theorem
for constructible sheaves (`AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor`) and
dévissage over the finitely many cohomology sheaves
(`AlgebraicGeometry.ProEtale.finiteLowerStar_of_bounded`). Here `Dᵇc(-, ℚ̄_ℓ)` is realised by
sheaves of modules over the constant `ℓ`-adic sheaf (Bhatt–Scholze) rather than as a
`2`-colimit. -/
theorem ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {K : DerivedCategory (ProEtale.AdicSheaf l Y)}
    (hK : ProEtale.DerivedCategory.boundedConstructibleAdic l Y K) :
    ProEtale.DerivedCategory.boundedConstructibleAdic l X
      ((ProEtale.adicLowerStar l f).rightDerivedFunctor.obj K) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  ProEtale.finiteLowerStar_of_bounded f
    (fun _ hF ↦ ProEtale.finiteLowerStar_singleFunctor s f hk hF) K hK.1 hK.2

variable (l) in
/-- The pullback `g^* : Dᵇc(X, ℚ̄_ℓ) ⥤ Dᵇc(Y, ℚ̄_ℓ)`, the restriction of `D(g^*)`. -/
noncomputable abbrev ProEtale.boundedConstructibleAdicUpperStar {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory :=
  (ProEtale.DerivedCategory.boundedConstructibleAdic l X).liftFullSubcategory _
    (ProEtale.adicUpperStar l g).mapDerivedCategory
    fun _ hK ↦ hK.mapDerivedCategory_adicUpperStar g

/-- The direct image `Rf_* : Dᵇc(Y, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)`, the restriction of `Rf_*`
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj`). -/
noncomputable abbrev ProEtale.boundedConstructibleAdicRightDerivedLowerStar (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).liftFullSubcategory _
    (ProEtale.adicLowerStar l f).rightDerivedFunctor
    fun _ hK ↦ ProEtale.boundedConstructibleAdic_rightDerivedFunctor_adicLowerStar_obj s hk f hK

/-- The adjunction `g^* ⊣ Rg_*` on `Dᵇc(-, ℚ̄_ℓ)`, the restriction of
`AlgebraicGeometry.ProEtale.adicDerivedUpperStarLowerStarAdjunction`. -/
noncomputable def ProEtale.boundedConstructibleAdicUpperStarLowerStarAdjunction (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f] :
    ProEtale.boundedConstructibleAdicUpperStar l f ⊣
      ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk f :=
  (ProEtale.adicDerivedUpperStarLowerStarAdjunction l f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

/-- For an open immersion `j`, the counit `j^* Rj_* ⟶ 𝟭` on `Dᵇc(-, ℚ̄_ℓ)` is an isomorphism:
`Rj_*` is fully faithful. -/
instance ProEtale.isIso_boundedConstructibleAdicUpperStarLowerStarAdjunction_counit (j : Y ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] :
    IsIso (ProEtale.boundedConstructibleAdicUpperStarLowerStarAdjunction s hk j).counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

end Finiteness

section Localization

variable {k : Type u} [Field k] [IsAlgClosed k] {Z U X : Scheme.{u}} (s : X ⟶ Spec (.of k))
  [LocallyOfFiniteType s] [QuasiCompact s] (hk : ringChar k ≠ l)
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

/-- The direct image `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion, built from the
finiteness theorem, is the functor
`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedLowerStar` built without it: both are
the restriction of `Ri_*`. -/
noncomputable def ProEtale.boundedConstructibleAdicRightDerivedLowerStarIsoClosedLowerStar :
    haveI := LocallyOfFiniteType.isLocallyNoetherian s
    ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) s hk i ≅
      ProEtale.boundedConstructibleAdicClosedLowerStar l i :=
  Iso.refl _

/-- The direct image `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion is fully
faithful, phrased with the direct image built from the finiteness theorem. The same statement
for `AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedLowerStar`, which does not use the
finiteness theorem, is
`AlgebraicGeometry.ProEtale.fullyFaithfulBoundedConstructibleAdicClosedLowerStar`. -/
noncomputable def ProEtale.fullyFaithfulBoundedConstructibleAdicRightDerivedLowerStar :
    (ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) s hk i).FullyFaithful :=
  have := LocallyOfFiniteType.isLocallyNoetherian s
  ProEtale.fullyFaithfulBoundedConstructibleAdicClosedLowerStar i

include hij in
/-- `j^* i_* = 0` on `Dᵇc(-, ℚ̄_ℓ)`
(`ProEtale.isZero_mapDerivedCategory_adicUpperStar_obj_rightDerivedFunctor_adicLowerStar_obj`). -/
lemma ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj
    (M : (ProEtale.DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory) :
    IsZero ((ProEtale.boundedConstructibleAdicUpperStar l j).obj
      ((ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i).obj M)) :=
  IsZero.of_full_of_faithful_of_isZero (ProEtale.DerivedCategory.boundedConstructibleAdic l U).ι _
    (ProEtale.isZero_mapDerivedCategory_adicUpperStar_obj_rightDerivedFunctor_adicLowerStar_obj
      i j hij M.obj)

include hij in
/-- An object `K` of `Dᵇc(X, ℚ̄_ℓ)` with `j^* K = 0` is `i_*` of the object `i^* K` of
`Dᵇc(Z, ℚ̄_ℓ)`: the unit `K ⟶ Ri_* D(i^*) K` is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero`).
-/
lemma ProEtale.boundedConstructibleAdicRightDerivedLowerStar_essImage_of_isZero
    (K : (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory)
    (hK : IsZero ((ProEtale.boundedConstructibleAdicUpperStar l j).obj K)) :
    (ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i).essImage K :=
  have := ProEtale.isIso_adicDerivedUpperStarLowerStarAdjunction_unit_app_of_isZero i j hij
    ((ProEtale.DerivedCategory.boundedConstructibleAdic l U).ι.map_isZero hK)
  ⟨(ProEtale.boundedConstructibleAdicUpperStar l i).obj K, ⟨ObjectProperty.isoMk _
    (asIso ((ProEtale.adicDerivedUpperStarLowerStarAdjunction l i).unit.app K.obj)).symm⟩⟩

include hij in
/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the stage `ℚ̄_ℓ`, the
vanishing: `Hom(i_* Q[m], Rj_* G) = 0` for `Q ∈ Dᵇc(Z, ℚ̄_ℓ)` and `G ∈ Dᵇc(U, ℚ̄_ℓ)`. -/
lemma ProEtale.subsingleton_hom_shift_boundedConstructibleAdic
    (Q : (ProEtale.DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory)
    (G : (ProEtale.DerivedCategory.boundedConstructibleAdic l U).FullSubcategory) (m : ℤ) :
    Subsingleton (((ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i).obj Q)⟦m⟧ ⟶
      (ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk j).obj G) :=
  Recollement.subsingleton_hom_shift _ _
    (ProEtale.boundedConstructibleAdicUpperStarLowerStarAdjunction s hk j)
    (ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj s hk i j hij)
    Q G m

variable [IsLocallyNoetherian X] [IsLocallyNoetherian U]

include j hij in
/-- The direct image `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion is a left
adjoint (`CategoryTheory.Pretriangulated.Recollement.isLeftAdjoint`). -/
lemma ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar :
    (ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) s hk i).IsLeftAdjoint :=
  Recollement.isLeftAdjoint (ProEtale.boundedConstructibleAdicUpperStarLowerStarAdjunction s hk j)
    (ProEtale.fullyFaithfulBoundedConstructibleAdicRightDerivedLowerStar s hk i)
    (ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj s hk i j hij)
    (ProEtale.boundedConstructibleAdicRightDerivedLowerStar_essImage_of_isZero s hk i j hij)

include s hk i j hij in
/-- The exceptional inverse image `Ri^! : Dᵇc(X, ℚ̄_ℓ) ⥤ Dᵇc(Z, ℚ̄_ℓ)` along a closed immersion:
the right adjoint of `i_*`
(`AlgebraicGeometry.ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar`). -/
noncomputable def ProEtale.boundedConstructibleAdicClosedUpperShriek :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l Z).FullSubcategory :=
  have := ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar s hk i j hij
  (ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i).rightAdjoint

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2) at the stage `ℚ̄_ℓ`: the direct
image `i_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a closed immersion has the right adjoint `Ri^!`. It
is constructed by the recollement argument
(`CategoryTheory.Pretriangulated.Recollement.isLeftAdjoint`): the fibre of the unit
`K ⟶ Rj_* j^* K` is killed by `j^*`, hence is `i_*` of an object of `Dᵇc(Z, ℚ̄_ℓ)`, and it
represents `Hom(i_* -, K)` since `Hom(i_* Q[m], Rj_* G) = 0`. -/
noncomputable def ProEtale.boundedConstructibleAdicClosedUpperShriekAdjunction :
    ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i ⊣
      ProEtale.boundedConstructibleAdicClosedUpperShriek (l := l) s hk i j hij :=
  have := ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar s hk i j hij
  Adjunction.ofIsLeftAdjoint _

/-- The closed-support triangle `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1]` on
`Dᵇc(X, ℚ̄_ℓ)`, with third arrow `w`. -/
noncomputable abbrev ProEtale.boundedConstructibleAdicClosedSupportTriangle
    (K : (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory)
    (w : (ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk j).obj
        ((ProEtale.boundedConstructibleAdicUpperStar l j).obj K) ⟶
      ((ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i).obj
        ((ProEtale.boundedConstructibleAdicClosedUpperShriek s hk i j hij).obj K))⟦(1 : ℤ)⟧) :
    Triangle (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  Recollement.triangle (ProEtale.boundedConstructibleAdicUpperStarLowerStarAdjunction s hk j)
    (ProEtale.boundedConstructibleAdicClosedUpperShriekAdjunction s hk i j hij) K w

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the stage `ℚ̄_ℓ`: for
`K ∈ Dᵇc(X, ℚ̄_ℓ)`, the counit `i_* Ri^! K ⟶ K` and the unit `K ⟶ Rj_* j^* K` extend to a
distinguished triangle `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1]` of `Dᵇc(X, ℚ̄_ℓ)`, and its
third arrow is unique, as `Hom(i_* Q[m], Rj_* G) = 0`
(`AlgebraicGeometry.ProEtale.subsingleton_hom_shift_boundedConstructibleAdic`). -/
theorem ProEtale.existsUnique_distTriang_boundedConstructibleAdicClosedSupportTriangle
    (K : (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory) :
    ∃! w, ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K w ∈ distTriang _ :=
  Recollement.existsUnique_distTriang_counit_unit _ _
    (ProEtale.fullyFaithfulBoundedConstructibleAdicRightDerivedLowerStar s hk i)
    (ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj s hk i j hij)
    (ProEtale.boundedConstructibleAdicRightDerivedLowerStar_essImage_of_isZero s hk i j hij) K

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the stage `ℚ̄_ℓ`,
functoriality: for `φ : K ⟶ K'` in `Dᵇc(X, ℚ̄_ℓ)` and distinguished closed-support triangles of `K`
and `K'`, the triple `(i_* Ri^! φ, φ, Rj_* j^* φ)` is a morphism of triangles. -/
theorem ProEtale.exists_triangleHom_boundedConstructibleAdicClosedSupportTriangle
    {K K' : (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory}
    (φ : K ⟶ K') {w w'}
    (hw : ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K w ∈ distTriang _)
    (hw' : ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K' w' ∈
      distTriang _) :
    ∃ τ : ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K w ⟶
        ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K' w',
      τ.hom₁ = (ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk i).map
          ((ProEtale.boundedConstructibleAdicClosedUpperShriek s hk i j hij).map φ) ∧
        τ.hom₂ = φ ∧
        τ.hom₃ = (ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk j).map
          ((ProEtale.boundedConstructibleAdicUpperStar l j).map φ) :=
  Recollement.exists_triangleHom _ _
    (ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj s hk i j hij)
    φ hw hw'

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the stage `ℚ̄_ℓ`,
functoriality: a morphism of distinguished closed-support triangles is determined by its middle
component. -/
theorem ProEtale.boundedConstructibleAdicClosedSupportTriangle_hom_ext
    {K K' : (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory} {w w'}
    (hw : ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K w ∈ distTriang _)
    (hw' : ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K' w' ∈
      distTriang _)
    {τ τ' : ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K w ⟶
      ProEtale.boundedConstructibleAdicClosedSupportTriangle s hk i j hij K' w'}
    (h : τ.hom₂ = τ'.hom₂) : τ = τ' :=
  Recollement.triangleHom_ext _ _
    (ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj s hk i j hij)
    hw hw' h

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4) at the stage `ℚ̄_ℓ`:
`Ri^! Rj_* G = 0` for `G ∈ Dᵇc(U, ℚ̄_ℓ)`, as `Hom(Q, Ri^! Rj_* G) = Hom(i_* Q, Rj_* G) = 0`. -/
theorem ProEtale.isZero_boundedConstructibleAdicClosedUpperShriek_obj
    (G : (ProEtale.DerivedCategory.boundedConstructibleAdic l U).FullSubcategory) :
    IsZero ((ProEtale.boundedConstructibleAdicClosedUpperShriek s hk i j hij).obj
      ((ProEtale.boundedConstructibleAdicRightDerivedLowerStar s hk j).obj G)) :=
  Recollement.isZero_obj_obj (ProEtale.boundedConstructibleAdicUpperStarLowerStarAdjunction s hk j)
    (ProEtale.boundedConstructibleAdicClosedUpperShriekAdjunction s hk i j hij)
    (ProEtale.isZero_boundedConstructibleAdicUpperStar_obj_rightDerivedLowerStar_obj s hk i j hij)
    G

/-- Clause (4) of the localization sequence at the stage `ℚ̄_ℓ`: the unit `Q ⟶ Ri^! i_* Q` is
an isomorphism, `i_*` being fully faithful on `Dᵇc(-, ℚ̄_ℓ)`. This is phrased with the direct
image built from the finiteness theorem; the same statement for any right adjoint of
`AlgebraicGeometry.ProEtale.boundedConstructibleAdicClosedLowerStar`, which does not use the
finiteness theorem, is
`AlgebraicGeometry.ProEtale.isIso_unit_boundedConstructibleAdicClosedLowerStar`. -/
instance ProEtale.isIso_boundedConstructibleAdicClosedUpperShriekAdjunction_unit :
    IsIso (ProEtale.boundedConstructibleAdicClosedUpperShriekAdjunction s hk i j hij).unit :=
  Adjunction.unit_isIso_of_L_fully_faithful _

end Localization

end AlgebraicGeometry
