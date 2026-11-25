/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Projection.ProjectionInternalHom

/-! # Open and closed formulas for internal derived Hom

The evaluation-normalized comparison maps are imported from the common maps module.
The formal adjunction argument reduces the formulas to the natural tensor projections.
Source: Bhatt--Scholze Lemma 6.7.13; Stacks Tag 08JB.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem tensorComparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K K' M M' : DerivedCategory (supportModules Λ Y)) (a : K ⟶ K') (b : M ⟶ M') :
    (supportPullback Λ f).mapDerivedCategory.map
        (((derivedTensor Λ Y).map a).app M ≫ ((derivedTensor Λ Y).obj K').map b) ≫
        (supportDerivedTensorComparison Λ f K' M').hom =
      (supportDerivedTensorComparison Λ f K M).hom ≫
        ((derivedTensor Λ X).map ((supportPullback Λ f).mapDerivedCategory.map a)).app
          ((supportPullback Λ f).mapDerivedCategory.obj M) ≫
        ((derivedTensor Λ X).obj ((supportPullback Λ f).mapDerivedCategory.obj K')).map
          ((supportPullback Λ f).mapDerivedCategory.map b) := by
  exact (Classical.choose_spec
    (ExistsUnique.exists (existsUnique_supportDerivedTensorComparison Λ f))).1 K K' M M' a b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openProjection_naturality_right {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L : DerivedCategory (supportModules Λ U))
    {T T' : DerivedCategory (supportModules Λ X)} (f : T ⟶ T') :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.map
        (((derivedTensor Λ U).obj L).map ((supportPullback Λ j).mapDerivedCategory.map f)) ≫
      openSupportProjection Λ j L T' =
    openSupportProjection Λ j L T ≫
      ((derivedTensor Λ X).obj
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).map f := by
  let e := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let r := (supportPullback Λ j).mapDerivedCategory
  let tX := derivedTensor Λ X
  let tU := derivedTensor Λ U
  let η : L ⟶ r.obj (e.obj L) := (openSupportDerivedAdjunction Λ j).unit.app L
  let χ : ∀ M : DerivedCategory (supportModules Λ X),
      r.obj ((tX.obj (e.obj L)).obj M) ≅
        (tU.obj (r.obj (e.obj L))).obj (r.obj M) :=
    fun M ↦ supportDerivedTensorComparison Λ j (e.obj L) M
  apply ((openSupportDerivedAdjunction Λ j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [openSupportProjection, Equiv.apply_symm_apply]
  change (tU.obj L).map (r.map f) ≫ (tU.map η).app (r.obj T') ≫ (χ T').inv =
    ((tU.map η).app (r.obj T) ≫ (χ T).inv) ≫ r.map ((tX.obj (e.obj L)).map f)
  have h := tensorComparison_naturality Λ j (e.obj L) (e.obj L) T T' (𝟙 _) f
  change r.map ((tX.map (𝟙 (e.obj L))).app T ≫ (tX.obj (e.obj L)).map f) ≫
      (χ T').hom = (χ T).hom ≫ (tU.map (r.map (𝟙 (e.obj L)))).app (r.obj T) ≫
        (tU.obj (r.obj (e.obj L))).map (r.map f) at h
  rw [tX.map_id, NatTrans.id_app, Category.id_comp, r.map_id,
    tU.map_id, NatTrans.id_app, Category.id_comp] at h
  rw [← Category.assoc, (tU.map η).naturality]
  simp only [Category.assoc]
  apply (cancel_mono (χ T').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openProjection_naturality_left {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L L' : DerivedCategory (supportModules Λ U)} (a : L' ⟶ L)
    (T : DerivedCategory (supportModules Λ X)) :
    (openImmersionLowerShriek Λ j).mapDerivedCategory.map
        (((derivedTensor Λ U).map a).app ((supportPullback Λ j).mapDerivedCategory.obj T)) ≫
      openSupportProjection Λ j L T =
    openSupportProjection Λ j L' T ≫
      ((derivedTensor Λ X).map
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.map a)).app T := by
  let e := (openImmersionLowerShriek Λ j).mapDerivedCategory
  let r := (supportPullback Λ j).mapDerivedCategory
  let tX := derivedTensor Λ X
  let tU := derivedTensor Λ U
  let η (M) : M ⟶ r.obj (e.obj M) := (openSupportDerivedAdjunction Λ j).unit.app M
  let χ : ∀ M : DerivedCategory (supportModules Λ U),
      r.obj ((tX.obj (e.obj M)).obj T) ≅
        (tU.obj (r.obj (e.obj M))).obj (r.obj T) :=
    fun M ↦ supportDerivedTensorComparison Λ j (e.obj M) T
  apply ((openSupportDerivedAdjunction Λ j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [openSupportProjection, Equiv.apply_symm_apply]
  change (tU.map a).app (r.obj T) ≫ (tU.map (η L)).app (r.obj T) ≫ (χ L).inv =
    ((tU.map (η L')).app (r.obj T) ≫ (χ L').inv) ≫ r.map ((tX.map (e.map a)).app T)
  have h := tensorComparison_naturality Λ j (e.obj L') (e.obj L) T T (e.map a) (𝟙 T)
  change r.map ((tX.map (e.map a)).app T ≫ (tX.obj (e.obj L)).map (𝟙 T)) ≫
      (χ L).hom = (χ L').hom ≫ (tU.map (r.map (e.map a))).app (r.obj T) ≫
        (tU.obj (r.obj (e.obj L))).map (r.map (𝟙 T)) at h
  rw [(tX.obj (e.obj L)).map_id, Category.comp_id, r.map_id,
    (tU.obj (r.obj (e.obj L))).map_id, Category.comp_id] at h
  have hu : a ≫ η L = η L' ≫ r.map (e.map a) :=
    (openSupportDerivedAdjunction Λ j).unit.naturality a
  rw [← Category.assoc, ← NatTrans.comp_app, ← tU.map_comp, hu,
    tU.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  apply (cancel_mono (χ L).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedProjection_naturality_right {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [PreservesFiniteColimits (lowerStar Λ i)]
    (P : DerivedCategory (supportModules Λ Z))
    {T T' : DerivedCategory (supportModules Λ X)} (f : T ⟶ T') :
    ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).map f ≫
      closedSupportProjection Λ i P T' =
    closedSupportProjection Λ i P T ≫
      (lowerStar Λ i).mapDerivedCategory.map
        (((derivedTensor Λ Z).obj P).map ((supportPullback Λ i).mapDerivedCategory.map f)) := by
  let e := (lowerStar Λ i).mapDerivedCategory
  let r := (supportPullback Λ i).mapDerivedCategory
  let tX := derivedTensor Λ X
  let tZ := derivedTensor Λ Z
  let η (M) : M ⟶ e.obj (r.obj M) := (closedPullbackDerivedAdjunction Λ i).unit.app M
  let ε : r.obj (e.obj P) ⟶ P := (closedPullbackDerivedAdjunction Λ i).counit.app P
  let χ : ∀ M : DerivedCategory (supportModules Λ X),
      r.obj ((tX.obj (e.obj P)).obj M) ≅
        (tZ.obj (r.obj (e.obj P))).obj (r.obj M) :=
    fun M ↦ supportDerivedTensorComparison Λ i (e.obj P) M
  change (tX.obj (e.obj P)).map f ≫
      (η ((tX.obj (e.obj P)).obj T') ≫
        e.map ((χ T').hom ≫ (tZ.map ε).app (r.obj T'))) =
    (η ((tX.obj (e.obj P)).obj T) ≫
        e.map ((χ T).hom ≫ (tZ.map ε).app (r.obj T))) ≫
      e.map ((tZ.obj P).map (r.map f))
  have hu : (tX.obj (e.obj P)).map f ≫ η ((tX.obj (e.obj P)).obj T') =
      η ((tX.obj (e.obj P)).obj T) ≫ e.map (r.map ((tX.obj (e.obj P)).map f)) :=
    (closedPullbackDerivedAdjunction Λ i).unit.naturality _
  have h := tensorComparison_naturality Λ i (e.obj P) (e.obj P) T T' (𝟙 _) f
  change r.map ((tX.map (𝟙 (e.obj P))).app T ≫ (tX.obj (e.obj P)).map f) ≫
      (χ T').hom = (χ T).hom ≫ (tZ.map (r.map (𝟙 (e.obj P)))).app (r.obj T) ≫
        (tZ.obj (r.obj (e.obj P))).map (r.map f) at h
  rw [tX.map_id, NatTrans.id_app, Category.id_comp, r.map_id,
    tZ.map_id, NatTrans.id_app, Category.id_comp] at h
  rw [← Category.assoc, hu]
  simp only [Category.assoc, ← e.map_comp]
  congr 2
  rw [← Category.assoc, h, Category.assoc, (tZ.map ε).naturality]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedProjection_naturality_left {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [PreservesFiniteColimits (lowerStar Λ i)]
    {P P' : DerivedCategory (supportModules Λ Z)} (a : P' ⟶ P)
    (T : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).map ((lowerStar Λ i).mapDerivedCategory.map a)).app T ≫
      closedSupportProjection Λ i P T =
    closedSupportProjection Λ i P' T ≫
      (lowerStar Λ i).mapDerivedCategory.map
        (((derivedTensor Λ Z).map a).app ((supportPullback Λ i).mapDerivedCategory.obj T)) := by
  let e := (lowerStar Λ i).mapDerivedCategory
  let r := (supportPullback Λ i).mapDerivedCategory
  let tX := derivedTensor Λ X
  let tZ := derivedTensor Λ Z
  let η (M) : M ⟶ e.obj (r.obj M) := (closedPullbackDerivedAdjunction Λ i).unit.app M
  let ε (M) : r.obj (e.obj M) ⟶ M := (closedPullbackDerivedAdjunction Λ i).counit.app M
  let χ : ∀ M : DerivedCategory (supportModules Λ Z),
      r.obj ((tX.obj (e.obj M)).obj T) ≅
        (tZ.obj (r.obj (e.obj M))).obj (r.obj T) :=
    fun M ↦ supportDerivedTensorComparison Λ i (e.obj M) T
  change (tX.map (e.map a)).app T ≫
      (η ((tX.obj (e.obj P)).obj T) ≫
        e.map ((χ P).hom ≫ (tZ.map (ε P)).app (r.obj T))) =
    (η ((tX.obj (e.obj P')).obj T) ≫
        e.map ((χ P').hom ≫ (tZ.map (ε P')).app (r.obj T))) ≫
      e.map ((tZ.map a).app (r.obj T))
  have hu : (tX.map (e.map a)).app T ≫ η ((tX.obj (e.obj P)).obj T) =
      η ((tX.obj (e.obj P')).obj T) ≫ e.map (r.map ((tX.map (e.map a)).app T)) :=
    (closedPullbackDerivedAdjunction Λ i).unit.naturality _
  have h := tensorComparison_naturality Λ i (e.obj P') (e.obj P) T T (e.map a) (𝟙 T)
  change r.map ((tX.map (e.map a)).app T ≫ (tX.obj (e.obj P)).map (𝟙 T)) ≫
      (χ P).hom = (χ P').hom ≫ (tZ.map (r.map (e.map a))).app (r.obj T) ≫
        (tZ.obj (r.obj (e.obj P))).map (r.map (𝟙 T)) at h
  rw [(tX.obj (e.obj P)).map_id, Category.comp_id, r.map_id,
    (tZ.obj (r.obj (e.obj P))).map_id, Category.comp_id] at h
  have hc : r.map (e.map a) ≫ ε P = ε P' ≫ a :=
    (closedPullbackDerivedAdjunction Λ i).counit.naturality a
  rw [← Category.assoc, hu]
  simp only [Category.assoc, ← e.map_comp]
  congr 2
  rw [← Category.assoc, h, Category.assoc, ← NatTrans.comp_app,
    ← tZ.map_comp, hc, tZ.map_comp, NatTrans.comp_app]

/-- The two internal sheaf-valued derived-Hom formulas, normalized by evaluation and all
adjunction transposes, natural contravariantly in L,P and covariantly in N.
Source: Bhatt--Scholze Lemma 6.7.13, formal internal-adjunction calculation, and Stacks
Tag 08JB (blueprint: lem-sfb-open-closed-internal-hom-formulas).

Proof plan (the eleven steps of the node):
1. Identify module objects with sectionwise modules over B_T=p_T^*Lambda. The relative
   tensor coequalizer imposes bm tensor n = m tensor bn. Alpha is invertible, identifying
   supportPullback with the recorded upperStar, and the lower-star and lower-shriek
   actions with their ringed-site actions.
2. Pro-etale open/closed localization gives exact j!,i*,i^*,j^*, the two restriction
   identities, mixed vanishing, and the short exact localization sequence. Hence the
   two restrictions detect isomorphisms, without global qcqs assumptions.
3. The open unit gives openSupportProjection. The closed unit, pullback tensor map,
   and closed counit give closedSupportProjection. Restricting to U,Z proves both
   are isomorphisms; the inverse of the latter has the required projection direction.
4. Each of j!,j^*,i*,i^* preserves coproducts by its left adjunction; for i* use its
   support right adjoint. Ringed-site module categories have these small colimits.
5. Sum the projection comparisons over p+q=n. Naturality intertwines both differential
   terms with the same (-1)^p sign. Signed symmetry squares to the identity, since
   (-1)^((p+1)q)=(-1)^(pq+q) and (-1)^(p(q+1)+p)=(-1)^pq.
6. For e=j! or i* and r=j^* or i^*, test K-flatness against acyclic complexes using
   eC tensor Q = e(C tensor rQ), exactness, re=id, and signed symmetry. The same
   exact-functor composite shows preservation of flat terms in both directions.
7. Resolve both inputs by flat-term K-flat complexes. The total-complex comparisons
   descend separately along both resolving-class localization equivalences. Naturality
   respects chain homotopies and inverses of quasi-isomorphisms, so is unbounded.
8. Use actual units/counits of j! adjoint to j^*, j^* adjoint to Rj*, i^* adjoint
   to exact i*, and exact i* adjoint to RclosedSupport. Exact functors are termwise;
   homotopy adjunction and localization preserve the triangle identities.
9. For every derived test object T, tensor-Hom, open projection, open adjunction,
   tensor-Hom and j^* adjoint to Rj* identify Hom(T,H_X(j!L,N)) with
   Hom(T,Rj*H_U(L,j^*N)), naturally in T,L,N.
10. Similarly closed projection, i* adjoint to RclosedSupport, tensor-Hom and
    i^* adjoint to i* identify Hom(T,H_X(i*P,N)) with Hom(T,i*H_Z(P,Ri!N)).
11. Apply these bijections to identities to construct inverse object maps. Naturality
    in the test object proves their inverse identities; naturality in L,P,N proves
    the equations below. Transposing evaluation gives exactly openSupportHomMap and
    closedSupportHomMap with the inverse closed projection, fixing the normalization. -/
theorem openClosedInternalHomFormulas {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    ∃ (p : ∀ (P : DerivedCategory (supportModules Λ Z))
        (T : DerivedCategory (supportModules Λ X)),
        ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ≅
          (lowerStar Λ i).mapDerivedCategory.obj
            (((derivedTensor Λ Z).obj P).obj
              ((supportPullback Λ i).mapDerivedCategory.obj T)))
      (o : ∀ (L : DerivedCategory (supportModules Λ U))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj
          (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N) ≅
        (lowerStar Λ j).rightDerivedFunctor.obj
          (((derivedHom Λ U).obj (op L)).obj
            ((supportPullback Λ j).mapDerivedCategory.obj N)))
      (c : ∀ (P : DerivedCategory (supportModules Λ Z))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ≅
        (lowerStar Λ i).mapDerivedCategory.obj
          (((derivedHom Λ Z).obj (op P)).obj
            ((closedSupport Λ i j).rightDerivedFunctor.obj N))),
      (∀ P T, (p P T).hom = closedSupportProjection Λ i P T) ∧
      (∀ L N, (o L N).hom = openSupportHomMap Λ j L N) ∧
      (∀ P N, (c P N).hom = closedSupportHomMap Λ i j hij P N
        (p P (((derivedHom Λ X).obj
          (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)).inv) ∧
      (∀ (L L' : DerivedCategory (supportModules Λ U))
          (N N' : DerivedCategory (supportModules Λ X)) (a : L' ⟶ L) (b : N ⟶ N'),
        (((derivedHom Λ X).map
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj
            (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L'))).map b) ≫
          (o L' N').hom =
        (o L N).hom ≫ (lowerStar Λ j).rightDerivedFunctor.map
          (((derivedHom Λ U).map a.op).app
              ((supportPullback Λ j).mapDerivedCategory.obj N) ≫
            ((derivedHom Λ U).obj (op L')).map
              ((supportPullback Λ j).mapDerivedCategory.map b))) ∧
      (∀ (P P' : DerivedCategory (supportModules Λ Z))
          (N N' : DerivedCategory (supportModules Λ X)) (a : P' ⟶ P) (b : N ⟶ N'),
        (((derivedHom Λ X).map ((lowerStar Λ i).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P'))).map b) ≫
          (c P' N').hom =
        (c P N).hom ≫ (lowerStar Λ i).mapDerivedCategory.map
          (((derivedHom Λ Z).map a.op).app ((closedSupport Λ i j).rightDerivedFunctor.obj N) ≫
            ((derivedHom Λ Z).obj (op P')).map
              ((closedSupport Λ i j).rightDerivedFunctor.map b))) := by
  let := closedSupport_lowerStarExact Λ i j hij
  obtain ⟨hc, ho⟩ := openClosedSupportProjectionFormula Λ i j hij
  have hon := openProjection_naturality_right Λ j
  have hol := @openProjection_naturality_left.{u} Λ _ _ U X j _
  have hcn := closedProjection_naturality_right Λ i
  have hcl := @closedProjection_naturality_left.{u} Λ _ _ Z X i _ _
  let _ := hc
  let _ := ho
  let φc := fun P T ↦ inv (closedSupportProjection Λ i P T)
  have hciN : ∀ (P : DerivedCategory (supportModules Λ Z))
      {T T' : DerivedCategory (supportModules Λ X)} (f : T ⟶ T'),
      (lowerStar Λ i).mapDerivedCategory.map
          (((derivedTensor Λ Z).obj P).map ((supportPullback Λ i).mapDerivedCategory.map f)) ≫
        φc P T' =
      φc P T ≫ ((derivedTensor Λ X).obj
        ((lowerStar Λ i).mapDerivedCategory.obj P)).map f := by
    intro P T T' f
    apply (cancel_mono (closedSupportProjection Λ i P T')).1
    dsimp [φc]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hcn P f, IsIso.inv_hom_id_assoc]
  have hciL : ∀ {P P' : DerivedCategory (supportModules Λ Z)} (a : P' ⟶ P)
      (T : DerivedCategory (supportModules Λ X)),
      (lowerStar Λ i).mapDerivedCategory.map
          (((derivedTensor Λ Z).map a).app
            ((supportPullback Λ i).mapDerivedCategory.obj T)) ≫ φc P T =
      φc P' T ≫ ((derivedTensor Λ X).map
        ((lowerStar Λ i).mapDerivedCategory.map a)).app T := by
    intro P P' a T
    apply (cancel_mono (closedSupportProjection Λ i P T)).1
    dsimp [φc]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hcl a T, IsIso.inv_hom_id_assoc]
  have hoi : ∀ L N, IsIso (openSupportHomMap Λ j L N) := by
    intro L N
    exact projectionInternalHomMap_isIso
      (derivedTensor Λ X) (derivedHom Λ X) (derivedTensor Λ U) (derivedHom Λ U)
      (derivedTensorHomAdjunction₂ Λ X) (derivedTensorHomAdjunction₂ Λ U)
      (openImmersionLowerShriek Λ j).mapDerivedCategory
      (supportPullback Λ j).mapDerivedCategory (supportPullback Λ j).mapDerivedCategory
      (lowerStar Λ j).rightDerivedFunctor
      (openSupportDerivedAdjunction Λ j) (closedSupportOpenDerivedAdjunction Λ j)
      (openSupportProjection Λ j) ho hon L N
  have hci : ∀ P N, IsIso (closedSupportHomMap Λ i j hij P N
      (φc P (((derivedHom Λ X).obj
        (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N))) := by
    intro P N
    exact projectionInternalHomMap_isIso
      (derivedTensor Λ X) (derivedHom Λ X) (derivedTensor Λ Z) (derivedHom Λ Z)
      (derivedTensorHomAdjunction₂ Λ X) (derivedTensorHomAdjunction₂ Λ Z)
      (lowerStar Λ i).mapDerivedCategory (supportPullback Λ i).mapDerivedCategory
      (closedSupport Λ i j).rightDerivedFunctor (lowerStar Λ i).mapDerivedCategory
      (closedSupportDerivedAdjunction Λ i j hij) (closedPullbackDerivedAdjunction Λ i)
      φc (fun P T ↦ inferInstance) hciN P N
  let _ := hoi
  let _ := hci
  refine ⟨(fun P T ↦ asIso (closedSupportProjection Λ i P T)),
    (fun L N ↦ asIso (openSupportHomMap Λ j L N)),
    (fun P N ↦ asIso (closedSupportHomMap Λ i j hij P N
      (φc P (((derivedHom Λ X).obj
        (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)))),
    (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), ?_, ?_⟩
  · intro L L' N N' a b
    exact projectionInternalHomMap_naturality
      (derivedTensor Λ X) (derivedHom Λ X) (derivedTensor Λ U) (derivedHom Λ U)
      (derivedTensorHomAdjunction₂ Λ X) (derivedTensorHomAdjunction₂ Λ U)
      (openImmersionLowerShriek Λ j).mapDerivedCategory
      (supportPullback Λ j).mapDerivedCategory (supportPullback Λ j).mapDerivedCategory
      (lowerStar Λ j).rightDerivedFunctor
      (openSupportDerivedAdjunction Λ j) (closedSupportOpenDerivedAdjunction Λ j)
      (openSupportProjection Λ j) hon hol L L' N N' a b
  · intro P P' N N' a b
    exact projectionInternalHomMap_naturality
      (derivedTensor Λ X) (derivedHom Λ X) (derivedTensor Λ Z) (derivedHom Λ Z)
      (derivedTensorHomAdjunction₂ Λ X) (derivedTensorHomAdjunction₂ Λ Z)
      (lowerStar Λ i).mapDerivedCategory (supportPullback Λ i).mapDerivedCategory
      (closedSupport Λ i j).rightDerivedFunctor (lowerStar Λ i).mapDerivedCategory
      (closedSupportDerivedAdjunction Λ i j hij) (closedPullbackDerivedAdjunction Λ i)
      φc hciN hciL P P' N N' a b

end AlgebraicGeometry.ProEtale.CondensedRing
