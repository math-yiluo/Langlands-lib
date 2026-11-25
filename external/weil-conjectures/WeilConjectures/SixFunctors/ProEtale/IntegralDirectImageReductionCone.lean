/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.ProEtale.IntegralReductionPullbackNormalization
import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPresentation
import all WeilConjectures.AlgebraicGeometry.NormalizedScalarRestrictionPush
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact

/-! # The finite direct-image projection as a map of scalar cone triangles

Source: blueprint integral open direct image, Reduction paragraph; Stacks 014A, 06YY.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true
attribute [local reducible] AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.QuotientChange.D AlgebraicGeometry.ProEtale.QuotientChange.F
  AlgebraicGeometry.ProEtale.QuotientChange.adj
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
attribute [local instance high] GrothendieckTopology.W.monoidal
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- The geometric mate of the inverse scalar pullback comparison, at exponent n+1.
Source: blueprint integral open direct image, Reduction paragraph; Stacks 06YY
(auxiliary; not a blueprint node). -/
def integralFiniteProjection (n : ℕ) [IsIso (integralReductionPullbackMap l E j n)]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :=
  ((CondensedRing.derivedUpperStarLowerStarAdjunction
    (DerivedNakayama.quotientRing l E (n + 1)) j).ofNatIsoLeft
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (DerivedNakayama.quotientRing l E (n + 1)) j)).homEquiv _ _
    (inv ((integralReductionPullbackMap l E j n).app
      ((CondensedRing.moduleObjectDerivedPushforward
        (DerivedNakayama.integerRing l E) j).obj K)) ≫
      (AdicCompletion.derivedReduction l E U n).map
        (((CondensedRing.derivedUpperStarLowerStarAdjunction
          (DerivedNakayama.integerRing l E) j).ofNatIsoLeft
            (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
              (DerivedNakayama.integerRing l E) j)).counit.app K))

private theorem triangle_transport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C)
    {A B D : C} (a : T.obj₁ ≅ A) (b : T.obj₂ ≅ B) (d : T.obj₃ ≅ D) :
    Pretriangulated.Triangle.mk (a.inv ≫ T.mor₁ ≫ b.hom)
      (b.inv ≫ T.mor₂ ≫ d.hom)
      (d.inv ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map a.hom) ∈ distTriang C := by
  apply Pretriangulated.isomorphic_distinguished _ hT _
  refine Pretriangulated.Triangle.isoMk _ _ a.symm b.symm d.symm ?_ ?_ ?_
  · simp
  · simp
  · simp [← Functor.map_comp]

private theorem inverse_mate_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ D} {RX : D ⥤ C} {LU : C' ⥤ D'} {RU : D' ⥤ C'}
    (aX : LX ⊣ RX) (aU : LU ⊣ RU)
    {G G' : C ⥤ C'} {H H' : D ⥤ D'} (e : G ≅ G') (f : H ≅ H')
    (r : RX ⋙ G' ⟶ H' ⋙ RU) (M : C) :
    LU.map (e.inv.app M) ≫
      (((mateEquiv aX aU).symm (TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft RX e.hom ≫ r ≫ Functor.whiskerRight f.inv RU))).app M) ≫
      f.hom.app (LX.obj M) =
    (((mateEquiv aX aU).symm (TwoSquare.mk _ _ _ _ r)).app M) := by
  let t := Functor.whiskerLeft RX e.hom ≫ r ≫ Functor.whiskerRight f.inv RU
  apply (aU.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [aU.unit_naturality_assoc]
  rw [← reassoc_of% (unit_mateEquiv_symm aX aU (TwoSquare.mk _ _ _ _ t) M)]
  simp only [t, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [← e.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← RU.map_comp, Iso.inv_hom_id_app, RU.map_id]
  erw [Category.comp_id]
  exact unit_mateEquiv_symm aX aU (TwoSquare.mk _ _ _ _ r) M

private theorem geometric_mate_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
    {LM : C ⥤ D} {LM' : C' ⥤ D'} (e : L ≅ LM) (f : L' ≅ LM')
    (b : G ⋙ L' ≅ L ⋙ H) (c : LM ⋙ H ⟶ G ⋙ LM') [IsIso c]
    (hb : ∀ M, b.inv.app M = H.map (e.hom.app M) ≫ c.app M ≫ f.inv.app (G.obj M))
    (K : D) :
    ((a'.ofNatIsoLeft f).homEquiv _ _
      (inv (c.app (R.obj K)) ≫ H.map ((a.ofNatIsoLeft e).counit.app K))) =
    (mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).app K := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  have he : b.hom.app (R.obj K) =
      f.hom.app (G.obj (R.obj K)) ≫ inv (c.app (R.obj K)) ≫
        H.map (e.inv.app (R.obj K)) := by
    have hh : (b.app (R.obj K)).symm =
        H.mapIso (e.app (R.obj K)) ≪≫ asIso (c.app (R.obj K)) ≪≫
          (f.app (G.obj (R.obj K))).symm := Iso.ext (hb _)
    simpa only [Iso.symm_inv, Iso.app_hom, Iso.trans_inv, Functor.mapIso_inv,
      asIso_inv, Iso.app_inv, Category.assoc] using congrArg Iso.inv hh
  apply (a'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hm := mateEquiv_counit a a' (TwoSquare.mk _ _ _ _ b.hom) K
  change L'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).app K) ≫
    a'.counit.app (H.obj K) = _ at hm
  change _ = L'.map ((mateEquiv a a' (TwoSquare.mk _ _ _ _ b.hom)).app K) ≫
    a'.counit.app (H.obj K)
  rw [hm, he]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]

private theorem finiteCoefficient_dualizable (Y : Scheme.{u}) (n : ℕ) :
    IsDualizable (QuotientChange.B
      (DerivedNakayama.reductionRing l E (n + 1)) Y) := by
  obtain ⟨d, _, r, _, _, _, _, _, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  obtain ⟨⟨hz, hs⟩, _⟩ := hres Y (n + 1) (by omega)
  have h := DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact hs
    (show IsDualizable (𝟙_ (AdicCompletion.Modules l E Y)) from ⟨inferInstance⟩)
    (show IsDualizable (𝟙_ (AdicCompletion.Modules l E Y)) from ⟨inferInstance⟩)
  let e := ((upperStarFromPoint Y).mapModComapIso
    (DerivedNakayama.reductionRing l E (n + 1))).app
      (Mod.regular (DerivedNakayama.quotientRing l E (n + 1)))
  exact h.of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e)

@[instance_reducible] private def proofSectionDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ Y) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology Y) _)

attribute [local instance] proofSectionDerived

section CachedInstances
variable (Y : Scheme.{u})
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
local notation "M" => Mod (Sheaf (Scheme.ProEt.topology Y) Ab) (condensedRingObj Λ Y)
@[instance_reducible]
private noncomputable def cachedMonoidal : MonoidalCategory M := inferInstance
private theorem cachedPreadditive : MonoidalPreadditive M := inferInstance
private theorem cachedFlat : Abelian.HasFunctorialFlatResolution M := inferInstance
private theorem cachedTensorFour : ∀ (A B C D : GradedObject ℤ M),
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance
private theorem cachedTensorLeft : ∀ (A B C : GradedObject ℤ M),
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance
private theorem cachedTensorRight : ∀ (A B C : GradedObject ℤ M),
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance
private theorem cachedColimitsLeft : ∀ (A : M),
    PreservesColimitsOfShape ℤ ((curriedTensor M).obj A) := inferInstance
private theorem cachedColimitsRight : ∀ (A : M),
    PreservesColimitsOfShape ℤ ((curriedTensor M).flip.obj A) := inferInstance
end CachedInstances
attribute [local instance] cachedMonoidal cachedPreadditive cachedFlat cachedTensorFour
  cachedTensorLeft cachedTensorRight cachedColimitsLeft cachedColimitsRight
attribute [local reducible] CochainComplex.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors

private theorem scalarProjection_dualizable
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedCategory (QuotientChange.Modules Λ U))
    (hB : IsDualizable (QuotientChange.B a X)) :
    IsIso (QuotientChange.scalarProjection a j K) := by
  obtain ⟨br⟩ := DerivedCategory.nonempty_braidedCategory (QuotientChange.Modules Λ X)
  let := br
  have hp := Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ j)
    (CondensedRing.leftDerivedUpperStarTensor Λ j) (fun _ _ ↦ rfl) K hB
  unfold QuotientChange.scalarProjection CondensedRing.moduleObjectProjectionMap
    CondensedRing.moduleObjectProjectionData
  dsimp only
  unfold QuotientChange.F CondensedRing.moduleObjectDerivedPushforward
  apply IsIso.comp_isIso'
  · exact hp
  · have : IsIso (((CondensedRing.derivedTensor Λ U).obj K).map
        (QuotientChange.scalarCoefficientPull a j).hom) := Functor.map_isIso _ _
    exact Functor.map_isIso _ _

private theorem normalized_inverse_exact
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {U X : Scheme.{u}} (j : U ⟶ X)
    (b : QuotientChange.D a X ⋙ QuotientChange.L Λ' j ≅
      QuotientChange.L Λ j ⋙ QuotientChange.D a U)
    (hb : QuotientChange.PullNormalized a j b)
    (M : DerivedCategory (QuotientChange.Modules Λ X)) :
    b.inv.app M =
      (QuotientChange.D a U).map
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app M) ≫
      (((mateEquiv (QuotientChange.scalarAdj a X)
        (QuotientChange.scalarAdj a U)).symm
        (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso a j).inv)).app M) ≫
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' j).inv.app
        ((QuotientChange.D a X).obj M) := by
  rw [QuotientChange.normalized_inverse a j b hb]
  have he := inverse_mate_transport (QuotientChange.scalarAdj a X)
    (QuotientChange.scalarAdj a U)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' j)
    (CondensedRing.derivedComapUpperStarIso a j).inv M
  apply (cancel_epi ((QuotientChange.D a U).map
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).inv.app M))).mp
  apply (cancel_mono ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' j).hom.app
    ((QuotientChange.D a X).obj M))).mp
  simp only [QuotientChange.scalarRestrictionPull, id_eq, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]
  exact he

private theorem finiteProjection_isIso (n : ℕ)
    [IsIso (integralReductionPullbackMap l E j n)]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :
    IsIso (integralFiniteProjection l E j n K) := by
  let a := DerivedNakayama.reductionRing l E (n + 1)
  obtain ⟨tU, tX, b, _, _, htU, htX, hb, _⟩ :=
    QuotientChange.internal_scalar_pullback_normalization a j
  have hb' (M : DerivedCategory (AdicCompletion.Modules l E X)) :
      b.inv.app M =
        (AdicCompletion.derivedReduction l E U n).map
            ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
              (DerivedNakayama.integerRing l E) j).hom.app M) ≫
          (integralReductionPullbackMap l E j n).app M ≫
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (DerivedNakayama.quotientRing l E (n + 1)) j).inv.app
              ((AdicCompletion.derivedReduction l E X n).obj M) := by
    exact normalized_inverse_exact a j b hb M
  have hproj : IsIso (QuotientChange.scalarProjection a j K) := by
    exact scalarProjection_dualizable a j K (finiteCoefficient_dualizable l E X n)
  have hi := ((QuotientChange.internal_scalar_mate_projection a j tU tX b
    htU htX hb).2.2.2.2.1 K).mpr hproj
  have he := geometric_mate_transport
    (CondensedRing.derivedUpperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) j)
    (CondensedRing.derivedUpperStarLowerStarAdjunction
      (DerivedNakayama.quotientRing l E (n + 1)) j)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (DerivedNakayama.integerRing l E) j)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (DerivedNakayama.quotientRing l E (n + 1)) j)
    b (integralReductionPullbackMap l E j n) hb' K
  change integralFiniteProjection l E j n K =
    (QuotientChange.rho a j b).app K at he
  rw [he]
  exact hi

private theorem integralLevel_triangle (Y : Scheme.{u}) (n : ℕ)
    (H : DerivedCategory (AdicCompletion.Modules l E Y)) :
    ∃ (s : H ⟶ H) (q : H ⟶ AdicCompletion.integralLevel l E Y H n)
      (δ : AdicCompletion.integralLevel l E Y H n ⟶ H⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk s q δ ∈ distTriang _ := by
  obtain ⟨d, _, r, _, _, _, _, _, hres⟩ :=
    DerivedNakayama.derived_nakayama_resolution l E
  obtain ⟨⟨hz, hs⟩, _⟩ := hres Y (n + 1) (by omega)
  let T := (MonoidalCategory.tensorLeft H).mapTriangle.obj
    (DerivedCategory.triangleOfSES (hs.map_of_exact
      (HomologicalComplex.single (AdicCompletion.Modules l E Y) (.up ℤ) 0)))
  have hT : T ∈ distTriang _ :=
    (MonoidalCategory.tensorLeft H).map_distinguished _
      (DerivedCategory.triangleOfSES_distinguished (hs.map_of_exact
        (HomologicalComplex.single (AdicCompletion.Modules l E Y) (.up ℤ) 0)))
  let a : T.obj₁ ≅ H :=
    (MonoidalCategory.tensorLeft H).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        (DerivedNakayama.regularPullbackIso l E Y)) ≪≫ MonoidalCategory.rightUnitor H
  let b : T.obj₂ ≅ H := a
  let e := ((upperStarFromPoint Y).mapModComapIso
    (DerivedNakayama.reductionRing l E (n + 1))).app
      (Mod.regular (DerivedNakayama.quotientRing l E (n + 1)))
  let c : T.obj₃ ≅ AdicCompletion.integralLevel l E Y H n :=
    (MonoidalCategory.tensorLeft H).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso e) ≪≫
        ((Mod.residueDerivedTensorIso (AdicCompletion.quotient l E Y n)).app H).symm
  exact ⟨_, _, _, triangle_transport T hT a b c⟩

/-- After scalar restriction, the specified projection completes the identity square
on uniformizer multiplication to a morphism of distinguished triangles.
Source: blueprint integral open direct image, Reduction paragraph; Stacks 014A, 06YY
(auxiliary; not a blueprint node).

Proof: the positive-power uniformizer short exact sequence supplied by
`derived_nakayama_resolution` presents the restricted finite coefficient as a cone
of a map between tensor units. It is therefore dualizable. The general adjunction
projection theorem and `internal_scalar_mate_projection` make the finite scalar
mate invertible. The normalized inverse comparison and two explicit mate-transport
calculations identify that mate with exactly `integralFiniteProjection`.
Tensor the same short exact sequence with H to construct its distinguished scalar
cone triangle. Transport this triangle along the identity on both copies of H and
along the restricted finite projection c on the third vertex. Set q' = q followed
by c and delta' = inverse c followed by delta. The triangle isomorphism retains the
connecting sign, and inverse cancellation gives both displayed squares. Positive
exponent one, zero complexes, empty schemes and unbounded complexes are covered. -/
theorem integral_direct_image_reduction_cone (n : ℕ)
    [IsIso (integralReductionPullbackMap l E j n)]
    (K : DerivedCategory (AdicCompletion.Modules l E U)) :
    let H := (CondensedRing.moduleObjectDerivedPushforward
      (DerivedNakayama.integerRing l E) j).obj K
    let c := (AdicCompletion.restrict l E X n).map (integralFiniteProjection l E j n K)
    ∃ (s : H ⟶ H)
      (q : H ⟶ (AdicCompletion.integralLevel l E X H n))
      (δ : (AdicCompletion.integralLevel l E X H n) ⟶ H⟦(1 : ℤ)⟧)
      (q' : H ⟶ (AdicCompletion.restrict l E X n).obj
        ((CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.quotientRing l E (n + 1)) j).obj
            ((AdicCompletion.derivedReduction l E U n).obj K)))
      (δ' : (AdicCompletion.restrict l E X n).obj
        ((CondensedRing.moduleObjectDerivedPushforward
          (DerivedNakayama.quotientRing l E (n + 1)) j).obj
            ((AdicCompletion.derivedReduction l E U n).obj K)) ⟶ H⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk s q δ ∈ distTriang _ ∧
      Pretriangulated.Triangle.mk s q' δ' ∈ distTriang _ ∧
      q ≫ c = q' ∧ c ≫ δ' = δ := by
  dsimp only
  let H := (CondensedRing.moduleObjectDerivedPushforward
    (DerivedNakayama.integerRing l E) j).obj K
  let c := (AdicCompletion.restrict l E X n).map (integralFiniteProjection l E j n K)
  have := finiteProjection_isIso l E j n K
  have : IsIso c := Functor.map_isIso _ _
  obtain ⟨s, q, δ, hT⟩ := integralLevel_triangle l E X n H
  refine ⟨s, q, δ, q ≫ c, inv c ≫ δ, hT, ?_, rfl, ?_⟩
  · apply Pretriangulated.isomorphic_distinguished _ hT _
    refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl H) (Iso.refl H)
      (asIso c).symm ?_ ?_ ?_
    · exact (Category.comp_id s).trans (Category.id_comp s).symm
    · change (q ≫ c) ≫ inv c = 𝟙 H ≫ q
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · change (inv c ≫ δ) ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 H) = inv c ≫ δ
      rw [CategoryTheory.Functor.map_id]
      exact Category.comp_id _
  · change c ≫ (inv c ≫ δ) = δ
    exact IsIso.hom_inv_id_assoc c δ

end AlgebraicGeometry.ProEtale
