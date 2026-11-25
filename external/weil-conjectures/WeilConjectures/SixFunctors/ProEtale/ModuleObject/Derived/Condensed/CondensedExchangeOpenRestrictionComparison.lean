/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.Exact.ExactCondensedExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import Mathlib.CategoryTheory.Comma.Arrow

set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 4000]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.Mod.instAbelian
attribute [local instance 5000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ClosedTestDerivedExchangeModel.exchange
attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Mod.monoidalCategory Mod.monoidalClosed Mod.monoidalCategoryStruct
  Functor.mapDerivedCategoryNatIso
  moduleObjectDerivedExchange condensedAmbientExchange
  pullbackSquareComparison derivedUpperStarLowerStarAdjunction
-- Instance search must find the same sheafification and `EssentiallySmall` instances as the
-- imported derived pullbacks and their coherences; otherwise unification and the kernel check
-- of the instantiated cube time out.
attribute [-instance] SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules
  SheafOfModules.RingedCoefficientProjection.cachedWeakSheafifyModules
  InternalAbelianSheafModule.comparison_essentiallySmall

/-! Cached instances for module objects over `Λ_Z`, used by every `L((f)^*⟦Λ⟧)` below.
Searching them from the generic instances costs seconds per use. -/

section CachedInstances

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

private local instance (priority := 2000) hasTensorFour_modCondensed (Z : Scheme.{u})
    (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasTensor₄ObjExt A B C D :=
  inferInstance

private local instance (priority := 2000) hasGoodTensor₁₂Tensor_modCondensed (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensor₁₂Tensor A B C :=
  inferInstance

private local instance (priority := 2000) hasGoodTensorTensor₂₃_modCondensed (Z : Scheme.{u})
    (A B C : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) : GradedObject.HasGoodTensorTensor₂₃ A B C :=
  inferInstance

private local instance (priority := 2000) hasColimitsOfShapeInt_modCondensed (Z : Scheme.{u}) :
    HasColimitsOfShape ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

private local instance (priority := 2000) hasExactColimitsOfShapeInt_modCondensed
    (Z : Scheme.{u}) :
    HasExactColimitsOfShape ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

private local instance (priority := 2000) hasCountableCoproducts_modCondensed (Z : Scheme.{u}) :
    HasCountableCoproducts
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

private local instance (priority := 2000) preservesColimitsOfShapeInt_tensorLeft_modCondensed
    (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).obj M) :=
  inferInstance

private local instance (priority := 2000) preservesColimitsOfShapeInt_tensorRight_modCondensed
    (Z : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).flip.obj M) :=
  inferInstance

private local instance (priority := 2000) hasFunctorialFlatResolution_modCondensed
    (Z : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :=
  inferInstance

end CachedInstances

private theorem arrow_of_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {L : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {L' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : L ⊣ S) (adj' : F' ⊣ R') (adjK' : L' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : L ⋙ d ≅ c ⋙ L')
    (θ : G ⋙ L ⟶ F ⋙ H) (θ' : G' ⋙ L' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      L'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (hF : IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E))
    (hK : IsIso ((mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E))) :
    Nonempty (Arrow.mk (c.map
      ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E)) ≅
      Arrow.mk ((mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E))) := by
  have := hF
  have := hK
  have h := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E
  refine ⟨Arrow.isoMk
    (pG.app (R.obj E) ≪≫ G'.mapIso
      (asIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E)))
    (asIso ((mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E)) ≪≫
      S'.mapIso (pH.app E)) ?_⟩
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    asIso_hom, Arrow.mk_hom, Category.assoc] using h.symm

private theorem arrow_of_cube_named
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {L : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {L' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : L ⊣ S) (adj' : F' ⊣ R') (adjK' : L' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : L ⋙ d ≅ c ⋙ L')
    (θ : G ⋙ L ⟶ F ⋙ H) (θ' : G' ⋙ L' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      L'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (hF : IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E))
    (hK : IsIso ((mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app
      (H.obj E)))
    (τ : R ⋙ G ⟶ H ⋙ S) (τ' : R' ⋙ G' ⟶ H' ⋙ S')
    (hτ : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)) = τ)
    (hτ' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')) = τ') :
    Nonempty (Arrow.mk (c.map (τ.app E)) ≅ Arrow.mk (τ'.app (b.obj E))) := by
  obtain ⟨e⟩ := arrow_of_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E hF hK
  rw [hτ, hτ'] at e
  exact ⟨e⟩

private theorem arrow_of_cube_native_named
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {L : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {L' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : L ⊣ S) (adj' : F' ⊣ R') (adjK' : L' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (qF : a ⋙ F' ≅ F ⋙ b) (qG : a ⋙ G' ≅ G ⋙ c)
    (qH : b ⋙ H' ≅ H ⋙ d) (qK : c ⋙ L' ≅ L ⋙ d)
    (θ : G ⋙ L ⟶ F ⋙ H) (θ' : G' ⋙ L' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      θ'.app (a.obj X) ≫ H'.map (qF.hom.app X) ≫ qH.hom.app (F.obj X) =
        L'.map (qG.hom.app X) ≫ qK.hom.app (G.obj X) ≫ d.map (θ.app X))
    (E : B)
    (τF : R ⋙ a ⟶ b ⋙ R') (τK : S ⋙ c ⟶ d ⋙ S')
    (hτF : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ qF.hom)) = τF)
    (hτK : (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ qK.hom)) = τK)
    (hF : IsIso (τF.app E)) (hK : IsIso (τK.app (H.obj E)))
    (τ : R ⋙ G ⟶ H ⋙ S) (τ' : R' ⋙ G' ⟶ H' ⋙ S')
    (hτ : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)) = τ)
    (hτ' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')) = τ') :
    Nonempty (Arrow.mk (c.map (τ.app E)) ≅ Arrow.mk (τ'.app (b.obj E))) := by
  have hmF : IsIso
      ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ qF.hom)).app E) := by
    rw [hτF]
    exact hF
  have hmK : IsIso
      ((mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ qK.hom)).app (H.obj E)) := by
    rw [hτK]
    exact hK
  exact arrow_of_cube_named adj adjK adj' adjK' a b c d
    qF.symm qG.symm qH.symm qK.symm θ θ' (fun X ↦ (hc X).symm) E hmF hmK
    τ τ' hτ hτ'

private noncomputable def arrow_of_eq
    {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y} (h : f = g) :
    Arrow.mk f ≅ Arrow.mk g := eqToIso (congrArg Arrow.mk h)

private noncomputable def map_arrow_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    Arrow.mk (F.map f) ≅ Arrow.mk (G.map f) :=
  Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm

private noncomputable def input_arrow_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (η : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    Arrow.mk (η.app X) ≅ Arrow.mk (η.app Y) :=
  Arrow.isoMk (F.mapIso e) (G.mapIso e) (η.naturality e.hom)

private theorem totalExchange_mate_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    moduleObjectDerivedExchange Λ sq =
      (mateEquiv (derivedUpperStarLowerStarAdjunction Λ f)
        (derivedUpperStarLowerStarAdjunction Λ f')
        (TwoSquare.mk (upperStar Λ j).leftDerivedFunctor _ _
          (upperStar Λ i).leftDerivedFunctor (pullbackSquareComparison Λ sq).hom)) := by
  unfold moduleObjectDerivedExchange moduleObjectDerivedPullbackSquareComparison
    moduleObjectDerivedPullback pullbackSquareComparison
  rfl

private theorem ambient_eq_total
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) :
    condensedAmbientExchange Λ sq = moduleObjectDerivedExchange Λ sq.toCommSq := by
  unfold condensedAmbientExchange condensedAmbientPullbackComparison
    moduleObjectDerivedExchange moduleObjectDerivedPullbackSquareComparison
    moduleObjectDerivedPullback
  rfl

private theorem squareExchange_eq_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {F' : C ⥤ D} {R' : D ⥤ C}
    (a : F ⊣ R) (a' : F' ⊣ R') (G : A ⥤ C) (H : B ⥤ D)
    (e : G ⋙ F' ≅ F ⋙ H) :
    Adjunction.squareExchange a a' G H e =
      (mateEquiv a a' (TwoSquare.mk G F F' H e.hom)) := by
  ext N
  apply (a'.homEquiv _ _).symm.injective
  rw [Adjunction.squareExchange_adjunct]
  exact (mateEquiv_counit a a' (TwoSquare.mk G F F' H e.hom) N).symm

private theorem exactExchange_eq_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    exactCondensedExchangeFor Λ sq = derivedDirectImageOpenRestriction Λ sq := by
  unfold exactCondensedExchangeFor derivedDirectImageOpenRestriction
    derivedOpenCoherencePullbackSquare condensedPullbackSquareFor
    openCoherencePullbackSquare
  rfl

private theorem derived_eqToIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    Functor.mapDerivedCategoryNatIso (eqToIso h) = eqToIso (by subst h; rfl) := by
  subst h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem exactExchange_eq_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    exactCondensedExchangeFor Λ sq = ClosedTestDerivedExchangeModel.exchange Λ sq := by
  have hsq : Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor Λ sq) =
      ClosedTestDerivedExchangeModel.square Λ sq := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, condensedPullbackSquareFor,
      ClosedTestDerivedExchangeModel.square, ClosedTestDerivedExchangeModel.pullComp,
      ClosedTestDerivedExchangeModel.pull, Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc, derived_eqToIso]
  rw [ClosedTestDerivedExchangeModel.exchange, squareExchange_eq_mate]
  unfold exactCondensedExchangeFor
  rw [hsq]
  rfl

private theorem total_restriction_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((moduleObjectDerivedExchange Λ sq.toCommSq).app K) := by
  obtain ⟨e⟩ := totalDerivedExchange_exact_comparisonFor Λ sq.toCommSq K
  have hi := (derivedOpenRestrictionNormalization Λ sq).derived_isIso
  have : IsIso ((exactCondensedExchangeFor Λ sq.toCommSq).app K) := by
    rw [exactExchange_eq_restriction]
    infer_instance
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr this

private theorem restricted_ambient_total_arrow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (b : Z ⟶ Y')
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    Nonempty (Arrow.mk ((upperStar Λ b).mapDerivedCategory.map
      ((condensedAmbientExchange Λ sq).app K)) ≅
      Arrow.mk ((upperStar Λ b).leftDerivedFunctor.map
        ((moduleObjectDerivedExchange Λ sq.toCommSq).app K))) := by
  exact ⟨arrow_of_eq (congrArg (upperStar Λ b).mapDerivedCategory.map
      (congr_app (ambient_eq_total Λ sq) K)) ≪≫
    map_arrow_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ b).symm
      ((moduleObjectDerivedExchange Λ sq.toCommSq).app K)⟩

private theorem total_exchange_closed_arrow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    Nonempty (Arrow.mk ((moduleObjectDerivedExchange Λ sq).app K) ≅
      Arrow.mk ((ClosedTestDerivedExchangeModel.exchange Λ sq).app K)) := by
  exact Nonempty.map2 Iso.trans (totalDerivedExchange_exact_comparisonFor Λ sq K)
    ⟨arrow_of_eq (congr_app (exactExchange_eq_closed Λ sq) K)⟩

-- Elaborating the twelve derived functors and four derived adjunctions is slow.
-- Cache successive specializations to keep kernel conversions between the abstract
-- cube and the concrete derived functors small.
private theorem derived_cube_arrow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (v : U ⟶ Y) (a : XU ⟶ X) (fU : XU ⟶ U)
    (b : YU' ⟶ Y') (gU : YU' ⟶ U) (hU : XU' ⟶ XU) (fU' : XU' ⟶ YU')
    (t : XU' ⟶ X') : type_of% (
  arrow_of_cube_native_named
    (F := (upperStar Λ f).leftDerivedFunctor)
    (R := (lowerStar Λ f).rightDerivedFunctor)
    (L := (upperStar Λ f').leftDerivedFunctor)
    (S := (lowerStar Λ f').rightDerivedFunctor)
    (F' := (upperStar Λ fU).leftDerivedFunctor)
    (R' := (lowerStar Λ fU).rightDerivedFunctor)
    (L' := (upperStar Λ fU').leftDerivedFunctor)
    (S' := (lowerStar Λ fU').rightDerivedFunctor)
    (G := (upperStar Λ g).leftDerivedFunctor)
    (H := (upperStar Λ g').leftDerivedFunctor)
    (G' := (upperStar Λ gU).leftDerivedFunctor)
    (H' := (upperStar Λ hU).leftDerivedFunctor)
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ fU)
    (derivedUpperStarLowerStarAdjunction Λ fU')
    (upperStar Λ v).leftDerivedFunctor (upperStar Λ a).leftDerivedFunctor
    (upperStar Λ b).leftDerivedFunctor (upperStar Λ t).leftDerivedFunctor
) :=
  arrow_of_cube_native_named
    (F := (upperStar Λ f).leftDerivedFunctor)
    (R := (lowerStar Λ f).rightDerivedFunctor)
    (L := (upperStar Λ f').leftDerivedFunctor)
    (S := (lowerStar Λ f').rightDerivedFunctor)
    (F' := (upperStar Λ fU).leftDerivedFunctor)
    (R' := (lowerStar Λ fU).rightDerivedFunctor)
    (L' := (upperStar Λ fU').leftDerivedFunctor)
    (S' := (lowerStar Λ fU').rightDerivedFunctor)
    (G := (upperStar Λ g).leftDerivedFunctor)
    (H := (upperStar Λ g').leftDerivedFunctor)
    (G' := (upperStar Λ gU).leftDerivedFunctor)
    (H' := (upperStar Λ hU).leftDerivedFunctor)
    (derivedUpperStarLowerStarAdjunction Λ f)
    (derivedUpperStarLowerStarAdjunction Λ f')
    (derivedUpperStarLowerStarAdjunction Λ fU)
    (derivedUpperStarLowerStarAdjunction Λ fU')
    (upperStar Λ v).leftDerivedFunctor (upperStar Λ a).leftDerivedFunctor
    (upperStar Λ b).leftDerivedFunctor (upperStar Λ t).leftDerivedFunctor

private theorem derived_cube_arrow_faces
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    {v : U ⟶ Y} {a : XU ⟶ X} {fU : XU ⟶ U}
    {b : YU' ⟶ Y'} {gU : YU' ⟶ U} {hU : XU' ⟶ XU} {fU' : XU' ⟶ YU'}
    (wf : CommSq a fU f v) (wg : CommSq b gU g v) (w : CommSq hU fU' fU gU)
    (t : XU' ⟶ X') (sf : CommSq t hU g' a) (sk : CommSq t fU' f' b) : type_of% (
  derived_cube_arrow Λ g' f' f g v a fU b gU hU fU' t
    (pullbackSquareComparison Λ wf) (pullbackSquareComparison Λ wg)
    (pullbackSquareComparison Λ sf)
    (pullbackSquareComparison Λ sk)
    (pullbackSquareComparison Λ sq).hom (pullbackSquareComparison Λ w).hom
) :=
  derived_cube_arrow Λ g' f' f g v a fU b gU hU fU' t
    (pullbackSquareComparison Λ wf) (pullbackSquareComparison Λ wg)
    (pullbackSquareComparison Λ sf)
    (pullbackSquareComparison Λ sk)
    (pullbackSquareComparison Λ sq).hom (pullbackSquareComparison Λ w).hom

private theorem native_cube_equation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    {v : U ⟶ Y} {a : XU ⟶ X} {fU : XU ⟶ U}
    {b : YU' ⟶ Y'} {gU : YU' ⟶ U} {hU : XU' ⟶ XU} {fU' : XU' ⟶ YU'}
    (wf : CommSq a fU f v) (wg : CommSq b gU g v) (w : CommSq hU fU' fU gU)
    (t : XU' ⟶ X') (sf : CommSq t hU g' a) (sk : CommSq t fU' f' b)
    (Z : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (pullbackSquareComparison Λ w).hom.app ((upperStar Λ v).leftDerivedFunctor.obj Z) ≫
        (upperStar Λ hU).leftDerivedFunctor.map ((pullbackSquareComparison Λ wf).hom.app Z) ≫
        (pullbackSquareComparison Λ sf).hom.app ((upperStar Λ f).leftDerivedFunctor.obj Z) =
      (upperStar Λ fU').leftDerivedFunctor.map ((pullbackSquareComparison Λ wg).hom.app Z) ≫
        (pullbackSquareComparison Λ sk).hom.app ((upperStar Λ g).leftDerivedFunctor.obj Z) ≫
        (upperStar Λ t).leftDerivedFunctor.map ((pullbackSquareComparison Λ sq).hom.app Z) := by
  have h := pullbackSquareComparison_cube Λ w sq sf wf sk wg Z
  exact h

private theorem derived_cube_arrow_squares
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    {v : U ⟶ Y} {a : XU ⟶ X} {fU : XU ⟶ U}
    {b : YU' ⟶ Y'} {gU : YU' ⟶ U} {hU : XU' ⟶ XU} {fU' : XU' ⟶ YU'}
    (wf : CommSq a fU f v) (wg : CommSq b gU g v) (w : CommSq hU fU' fU gU)
    (t : XU' ⟶ X') (sf : CommSq t hU g' a) (sk : CommSq t fU' f' b) : type_of% (
  derived_cube_arrow_faces Λ sq wf wg w t sf sk
    (by
      intro Z
      have h := native_cube_equation Λ sq wf wg w t sf sk Z
      simpa only [Functor.comp_obj, Functor.comp_map] using h)
) :=
  derived_cube_arrow_faces Λ sq wf wg w t sf sk
    (by
      intro Z
      have h := native_cube_equation Λ sq wf wg w t sf sk Z
      simpa only [Functor.comp_obj, Functor.comp_map] using h)

private theorem total_cube_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    {v : U ⟶ Y} {a : XU ⟶ X} {fU : XU ⟶ U}
    {b : YU' ⟶ Y'} {gU : YU' ⟶ U} {hU : XU' ⟶ XU} {fU' : XU' ⟶ YU'}
    (wf : CommSq a fU f v) (wg : CommSq b gU g v) (w : CommSq hU fU' fU gU)
    (t : XU' ⟶ X') (sf : CommSq t hU g' a) (sk : CommSq t fU' f' b)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hmF : IsIso ((moduleObjectDerivedExchange Λ wf).app K))
    (hmK : IsIso ((moduleObjectDerivedExchange Λ sk).app
      ((upperStar Λ g').leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((upperStar Λ b).leftDerivedFunctor.map
      ((moduleObjectDerivedExchange Λ sq).app K)) ≅
      Arrow.mk ((moduleObjectDerivedExchange Λ w).app
        ((upperStar Λ a).leftDerivedFunctor.obj K))) := by
  exact derived_cube_arrow_squares Λ sq wf wg w t sf sk K
    (moduleObjectDerivedExchange Λ wf) (moduleObjectDerivedExchange Λ sk)
    (totalExchange_mate_eq Λ wf).symm
    (totalExchange_mate_eq Λ sk).symm hmF hmK
    (moduleObjectDerivedExchange Λ sq) (moduleObjectDerivedExchange Λ w)
    (totalExchange_mate_eq Λ sq).symm (totalExchange_mate_eq Λ w).symm

private theorem total_cube_open_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y U XU YU' XU' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    {v : U ⟶ Y} {a : XU ⟶ X} {fU : XU ⟶ U}
    {b : YU' ⟶ Y'} {gU : YU' ⟶ U} {hU : XU' ⟶ XU} {fU' : XU' ⟶ YU'}
    [IsOpenImmersion v] [IsOpenImmersion a] [IsOpenImmersion b]
    (wf : IsPullback a fU f v) (wg : IsPullback b gU g v)
    (w : IsPullback hU fU' fU gU)
    (t : XU' ⟶ X') [IsOpenImmersion t]
    (ht : IsPullback t fU' f' b)
    (htg : t ≫ g' = hU ≫ a)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    Nonempty (Arrow.mk ((upperStar Λ b).leftDerivedFunctor.map
      ((moduleObjectDerivedExchange Λ sq).app K)) ≅
      Arrow.mk ((moduleObjectDerivedExchange Λ w.toCommSq).app
        ((upperStar Λ a).leftDerivedFunctor.obj K))) := by
  exact total_cube_restriction Λ sq wf.toCommSq wg.toCommSq w.toCommSq t
    (CommSq.mk htg) ht.toCommSq K
    (total_restriction_isIso Λ wf K)
    (total_restriction_isIso Λ ht ((upperStar Λ g').leftDerivedFunctor.obj K))

private theorem exchange_input_total_exact_arrow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' V : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) (a : X ⟶ V)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :
    Nonempty (Arrow.mk ((moduleObjectDerivedExchange Λ sq).app
      ((upperStar Λ a).leftDerivedFunctor.obj K)) ≅
      Arrow.mk ((moduleObjectDerivedExchange Λ sq).app
        ((upperStar Λ a).mapDerivedCategory.obj K))) := by
  exact ⟨input_arrow_iso (moduleObjectDerivedExchange Λ sq)
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ a).app K)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
