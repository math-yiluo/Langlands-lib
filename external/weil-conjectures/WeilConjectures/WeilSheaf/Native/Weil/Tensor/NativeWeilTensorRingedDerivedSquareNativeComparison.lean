/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorForgetKFlat
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModelNaturality
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.CategoryTheory.Localization.Prod

/-! # Native comparison part of the native ringed derived square

Source: Stacks 06YU, 0FPT; blueprint steps 2--3 of
`lem-sf-native-weil-tensor-ringed-derived-square`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
attribute [local irreducible] Functor.mapDerivedCategory
section Helpers
attribute [local implicit_reducible] CategoryTheory.uniformProd CategoryTheory.prod'
private theorem descend_one_sided
    {C A D E : Type*} [Category C] [Category A] [Category D] [Category E]
    (q : C ⥤ D) (q' : A ⥤ E) (U : C ⥤ A) (F : D ⥤ E)
    (τ : q ⋙ F ≅ U ⋙ q') (P : ObjectProperty C)
    (ff : ((Functor.whiskeringLeft (C × P.FullSubcategory) (D × D) E).obj
      (q.prod (P.ι ⋙ q))).FullyFaithful)
    (t : C × C ⥤ C) (t' : A × A ⥤ A) (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (r : ∀ X Y : C, P X → (T.obj (q.obj Y, q.obj X) ≅ q.obj (t.obj (X, Y))))
    (hr : ∀ (X Y X' Y' : C) (hX : P X) (hX' : P X') (f : X ⟶ X') (g : Y ⟶ Y'),
      T.map (q.map g, q.map f) ≫ (r X' Y' hX').hom =
        (r X Y hX).hom ≫ q.map (t.map (f, g)))
    (s : ∀ X Y : C, P X →
      (T'.obj (q'.obj (U.obj Y), q'.obj (U.obj X)) ≅
        q'.obj (t'.obj (U.obj X, U.obj Y))))
    (hs : ∀ (X Y X' Y' : C) (hX : P X) (hX' : P X') (f : X ⟶ X') (g : Y ⟶ Y'),
      T'.map (q'.map (U.map g), q'.map (U.map f)) ≫ (s X' Y' hX').hom =
        (s X Y hX).hom ≫ q'.map (t'.map (U.map f, U.map g)))
    (c : ∀ X Y : C, U.obj (t.obj (X, Y)) ≅ t'.obj (U.obj X, U.obj Y))
    (hc : ∀ (X Y X' Y' : C) (f : X ⟶ X') (g : Y ⟶ Y'),
      U.map (t.map (f, g)) ≫ (c X' Y').hom =
        (c X Y).hom ≫ t'.map (U.map f, U.map g)) :
    ∃! a : T ⋙ F ≅ F.prod F ⋙ T', ∀ (X Y : C) (hX : P X),
      F.map (r X Y hX).hom ≫ τ.hom.app (t.obj (X, Y)) ≫ q'.map (c X Y).hom =
        a.hom.app (q.obj Y, q.obj X) ≫ T'.map (X := (F.obj (q.obj Y), F.obj (q.obj X)))
          (Y := (q'.obj (U.obj Y), q'.obj (U.obj X)))
          (Prod.mkHom (τ.hom.app Y) (τ.hom.app X)) ≫
          (s X Y hX).hom := by
  let L := q.prod (P.ι ⋙ q)
  let B := (𝟭 C).prod P.ι ⋙ CategoryTheory.Prod.swap C C ⋙ t
  let B' := (𝟭 C).prod P.ι ⋙ CategoryTheory.Prod.swap C C ⋙ U.prod U ⋙ t'
  let r' : L ⋙ T ≅ B ⋙ q :=
    NatIso.ofComponents (fun X ↦ r X.2.obj X.1 X.2.property) (fun f ↦
      hr _ _ _ _ _ _ f.2.hom f.1)
  let c' : B ⋙ U ≅ B' :=
    NatIso.ofComponents (fun X ↦ c X.2.obj X.1) (fun f ↦ hc _ _ _ _ f.2.hom f.1)
  let s' : ((U ⋙ q').prod (P.ι ⋙ U ⋙ q')) ⋙ T' ≅ B' ⋙ q' :=
    NatIso.ofComponents (fun X ↦ s X.2.obj X.1 X.2.property) (fun f ↦
      hs _ _ _ _ _ _ f.2.hom f.1)
  let ε : L ⋙ F.prod F ≅ (U ⋙ q').prod (P.ι ⋙ U ⋙ q') :=
    NatIso.prod τ (Functor.isoWhiskerLeft P.ι τ)
  let e : L ⋙ (T ⋙ F) ≅ L ⋙ (F.prod F ⋙ T') :=
    Functor.isoWhiskerRight r' F ≪≫ Functor.isoWhiskerLeft B τ ≪≫
      Functor.isoWhiskerRight c' q' ≪≫ s'.symm ≪≫ Functor.isoWhiskerRight ε.symm T'
  let a : T ⋙ F ≅ F.prod F ⋙ T' := ff.preimageIso e
  have hrep (X Y : C) (hX : P X) :
      F.map (r X Y hX).hom ≫ τ.hom.app (t.obj (X, Y)) ≫ q'.map (c X Y).hom =
        a.hom.app (q.obj Y, q.obj X) ≫ T'.map
          (X := (F.obj (q.obj Y), F.obj (q.obj X)))
          (Y := (q'.obj (U.obj Y), q'.obj (U.obj X)))
          (Prod.mkHom (τ.hom.app Y) (τ.hom.app X)) ≫ (s X Y hX).hom := by
    have ha : a.hom.app (q.obj Y, q.obj X) = e.hom.app (Y, ⟨X, hX⟩) :=
      congrArg (fun z ↦ z.app (Y, ⟨X, hX⟩)) (ff.map_preimage e.hom)
    rw [ha]
    change F.map (r X Y hX).hom ≫ τ.hom.app (t.obj (X, Y)) ≫ q'.map (c X Y).hom =
      (F.map (r X Y hX).hom ≫ τ.hom.app (t.obj (X, Y)) ≫ q'.map (c X Y).hom ≫
        (s X Y hX).inv ≫ T'.map (X := (q'.obj (U.obj Y), q'.obj (U.obj X)))
          (Y := (F.obj (q.obj Y), F.obj (q.obj X)))
          (Prod.mkHom (τ.inv.app Y) (τ.inv.app X))) ≫
          T'.map (X := (F.obj (q.obj Y), F.obj (q.obj X)))
            (Y := (q'.obj (U.obj Y), q'.obj (U.obj X)))
            (Prod.mkHom (τ.hom.app Y) (τ.hom.app X)) ≫ (s X Y hX).hom
    simp only [Category.assoc, ← T'.map_comp_assoc]
    simp
  refine ⟨a, hrep, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply ff.map_injective
  apply NatTrans.ext
  funext Z
  change a'.hom.app (q.obj Z.1, q.obj Z.2.obj) =
    a.hom.app (q.obj Z.1, q.obj Z.2.obj)
  let σ := T'.mapIso ((τ.app Z.1).prod (τ.app Z.2.obj))
  apply (cancel_mono σ.hom).mp
  apply (cancel_mono (s Z.2.obj Z.1 Z.2.property).hom).mp
  simpa only [Category.assoc, σ, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom] using
    (ha' Z.2.obj Z.1 Z.2.property).symm.trans (hrep _ _ Z.2.property)

private def curry_comparison {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (W : D ⥤ D ⥤ D) (U : C ⥤ D)
    (e : Functor.uncurry.obj T ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj W) :
    (Functor.postcompose₂.obj U).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj U).obj U).obj W :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ e.app (X, Y)) (by
    intro Y Y' g
    simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g))) (by
    intro X X' f
    apply NatTrans.ext
    funext Y
    simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y))

private theorem total_map_eq {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ C ⥤ C) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q T]
    {P Q P' Q' : CochainComplex C ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj T.map₂CochainComplex).map
        (X := (P, Q)) (Y := (P', Q')) (f, g) =
      HomologicalComplex.mapBifunctorMap f g T (.up ℤ) := by
  simp only [Functor.uncurry_obj_map, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex_obj_map, Functor.map₂HomologicalComplex_map_app,
    HomologicalComplex.mapBifunctorMap]
  rw [((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P').map_id,
    (T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).map_id]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id,
    HomologicalComplex₂.total.map_comp]

private noncomputable def total_bifunctor {C : Type*} [Category C] [Preadditive C]
    (T : C ⥤ C ⥤ C) [T.Additive] [∀ X, (T.obj X).Additive]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q T] :
    CochainComplex C ℤ × CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj X := CochainComplex.mapBifunctor X.1 X.2 T
  map f := HomologicalComplex.mapBifunctorMap f.1 f.2 T (.up ℤ)
  map_id X := by
    change HomologicalComplex.mapBifunctorMap (𝟙 X.1) (𝟙 X.2) T (.up ℤ) = _
    rw [← total_map_eq T (𝟙 X.1) (𝟙 X.2)]
    exact (Functor.uncurry.obj T.map₂CochainComplex).map_id X
  map_comp f g := by
    change HomologicalComplex.mapBifunctorMap (f.1 ≫ g.1) (f.2 ≫ g.2) T (.up ℤ) = _
    rw [← total_map_eq T (f.1 ≫ g.1) (f.2 ≫ g.2),
      ← total_map_eq T f.1 f.2, ← total_map_eq T g.1 g.2]
    exact (Functor.uncurry.obj T.map₂CochainComplex).map_comp f g

private theorem forget_preserves_coproducts
    {C : Type*} [Category C] (F : C ⥤ C) [F.IsEquivalence]
    (I : Type) [HasColimitsOfShape (Discrete I) C] :
    PreservesColimitsOfShape (Discrete I) (Endofunctor.IsoAlgebra.forget F) :=
  inferInstance

private theorem chain_naturality
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (T : C ⥤ C ⥤ C) [T.Additive] [∀ X, (T.obj X).Additive]
    (W : D ⥤ D ⥤ D) [W.Additive] [∀ X, (W.obj X).Additive]
    (U : C ⥤ D) [U.Additive]
    [∀ I : Type, PreservesColimitsOfShape (Discrete I) U]
    (e : Functor.uncurry.obj T ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj W)
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q T]
    [∀ P Q : CochainComplex D ℤ, P.HasMapBifunctor Q W]
    (c : ∀ P Q : CochainComplex C ℤ,
      (U.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mapBifunctor P Q T) ≅
        CochainComplex.mapBifunctor
          ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) W)
    (hc : ∀ (P Q : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
      U.map (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
        (c P Q).hom.f n = e.hom.app (P.X p, Q.X q) ≫
          HomologicalComplex.ιMapBifunctor
            ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) W (.up ℤ) p q n h)
    (P Q P' Q' : CochainComplex C ℤ) (f : P ⟶ P') (g : Q ⟶ Q') :
    (U.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (c P' Q').hom =
      (c P Q).hom ≫ HomologicalComplex.mapBifunctorMap
        ((U.mapHomologicalComplex (.up ℤ)).map f)
        ((U.mapHomologicalComplex (.up ℤ)).map g) W (.up ℤ) := by
  let χ := curry_comparison T W U e
  have hχ (P Q : CochainComplex C ℤ) :
      (c P Q).hom = HomologicalComplex.mapBifunctorComparison χ.hom (.up ℤ) P Q := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex.mapBifunctor.hom_ext_of_map U
    intro p q h
    rw [hc]
    exact (HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      χ.hom (.up ℤ) P Q p q n h).symm
  rw [hχ, hχ]
  exact HomologicalComplex.mapBifunctorComparison_naturality χ.hom (.up ℤ) f g

end Helpers
attribute [local irreducible] AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedMonoidal
  DerivedCategory DerivedCategory.Q instCategoryDerivedCategory
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilRingedTensorModel
  Functor.mapDerivedCategoryFactors HomologicalComplex.mapBifunctorMap
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeOrdinaryKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeTensorKFlat

namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Specializing product localization compares large dependent functor types.
-- Local irreducibility above avoids expanding the tensor-model implementations.
/-- The specified one-K-flat models determine a derived tensor-forgetting comparison
with the full representative square, including both exact-functor factorization maps.
The argument uses representative naturality and product localization.

Source: Stacks 06YU; the representative-square step of native tensor transport.
(blueprint: lem-sf-native-weil-tensor-ringed-derived-square-comparison).

Proof: identify the supplied chain comparison with the canonical bifunctor comparison
on each total summand; its naturality follows. Restrict the two derived bifunctors
to pairs (Q,P), with Q arbitrary and P native K-flat. Compose the native model,
exact-forgetting factorization, chain comparison, inverse ordinary model and inverse
factorizations on Q and P. The model naturality equations make this a natural
isomorphism on representatives. The product of derived localization in Q and the
supplied native K-flat localization in P is a localization. Its fully faithful
restriction of functor categories lifts this isomorphism. The preimage equation
and cancellation of the ordinary model and factor isomorphisms give the square.
Faithfulness of the same restriction and cancellation of the two isomorphisms
on the right of the square also give uniqueness. All comparisons are explicit;
no resolution or arbitrary existential witness is chosen.
The argument applies to unbounded and zero complexes and empty sites. -/
theorem native_weil_tensor_ringed_derived_square_comparison
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (hnaturality : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
          (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
          (hP' : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P')
          (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (ordinaryModel P' Q' hP').hom =
          (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ))) :
    ∃! t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom) := by
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let W := ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let hW : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ, P.HasMapBifunctor Q W :=
    fun P Q ↦ by infer_instance
  let P : ObjectProperty (CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :=
    NativeTensorKFlat k₀ l X T
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let Wq := HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)
  let : (P.ι ⋙ q).IsLocalization (Wq.inverseImage P.ι) := A.localization
  let L := q.prod (P.ι ⋙ q)
  let ff := Localization.fullyFaithfulWhiskeringLeft L
    (Wq.prod (Wq.inverseImage P.ι))
    (DerivedCategory (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
  let hsmall : HasColimitsOfSize.{0, 0} (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    hasColimitsOfSizeShrink.{0, 0} _
  let : (WeilSheaf.frobeniusPullback k₀ l X).IsEquivalence :=
    ProEtale.isEquivalence_adicLowerStar _ _
  let hcolim : ∀ I : Type, PreservesColimitsOfShape (Discrete I) U := fun I ↦ by
    let : HasColimitsOfShape (Discrete I) (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
      hsmall.has_colimits_of_shape (Discrete I)
    exact forget_preserves_coproducts (WeilSheaf.frobeniusPullback k₀ l X) I
  exact descend_one_sided q DerivedCategory.Q
    (U.mapHomologicalComplex (.up ℤ)) (nativeForget k₀ l X)
    U.mapDerivedCategoryFactors P ff (total_bifunctor T) (total_bifunctor W)
    (@MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB)) S.tensor
    (nativeWeilRingedTensorModel b T adj A SB TB βB cB)
    (nativeWeilRingedTensorModel_naturality b T adj A SB TB βB cB)
    (fun P Q hP ↦ ordinaryModel _ _ (native_weil_tensor_forget_kflat k₀ l X T chain P hP))
    (fun P Q P' Q' hP hP' f g ↦ hnaturality _ _ _ _ _ _
      ((U.mapHomologicalComplex (.up ℤ)).map f)
      ((U.mapHomologicalComplex (.up ℤ)).map g))
    chain (chain_naturality T W U e chain hchain)

end AlgebraicGeometry.ProEtaleWeilSheaf
